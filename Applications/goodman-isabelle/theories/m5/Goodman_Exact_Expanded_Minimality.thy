theory Goodman_Exact_Expanded_Minimality
  imports Goodman_Exact_Expanded_Stock
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Fresh_Constant
begin

section \<open>Exact evaluation of capture-avoiding constant abstraction\<close>

lemma gi_M5_pconst_subst_eval:
  "pp_e_eval C \<rho> (pterm_to_oterm (pconst_subst k \<sigma> N M)) =
    pp_e_eval (\<lambda>c \<tau>. if k = c \<and> \<sigma> = \<tau>
      then pp_e_eval C \<rho> (pterm_to_oterm N) else C c \<tau>) \<rho> (pterm_to_oterm M)"
proof -
  have update:
      "(\<lambda>c \<tau>. if k = c \<and> \<sigma> = \<tau>
        then pp_e_eval C (extend_env a \<eta>) (pterm_to_oterm (pshift P)) else C c \<tau>) =
       (\<lambda>c \<tau>. if k = c \<and> \<sigma> = \<tau>
        then pp_e_eval C \<eta> (pterm_to_oterm P) else C c \<tau>)" for a \<eta> P
  proof -
    have replacement: "pp_e_eval C (extend_env a \<eta>) (pterm_to_oterm (pshift P)) =
      pp_e_eval C \<eta> (pterm_to_oterm P)"
      by (simp only: pterm_to_pshift pp_e_eval_shift)
    show ?thesis
      by (rule arg_cong[OF replacement, where f="\<lambda>v. (\<lambda>c \<tau>. if k = c \<and> \<sigma> = \<tau> then v else C c \<tau>)"])
  qed
  show ?thesis
    by (induction M arbitrary: N \<rho>)
      (simp_all add: update pterm_to_pshift pp_e_eval_shift split: if_splits)
qed

lemma gi_M5_pconst_removes_only_signature:
  assumes source: "pterm_in_signature (gi_M5_expanded_signature k) M"
    and replacement: "pterm_in_signature (\<lambda>_. {}) N"
  shows "pterm_in_signature (\<lambda>_. {}) (pconst_subst k gb_unary N M)"
  using source replacement
  by (induction M arbitrary: N)
    (auto simp: gi_M5_expanded_signature_def pshift_def split: if_splits)

definition gi_M5_constant_abstractor :: "string \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gi_M5_constant_abstractor k M =
    Lam gb_unary (pterm_to_oterm (pabstract_const k gb_unary (pterm_of_oterm M)))"

lemma gi_M5_constant_abstractor_type:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "[] \<turnstile> gi_M5_constant_abstractor k M : Arr gb_unary \<sigma>"
  unfolding gi_M5_constant_abstractor_def
  by (rule has_type.Lam, rule pterm_to_preserves_typing,
    rule pabstract_const_type, rule pterm_of_preserves_typing[OF typed])

lemma gi_M5_constant_abstractor_logical:
  assumes signature: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "pp_logical_vocabulary (gi_M5_constant_abstractor k M)"
proof -
  have source: "pterm_in_signature (gi_M5_expanded_signature k) (pshift (pterm_of_oterm M))"
    using signature by (simp add: pshift_def pterm_of_signature_iff)
  have empty: "pterm_in_signature (\<lambda>_. {}) (pabstract_const k gb_unary (pterm_of_oterm M))"
    unfolding pabstract_const_def
    by (rule gi_M5_pconst_removes_only_signature[OF source]; simp)
  have no_constants: "consts_of (pterm_to_oterm (pabstract_const k gb_unary (pterm_of_oterm M))) = {}"
    by (rule gi_pterm_empty_signature_const_free[OF empty])
  show ?thesis by (simp only: gi_M5_constant_abstractor_def pp_logical_vocabulary_def consts_of.simps no_constants)
qed

lemma gi_M5_abstracted_body_eval:
  "pp_e_eval pp_e_default_constants (extend_env K \<rho>)
      (pterm_to_oterm (pabstract_const k gb_unary (pterm_of_oterm M))) =
    pp_e_eval (gi_M5_basis_constants k K) \<rho> M"
proof -
  have constants: "(\<lambda>c \<tau>. if k = c \<and> gb_unary = \<tau> then K else pp_e_default_constants c \<tau>) =
    gi_M5_basis_constants k K"
    by (rule ext, rule ext; simp add: gi_M5_basis_constants_def pp_e_default_constants_def eq_commute)
  show ?thesis
    by (simp only: pabstract_const_def gi_M5_pconst_subst_eval pterm_to_oterm.simps
      pp_e_eval.simps(1) extend_env.simps constants pterm_to_pshift pp_e_eval_shift pterm_to_of)
qed

theorem gi_M5_constant_abstractor_application:
  assumes member: "Elem K (pp_e_domain gb_unary)"
  shows "pp_e_closed_den (gi_M5_constant_abstractor k M) \<acute> K = gi_M5_expanded_closed_den k K M"
  by (simp only: pp_e_closed_den_def gi_M5_constant_abstractor_def pp_e_eval.simps(4)
    Lambda_app[OF member] gi_M5_abstracted_body_eval gi_M5_expanded_closed_den_def)

text \<open>
  Thus each closed k-only term M:σ has a closed LOGICAL abstraction
  A_M:(t→t)→σ whose exact value applied to K equals the original expanded
  value. The replacement is indexed by the pair (k,t→t), and shifts under
  every binder. This covers abstraction and higher-order quantifiers in M;
  no closure of the candidate family under lambda abstraction is assumed.
\<close>

section \<open>Leastness among all-type application-closed families\<close>

theorem gi_M5_expanded_basis_least:
  fixes D :: "otype \<Rightarrow> ZF set"
  assumes member_K: "Elem K (pp_e_domain gb_unary)"
    and logical: "\<And>\<sigma> M. [] \<turnstile> M : \<sigma> \<Longrightarrow> pp_logical_vocabulary M \<Longrightarrow> pp_e_closed_den M \<in> D \<sigma>"
    and exotic: "K \<in> D gb_unary"
    and application: "\<And>\<sigma> \<tau> F x. F \<in> D (Arr \<sigma> \<tau>) \<Longrightarrow> x \<in> D \<sigma> \<Longrightarrow> F \<acute> x \<in> D \<tau>"
    and value_member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  shows "x \<in> D \<sigma>"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>"
    and signature: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
    and shape: "x = gi_M5_expanded_closed_den k K M"
    using value_member by (rule gi_M5_expanded_basisE)
  have abstractor: "pp_e_closed_den (gi_M5_constant_abstractor k M) \<in> D (Arr gb_unary \<sigma>)"
    by (rule logical[OF gi_M5_constant_abstractor_type[OF typed] gi_M5_constant_abstractor_logical[OF signature]])
  have applied: "pp_e_closed_den (gi_M5_constant_abstractor k M) \<acute> K \<in> D \<sigma>"
    by (rule application[OF abstractor exotic])
  show ?thesis using applied by (simp only: gi_M5_constant_abstractor_application[OF member_K] shape)
qed

inductive gi_M5_application_generated :: "ZF \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> bool" for K where
  Logical: "[] \<turnstile> M : \<sigma> \<Longrightarrow> pp_logical_vocabulary M \<Longrightarrow>
    gi_M5_application_generated K \<sigma> (pp_e_closed_den M)"
| Exotic: "gi_M5_application_generated K gb_unary K"
| Application: "gi_M5_application_generated K (Arr \<sigma> \<tau>) F \<Longrightarrow>
    gi_M5_application_generated K \<sigma> x \<Longrightarrow> gi_M5_application_generated K \<tau> (F \<acute> x)"

definition gi_M5_application_hull :: "ZF \<Rightarrow> otype \<Rightarrow> ZF set" where
  "gi_M5_application_hull K \<sigma> = {x. gi_M5_application_generated K \<sigma> x}"

lemma gi_M5_application_hull_logical:
  "[] \<turnstile> M : \<sigma> \<Longrightarrow> pp_logical_vocabulary M \<Longrightarrow> pp_e_closed_den M \<in> gi_M5_application_hull K \<sigma>"
  unfolding gi_M5_application_hull_def
  by (rule CollectI, rule gi_M5_application_generated.Logical; assumption)

lemma gi_M5_application_hull_K:
  "K \<in> gi_M5_application_hull K gb_unary"
  unfolding gi_M5_application_hull_def by (rule CollectI, rule gi_M5_application_generated.Exotic)

lemma gi_M5_application_hull_closed:
  "F \<in> gi_M5_application_hull K (Arr \<sigma> \<tau>) \<Longrightarrow> x \<in> gi_M5_application_hull K \<sigma> \<Longrightarrow>
    F \<acute> x \<in> gi_M5_application_hull K \<tau>"
  unfolding gi_M5_application_hull_def
  by (simp only: mem_Collect_eq; rule gi_M5_application_generated.Application; assumption)

theorem gi_M5_expanded_basis_subset_application_hull:
  assumes member_K: "Elem K (pp_e_domain gb_unary)"
  shows "gi_M5_expanded_basis k K \<sigma> \<subseteq> gi_M5_application_hull K \<sigma>"
proof
  fix x assume member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  show "x \<in> gi_M5_application_hull K \<sigma>"
    by (rule gi_M5_expanded_basis_least[where D="gi_M5_application_hull K",
      OF member_K gi_M5_application_hull_logical
      gi_M5_application_hull_K gi_M5_application_hull_closed member])
qed

context gi_exact_expanded_stock
begin

lemma gi_M5_generated_in_expanded_basis:
  assumes generated: "gi_M5_application_generated K \<sigma> x"
  shows "x \<in> gi_M5_expanded_basis k K \<sigma>"
  using generated
proof (induction rule: gi_M5_application_generated.induct)
  case (Logical M \<sigma>)
  show ?case by (rule gi_M5_expanded_basis_contains_logical[OF Logical.hyps])
next
  case Exotic
  show ?case by (rule gi_M5_expanded_basis_contains_K)
next
  case (Application \<sigma> \<tau> F x)
  show ?case by (rule gi_M5_expanded_basis_application[OF Application.IH])
qed

theorem gi_M5_expanded_basis_is_application_hull:
  "gi_M5_expanded_basis k K \<sigma> = gi_M5_application_hull K \<sigma>"
proof
  show "gi_M5_expanded_basis k K \<sigma> \<subseteq> gi_M5_application_hull K \<sigma>"
    by (rule gi_M5_expanded_basis_subset_application_hull[OF K_typed])
  show "gi_M5_application_hull K \<sigma> \<subseteq> gi_M5_expanded_basis k K \<sigma>"
    unfolding gi_M5_application_hull_def using gi_M5_generated_in_expanded_basis by blast
qed

corollary gi_M5_named_expanded_basis_is_application_hull:
  assumes rich: "sg_rich G"
  shows "gi_M5_named_expanded_basis k K G \<sigma> = gi_M5_application_hull K \<sigma>"
  by (simp only: gi_M5_named_expanded_basis_equal[OF rich] gi_M5_expanded_basis_is_application_hull)

end

text \<open>
  The inductive hull has exactly three clauses: original closed logical
  values, K itself, and application. Its equality with the complete
  expanded closed-term basis is therefore stronger than simply showing
  that this basis is application-closed. The all-type leastness theorem
  needs only typed K; invariance and name freshness are retained by the
  existing expanded-stock locale for its other semantic uses.

  This is a statement about the unsaturated basis of actual values.
  Local-identity saturation, the final Pure/Fun interpretation, and PP
  remain separate; no lambda-closure of an arbitrary candidate D was used.
\<close>

end
