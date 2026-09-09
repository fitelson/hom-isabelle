theory Bacon_H_BBK_Canonical_Quantifiers
  imports Bacon_H_BBK_Canonical_Truth
begin

section \<open>Quantification over canonical identity classes\<close>

text \<open>
  𝔐,g ⊨ ∀xσ A ⇔ ∀a ∈ Dσ, 𝔐,g[x↦a] ⊨ A; replace ∀ by ∃ for existence. Bacon–Dorr,
  Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: case_nat inserts the bound variable at slot zero. Every
  value is a closed-term class, and representative independence permits each Henkin
  witness to serve as its representative.

  Status: Quantifiers range over the actual class domains, not just a selected list of
  names.
\<close>

context H_closed_Henkin
begin

lemma H_BBK_env_extend:
  assumes env: "H_BBK_env_typed \<Gamma> \<rho>" and domain: "v \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_env_typed (\<sigma> # \<Gamma>) (case_nat v \<rho>)"
proof (unfold H_BBK_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "case_nat v \<rho> n \<in> H_BBK_domain \<tau>"
  proof (cases n)
    case 0
    have same_type: "\<tau> = \<sigma>" using lookup by (simp add: 0)
    show ?thesis using domain by (simp add: 0 same_type)
  next
    case (Suc m)
    have tail_lookup: "lookup \<Gamma> m = Some \<tau>" using lookup by (simp add: Suc)
    have tail_domain: "\<rho> m \<in> H_BBK_domain \<tau>" by (rule H_BBK_env_lookup[OF env tail_lookup])
    show ?thesis using tail_domain by (simp add: Suc)
  qed
qed

lemma H_BBK_binder_representatives:
  assumes env: "H_BBK_env_typed \<Gamma> \<rho>" and W: "[] \<turnstile> W : \<sigma>"
    and lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  shows "H_BBK_class \<tau> (case_nat W (\<lambda>k. H_BBK_rep (\<rho> k)) n) =
    case_nat (H_BBK_class \<sigma> W) \<rho> n"
proof (cases n)
  case 0
  have same_type: "\<tau> = \<sigma>" using lookup by (simp add: 0)
  show ?thesis by (simp add: 0 same_type)
next
  case (Suc m)
  have tail_lookup: "lookup \<Gamma> m = Some \<tau>" using lookup by (simp add: Suc)
  have domain: "\<rho> m \<in> H_BBK_domain \<tau>" by (rule H_BBK_env_lookup[OF env tail_lookup])
  show ?thesis by (simp add: Suc H_BBK_rep_reconstruct[OF domain])
qed

lemma H_BBK_binder_truth_class:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and env: "H_BBK_env_typed \<Gamma> \<rho>" and W: "[] \<turnstile> W : \<sigma>"
  shows "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>) A)
    \<longleftrightarrow> subst (case_nat W (\<lambda>n. H_BBK_rep (\<rho> n))) A \<in> T"
proof -
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  have st: "term_subst_typed \<Gamma> [] ?s" by (rule H_BBK_rep_substitution_typed[OF env])
  have extended_st: "term_subst_typed (\<sigma> # \<Gamma>) [] (case_nat W ?s)"
    by (rule term_subst_typed_extend[OF st W])
  have domain: "H_BBK_class \<sigma> W \<in> H_BBK_domain \<sigma>" by (rule H_BBK_class_in_domain[OF W])
  have extended_env: "H_BBK_env_typed (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>)"
    by (rule H_BBK_env_extend[OF env domain])
  have represents: "\<And>n \<tau>. lookup (\<sigma> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      H_BBK_class \<tau> (case_nat W ?s n) = case_nat (H_BBK_class \<sigma> W) \<rho> n"
    by (rule H_BBK_binder_representatives[OF env W])
  show ?thesis
    by (rule H_BBK_truth_representatives[where \<Gamma>="\<sigma> # \<Gamma>" and A=A
          and \<rho>="case_nat (H_BBK_class \<sigma> W) \<rho>" and s="case_nat W ?s",
          OF body extended_env extended_st represents])
qed

subsection \<open>Quantifier membership in terms of all closed instances\<close>

text \<open>
  ∀xσ A ∈ T ⇔ ∀W : σ closed, A[W/x] ∈ T; the existential clause uses some W.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Henkin witness completeness supplies the converse to
  universal instantiation and the witness direction for existence.

  Status: Closed typed instances only, relative to the fixed Henkin theory.
\<close>

lemma H_BBK_lifted_body_type:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "[\<sigma>] \<turnstile> subst (lift_subst (\<lambda>n. H_BBK_rep (\<rho> n))) A : Prop"
proof -
  have st: "term_subst_typed \<Gamma> [] (\<lambda>n. H_BBK_rep (\<rho> n))"
    by (rule H_BBK_rep_substitution_typed[OF env])
  have lifted: "term_subst_typed (\<sigma> # \<Gamma>) [\<sigma>] (lift_subst (\<lambda>n. H_BBK_rep (\<rho> n)))"
    by (rule term_subst_typed_lift[OF st])
  show ?thesis by (rule term_subst_preserves_typing[OF body lifted])
qed

lemma H_BBK_truth_Forall_terms:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Forall \<sigma> A)) \<longleftrightarrow>
    (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst (case_nat W (\<lambda>n. H_BBK_rep (\<rho> n))) A \<in> T)"
proof -
  have quantified: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop" by (rule has_type.Forall[OF body])
  have lifted: "[\<sigma>] \<turnstile> subst (lift_subst (\<lambda>n. H_BBK_rep (\<rho> n))) A : Prop"
    by (rule H_BBK_lifted_body_type[OF body env])
  show ?thesis
    using H_Henkin_forall_mem_iff[OF henkin lifted]
    by (simp only: H_BBK_truth_lemma[OF quantified env] subst.simps subst0_subst_lift)
qed

lemma H_BBK_truth_Exists_terms:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Exists \<sigma> A)) \<longleftrightarrow>
    (\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst (case_nat W (\<lambda>n. H_BBK_rep (\<rho> n))) A \<in> T)"
proof -
  have quantified: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop" by (rule has_type.Exists[OF body])
  have lifted: "[\<sigma>] \<turnstile> subst (lift_subst (\<lambda>n. H_BBK_rep (\<rho> n))) A : Prop"
    by (rule H_BBK_lifted_body_type[OF body env])
  show ?thesis
    using H_Henkin_exists_mem_iff[OF henkin lifted]
    by (simp only: H_BBK_truth_lemma[OF quantified env] subst.simps subst0_subst_lift)
qed

subsection \<open>Quantifier truth over the actual domains\<close>

text \<open>
  v(⟦∀xσ A⟧g) = 1 ⇔ ∀a ∈ Dσ, v(⟦A⟧g[x↦a]) = 1. Bacon–Dorr, Theorem 3.2, p. 45 n. 64;
  Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: The proof replaces each domain element by a closed
  representative, applies the membership characterization, and transports back to the
  same assignment.

  Status: The universal and existential BBK clauses are proved with domain guards.
\<close>

lemma H_BBK_truth_Forall:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Forall \<sigma> A)) \<longleftrightarrow>
    (\<forall>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A))"
proof
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  assume truth: "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Forall \<sigma> A))"
  have all_terms: "\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst (case_nat W ?s) A \<in> T"
    using H_BBK_truth_Forall_terms[OF body env] truth by blast
  show "\<forall>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
  proof (intro ballI)
    fix v
    assume domain: "v \<in> H_BBK_domain \<sigma>"
    obtain W where W: "[] \<turnstile> W : \<sigma>" and v: "v = H_BBK_class \<sigma> W"
      by (rule H_BBK_domain_representation[OF domain])
    have inst_mem: "subst (case_nat W ?s) A \<in> T" using all_terms W by blast
    have truth_W: "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>) A)"
      using H_BBK_binder_truth_class[OF body env W] inst_mem by blast
    show "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
      using truth_W by (simp only: v)
  qed
next
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  assume all_values: "\<forall>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
  have all_terms: "\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst (case_nat W ?s) A \<in> T"
  proof (intro allI impI)
    fix W
    assume W: "[] \<turnstile> W : \<sigma>"
    have domain: "H_BBK_class \<sigma> W \<in> H_BBK_domain \<sigma>" by (rule H_BBK_class_in_domain[OF W])
    have truth_W: "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>) A)"
      using all_values domain by blast
    show "subst (case_nat W ?s) A \<in> T"
      using H_BBK_binder_truth_class[OF body env W] truth_W by blast
  qed
  show "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Forall \<sigma> A))"
    using H_BBK_truth_Forall_terms[OF body env] all_terms by blast
qed

lemma H_BBK_truth_Exists:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Exists \<sigma> A)) \<longleftrightarrow>
    (\<exists>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A))"
proof
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  assume truth: "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Exists \<sigma> A))"
  obtain W where W: "[] \<turnstile> W : \<sigma>" and inst_mem: "subst (case_nat W ?s) A \<in> T"
    using H_BBK_truth_Exists_terms[OF body env] truth by blast
  have domain: "H_BBK_class \<sigma> W \<in> H_BBK_domain \<sigma>" by (rule H_BBK_class_in_domain[OF W])
  have truth_W: "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>) A)"
    using H_BBK_binder_truth_class[OF body env W] inst_mem by blast
  show "\<exists>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
    by (rule bexI[where x="H_BBK_class \<sigma> W"]) (rule truth_W, rule domain)
next
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  assume some_value: "\<exists>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
  obtain v where domain: "v \<in> H_BBK_domain \<sigma>"
    and truth_v: "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat v \<rho>) A)"
    using some_value by blast
  obtain W where W: "[] \<turnstile> W : \<sigma>" and v: "v = H_BBK_class \<sigma> W"
    by (rule H_BBK_domain_representation[OF domain])
  have truth_W: "H_BBK_holds (H_BBK_den (\<sigma> # \<Gamma>) (case_nat (H_BBK_class \<sigma> W) \<rho>) A)"
    using truth_v by (simp only: v)
  have inst_mem: "subst (case_nat W ?s) A \<in> T"
    using H_BBK_binder_truth_class[OF body env W] truth_W by blast
  have some_term: "\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst (case_nat W ?s) A \<in> T"
    by (rule exI[where x=W], rule conjI) (rule W, rule inst_mem)
  show "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Exists \<sigma> A))"
    using H_BBK_truth_Exists_terms[OF body env] some_term by blast
qed

subsection \<open>A context-free interpretation and conversion at every type\<close>

text \<open>
  ⟦M⟧g is independent of a supplied typing context, and M ≡βη N ⇒ ⟦M⟧g = ⟦N⟧g.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: After representatives close M, infer_type recovers its
  type. H_BBK_denote agrees with the earlier context-indexed H_BBK_den on typed
  assignments.

  Status: Conversion is covered at every type; the following model file separately
  discharges locality and interface fields.
\<close>

definition H_BBK_denote :: "(nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value" where
  "H_BBK_denote \<rho> M = (let N = subst (\<lambda>n. H_BBK_rep (\<rho> n)) M
    in H_BBK_class (the (infer_type [] N)) N)"

lemma H_BBK_denote_eq_den:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_denote \<rho> M = H_BBK_den \<Gamma> \<rho> M"
proof -
  have closed_type: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) M : \<tau>"
    by (rule H_BBK_closed_instance_type[OF typed env])
  show ?thesis
    by (simp add: H_BBK_denote_def infer_type_complete[OF closed_type] H_BBK_den_typed_form[OF typed])
qed

lemma H_BBK_den_beta_eta:
  assumes conversion: "beta_eta_equiv \<Gamma> \<tau> M N" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_den \<Gamma> \<rho> M = H_BBK_den \<Gamma> \<rho> N"
proof -
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  have M: "\<Gamma> \<turnstile> M : \<tau>" and N: "\<Gamma> \<turnstile> N : \<tau>"
    using beta_eta_equiv_types[OF conversion] by blast+
  have st: "term_subst_typed \<Gamma> [] ?s" by (rule H_BBK_rep_substitution_typed[OF env])
  have closed_conversion: "beta_eta_equiv [] \<tau> (subst ?s M) (subst ?s N)"
    by (rule beta_eta_equiv_subst[OF conversion st])
  have eq: "H_term_eq \<tau> (subst ?s M) (subst ?s N)" by (rule H_term_eq_beta_eta[OF closed_conversion])
  have closed_M: "[] \<turnstile> subst ?s M : \<tau>" by (rule term_subst_preserves_typing[OF M st])
  have closed_N: "[] \<turnstile> subst ?s N : \<tau>" by (rule term_subst_preserves_typing[OF N st])
  have classes: "H_BBK_class \<tau> (subst ?s M) = H_BBK_class \<tau> (subst ?s N)"
    using H_BBK_class_eq_iff[OF closed_M closed_N] eq by blast
  show ?thesis by (simp only: H_BBK_den_typed_form[OF M] H_BBK_den_typed_form[OF N] classes)
qed

lemma H_BBK_denote_beta_eta:
  assumes conversion: "beta_eta_equiv \<Gamma> \<tau> M N" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_denote \<rho> M = H_BBK_denote \<rho> N"
proof -
  have M: "\<Gamma> \<turnstile> M : \<tau>" and N: "\<Gamma> \<turnstile> N : \<tau>"
    using beta_eta_equiv_types[OF conversion] by blast+
  show ?thesis
    by (simp only: H_BBK_denote_eq_den[OF M env] H_BBK_denote_eq_den[OF N env]
          H_BBK_den_beta_eta[OF conversion env])
qed

text \<open>
  The canonical truth clauses now cover all logical constructors, and the
  interpretation respects βη conversion at every type.  A BBK locale
  interpretation still requires locality on precisely the free slots and
  coherence under their renaming, together with the explicit interface
  bridge.  No locale interpretation or model-existence theorem is asserted
  in this file.  Source-language translation and arbitrary-signature
  Henkinization remain separate from these canonical-model ingredients.
\<close>

end
end
