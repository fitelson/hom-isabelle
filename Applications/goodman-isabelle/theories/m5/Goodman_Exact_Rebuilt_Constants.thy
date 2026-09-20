theory Goodman_Exact_Rebuilt_Constants
  imports Goodman_Exact_Expanded_Stock Goodman_Exact_Basis_Seed
begin

section \<open>Evaluation depends only on declared constant coordinates\<close>

lemma gi_M5_eval_constant_agreement:
  assumes admitted: "oterm_in_string_signature \<Sigma> M"
    and agreement: "\<And>c \<tau>. c \<in> \<Sigma> \<tau> \<Longrightarrow> C c \<tau> = D c \<tau>"
  shows "pp_e_eval C \<rho> M = pp_e_eval D \<rho> M"
  using admitted
proof (induction M arbitrary: \<rho>)
  case (Var n)
  show ?case by (simp only: pp_e_eval.simps)
next
  case (Const c \<tau>)
  have member: "c \<in> \<Sigma> \<tau>" using Const.prems by simp
  show ?case by (simp only: pp_e_eval.simps agreement[OF member])
next
  case (App M N)
  have ma: "oterm_in_string_signature \<Sigma> M" and na: "oterm_in_string_signature \<Sigma> N"
    using App.prems by simp_all
  show ?case by (simp only: pp_e_eval.simps App.IH(1)[OF ma] App.IH(2)[OF na])
next
  case (Lam \<sigma> M)
  have ma: "oterm_in_string_signature \<Sigma> M" using Lam.prems by simp
  have body: "pp_e_eval C (extend_env x \<rho>) M = pp_e_eval D (extend_env x \<rho>) M" for x
    by (rule Lam.IH[OF ma])
  show ?case by (simp only: pp_e_eval.simps body)
next
  case (Eq \<sigma> M N)
  have ma: "oterm_in_string_signature \<Sigma> M" and na: "oterm_in_string_signature \<Sigma> N"
    using Eq.prems by simp_all
  show ?case by (simp only: pp_e_eval.simps Eq.IH(1)[OF ma] Eq.IH(2)[OF na])
next
  case (Neg M)
  have ma: "oterm_in_string_signature \<Sigma> M" using Neg.prems by simp
  show ?case by (simp only: pp_e_eval.simps Neg.IH[OF ma])
next
  case (Conj M N)
  have ma: "oterm_in_string_signature \<Sigma> M" and na: "oterm_in_string_signature \<Sigma> N"
    using Conj.prems by simp_all
  show ?case by (simp only: pp_e_eval.simps Conj.IH(1)[OF ma] Conj.IH(2)[OF na])
next
  case (Disj M N)
  have ma: "oterm_in_string_signature \<Sigma> M" and na: "oterm_in_string_signature \<Sigma> N"
    using Disj.prems by simp_all
  show ?case by (simp only: pp_e_eval.simps Disj.IH(1)[OF ma] Disj.IH(2)[OF na])
next
  case (Imp M N)
  have ma: "oterm_in_string_signature \<Sigma> M" and na: "oterm_in_string_signature \<Sigma> N"
    using Imp.prems by simp_all
  show ?case by (simp only: pp_e_eval.simps Imp.IH(1)[OF ma] Imp.IH(2)[OF na])
next
  case (Forall \<sigma> M)
  have ma: "oterm_in_string_signature \<Sigma> M" using Forall.prems by simp
  have body: "pp_e_eval C (extend_env x \<rho>) M = pp_e_eval D (extend_env x \<rho>) M" for x
    by (rule Forall.IH[OF ma])
  show ?case by (simp only: pp_e_eval.simps body)
next
  case (Exists \<sigma> M)
  have ma: "oterm_in_string_signature \<Sigma> M" using Exists.prems by simp
  have body: "pp_e_eval C (extend_env x \<rho>) M = pp_e_eval D (extend_env x \<rho>) M" for x
    by (rule Exists.IH[OF ma])
  show ?case by (simp only: pp_e_eval.simps body)
qed

lemma gi_M5_named_constant_agreement:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and agreement: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> C c \<sigma> = D c \<sigma>"
  shows "gi_exact_named_denote C G g M = gi_exact_named_denote D G g M"
proof -
  have admitted: "oterm_in_string_signature \<Sigma> (pterm_to_oterm (book_named_to_pterm G M))"
    using book_named_translation_in_signature[OF language]
    by (simp only: pterm_string_signature_iff)
  show ?thesis unfolding gi_exact_named_denote_def
    by (rule gi_M5_eval_constant_agreement[OF admitted agreement])
qed

section \<open>The actual interpretation preserves the new primitive and Pure/Fun\<close>

definition gi_M5_rebuilt_constants :: "string \<Rightarrow> ZF \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF" where
  "gi_M5_rebuilt_constants k K c \<tau> =
    (if c = k \<and> \<tau> = gb_unary then K
     else gi_basis_internal_constants (gi_M5_expanded_basis k K) c \<tau>)"

definition gi_M5_rebuilt_named_basis ::
  "string \<Rightarrow> ZF \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> ZF set" where
  "gi_M5_rebuilt_named_basis k K G \<sigma> =
    {x. \<exists>A. book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma> \<and>
      named_fv A = {} \<and>
      x = gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A}"

context gi_exact_expanded_stock
begin

sublocale Expanded: gi_exact_invariant_basis "gi_M5_expanded_basis k K"
proof
  show "Elem x (pp_e_domain \<sigma>)" if "x \<in> gi_M5_expanded_basis k K \<sigma>" for \<sigma> x
    by (rule gi_M5_expanded_basis_typed[OF that])
next
  show "pp_b_action \<sigma> i x = x" if "x \<in> gi_M5_expanded_basis k K \<sigma>" for \<sigma> x i
    by (rule gi_M5_expanded_basis_invariant[OF that])
next
  show "countable (gi_M5_expanded_basis k K \<sigma>)" for \<sigma>
    by (rule gi_M5_expanded_basis_countable)
next
  show "f \<acute> x \<in> gi_M5_expanded_basis k K \<tau>"
    if "f \<in> gi_M5_expanded_basis k K (Arr \<sigma> \<tau>)" "x \<in> gi_M5_expanded_basis k K \<sigma>"
    for \<sigma> \<tau> f x
    by (rule gi_M5_expanded_basis_application[OF that])
next
  show "pp_e_closed_den M \<in> gi_M5_expanded_basis k K \<sigma>"
    if "[] \<turnstile> M : \<sigma>" "pp_logical_vocabulary M" for \<sigma> M
    by (rule gi_M5_expanded_basis_contains_logical[OF that])
qed

theorem gi_M5_expanded_invariant_basis:
  "gi_exact_invariant_basis (gi_M5_expanded_basis k K)"
  by (rule Expanded.gi_exact_invariant_basis_axioms)

theorem gi_M5_rebuilt_constants_typed:
  "Elem (gi_M5_rebuilt_constants k K c \<tau>) (pp_e_domain \<tau>)"
  using K_typed Expanded.gi_basis_internal_constants_typed[where c=c and \<sigma>=\<tau>]
  by (auto simp: gi_M5_rebuilt_constants_def)

theorem gi_M5_rebuilt_constants_locale:
  "pp_e_constants (gi_M5_rebuilt_constants k K)"
  by standard (rule gi_M5_rebuilt_constants_typed)

sublocale Rebuilt: pp_e_constants "gi_M5_rebuilt_constants k K"
  by (rule gi_M5_rebuilt_constants_locale)

lemma gi_M5_rebuilt_constant_at:
  "gi_M5_rebuilt_constants k K k gb_unary = K"
  by (simp add: gi_M5_rebuilt_constants_def)

lemma gi_M5_rebuilt_Pure_coordinate:
  "gi_M5_rebuilt_constants k K pp_pure_name \<tau> =
    gi_basis_internal_constants (gi_M5_expanded_basis k K) pp_pure_name \<tau>"
  using fresh_pure by (auto simp: gi_M5_rebuilt_constants_def)

lemma gi_M5_rebuilt_Fun_coordinate:
  "gi_M5_rebuilt_constants k K pp_fun_name \<tau> =
    gi_basis_internal_constants (gi_M5_expanded_basis k K) pp_fun_name \<tau>"
  using fresh_fun by (auto simp: gi_M5_rebuilt_constants_def)

lemma gi_M5_rebuilt_goodman_coordinate:
  assumes declared: "c \<in> gi_goodman_string_signature \<tau>"
  shows "gi_M5_rebuilt_constants k K c \<tau> =
    gi_basis_internal_constants (gi_M5_expanded_basis k K) c \<tau>"
  using declared gi_M5_rebuilt_Pure_coordinate gi_M5_rebuilt_Fun_coordinate
  by (auto simp: gi_goodman_string_signature_def split: if_splits)

lemma gi_M5_rebuilt_basis_coordinate:
  assumes declared: "c \<in> gi_M5_expanded_signature k \<tau>"
  shows "gi_M5_rebuilt_constants k K c \<tau> = gi_M5_basis_constants k K c \<tau>"
  using declared by (auto simp: gi_M5_expanded_signature_def gi_M5_rebuilt_constants_def gi_M5_basis_constants_def
      split: if_splits)

section \<open>The whole expanded language retains its generating denotations\<close>

theorem gi_M5_rebuilt_expanded_eval:
  assumes admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M =
    pp_e_eval (gi_M5_basis_constants k K) \<rho> M"
  by (rule gi_M5_eval_constant_agreement[OF admitted]; rule gi_M5_rebuilt_basis_coordinate; assumption)

theorem gi_M5_rebuilt_expanded_closed_denotation:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M = gi_M5_expanded_closed_den k K M"
  by (simp only: gi_M5_rebuilt_expanded_eval[OF admitted] gi_M5_expanded_closed_eval_independent[OF typed])

theorem gi_M5_rebuilt_named_expanded_denotation:
  assumes language: "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
  shows "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G g A =
    gi_exact_named_denote (gi_M5_basis_constants k K) G g A"
  by (rule gi_M5_named_constant_agreement[OF language]; rule gi_M5_rebuilt_basis_coordinate; assumption)

theorem gi_M5_rebuilt_named_basis_equal:
  assumes rich: "sg_rich G"
  shows "gi_M5_rebuilt_named_basis k K G \<sigma> = gi_M5_expanded_basis k K \<sigma>"
proof -
  have same: "gi_M5_rebuilt_named_basis k K G \<sigma> = gi_M5_named_expanded_basis k K G \<sigma>"
  proof (rule set_eqI)
    fix x
    show "x \<in> gi_M5_rebuilt_named_basis k K G \<sigma> \<longleftrightarrow>
      x \<in> gi_M5_named_expanded_basis k K G \<sigma>"
    proof
      assume member: "x \<in> gi_M5_rebuilt_named_basis k K G \<sigma>"
      obtain A where language:
          "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
        and closed_term: "named_fv A = {}"
        and value_eq: "x = gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A"
        using member unfolding gi_M5_rebuilt_named_basis_def by blast
      have agreement:
          "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A =
            gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A"
        by (rule gi_M5_rebuilt_named_expanded_denotation[OF language])
      have target_value: "x = gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A"
        by (rule trans[OF value_eq agreement])
      show "x \<in> gi_M5_named_expanded_basis k K G \<sigma>"
        unfolding gi_M5_named_expanded_basis_def
        by (rule CollectI, rule exI[where x=A], rule conjI[OF language conjI[OF closed_term target_value]])
    next
      assume member: "x \<in> gi_M5_named_expanded_basis k K G \<sigma>"
      obtain A where language:
          "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
        and closed_term: "named_fv A = {}"
        and value_eq: "x = gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A"
        using member unfolding gi_M5_named_expanded_basis_def by blast
      have agreement:
          "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A =
            gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A"
        by (rule gi_M5_rebuilt_named_expanded_denotation[OF language])
      have target_value: "x = gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A"
        by (rule trans[OF value_eq agreement[symmetric]])
      show "x \<in> gi_M5_rebuilt_named_basis k K G \<sigma>"
        unfolding gi_M5_rebuilt_named_basis_def
        by (rule CollectI, rule exI[where x=A], rule conjI[OF language conjI[OF closed_term target_value]])
    qed
  qed
  show ?thesis by (rule trans[OF same gi_M5_named_expanded_basis_equal[OF rich]])
qed

corollary gi_M5_rebuilt_exotic_constant_denotation:
  "pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> (Const k gb_unary) = K"
  by (simp only: pp_e_eval.simps gi_M5_rebuilt_constant_at)

section \<open>The native Goodman vocabulary keeps the basis model's truth\<close>

theorem gi_M5_rebuilt_native_denotation:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
  shows "gi_exact_goodman_denote (gi_M5_rebuilt_constants k K) G g A =
    gi_exact_goodman_denote (gi_basis_internal_constants (gi_M5_expanded_basis k K)) G g A"
  unfolding gi_exact_goodman_denote_def
  by (rule gi_M5_named_constant_agreement[OF gi_goodman_string_term_language[OF language]];
    rule gi_M5_rebuilt_goodman_coordinate; assumption)

theorem gi_M5_rebuilt_native_global_valid_iff:
  assumes language: "book_theory_formula gb_signature G A"
  shows "gi_exact_goodman_global_valid (gi_M5_rebuilt_constants k K) G A \<longleftrightarrow>
    gi_exact_goodman_global_valid (gi_basis_internal_constants (gi_M5_expanded_basis k K)) G A"
  by (simp only: gi_exact_goodman_global_valid_iff gi_M5_rebuilt_native_denotation[OF language])

end

text \<open>
  The rebuilt interpreter now has both required roles: the new coordinate
  literally denotes K, while Pure and Fun retain their independently
  constructed basis-model meanings. The entire closed expanded language
  denotes precisely the specified generating family in this actual
  interpreter, not only in the auxiliary interpreter used to define it.

  Agreement on the native Goodman language uses its explicit signature
  guard. It cannot be applied to a formula mentioning the new k occurrence
  as though that occurrence belonged to gb_signature. This file transports
  native global validity conditionally; global background/QLN validity is
  supplied by the separate basis-model proofs, not assumed here.
\<close>

end
