theory Goodman_Exact_Fixed_Constant_Gluing
  imports "Goodman_Integration_Exact_QLN.Goodman_Exact_10_1_Transfer"
begin

section \<open>Preserving one invariant primitive literally during exact gluing\<close>

definition gi_exact_fixed_glued_constants ::
  "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
    string \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF" where
  "gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma> =
    (if c = k \<and> \<sigma> = \<kappa> then K else pp_e_Bacon_glued_constants A c \<sigma>)"

text \<open>
  Ordinary exact gluing preserves the given interpretations after taking
  each branch action. It need not assign a distinguished primitive its
  original global value. Here we explicitly overwrite the single typed
  occurrence (k,κ) by K. Its action invariance and the family's common
  interpretation of that occurrence preserve all branch equations.
  All other typed occurrences retain the original exact glued value.
\<close>

lemma gi_exact_fixed_glued_constants_typed:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and K_typed: "Elem K (pp_e_domain \<kappa>)"
  shows "Elem (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) (pp_e_domain \<sigma>)"
  using K_typed pp_e_Bacon_glued_constants_typed[OF family, where c=c and \<sigma>=\<sigma>]
  by (auto simp: gi_exact_fixed_glued_constants_def)

lemma gi_exact_fixed_glued_constant_at:
  "gi_exact_fixed_glued_constants A k \<kappa> K k \<kappa> = K"
  by (simp only: gi_exact_fixed_glued_constants_def; simp)

lemma gi_exact_fixed_glued_constant_other:
  assumes other: "c \<noteq> k \<or> \<sigma> \<noteq> \<kappa>"
  shows "gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma> = pp_e_Bacon_glued_constants A c \<sigma>"
  using other by (auto simp: gi_exact_fixed_glued_constants_def)

lemma gi_exact_fixed_glued_completed_action:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
  shows "pp_b_action \<sigma> [n] (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) =
    pp_e_Bacon_completed_constants A n c \<sigma>"
proof (cases "c = k \<and> \<sigma> = \<kappa>")
  case True
  show ?thesis using True fragment_type invariant[of "[n]"] fixed[of n]
    by (simp add: gi_exact_fixed_glued_constants_def pp_e_Bacon_completed_constants_def)
next
  case False
  show ?thesis
    by (simp only: gi_exact_fixed_glued_constants_def False if_False;
      rule pp_e_Bacon_glued_completed_action[OF family])
qed

theorem gi_exact_fixed_glued_branch_action:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
    and target_type: "pp_e_propositional_type \<sigma>"
  shows "pp_b_action \<sigma> [n] (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) = A n c \<sigma>"
  by (simp only: gi_exact_fixed_glued_completed_action[
        where A=A and k=k and \<kappa>=\<kappa> and K=K, OF family fragment_type invariant fixed]
      pp_e_Bacon_completed_constants_def target_type if_True)

section \<open>Exact action-related evaluation with the fixed primitive\<close>

theorem gi_exact_fixed_glued_closed_term_action:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and K_typed: "Elem K (pp_e_domain \<kappa>)"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
    and typed: "[] \<turnstile> M : \<tau>"
    and fragment: "pp_e_propositional_term M"
  shows "pp_b_action \<tau> [n]
      (pp_e_eval (gi_exact_fixed_glued_constants A k \<kappa> K) pp_e_closed_env M) =
    pp_e_eval (A n) pp_e_closed_env M"
proof -
  interpret Related: pp_e_action_related_constants
      "gi_exact_fixed_glued_constants A k \<kappa> K"
      "pp_e_Bacon_completed_constants A n" "[n]"
  proof
    show "Elem (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) (pp_e_domain \<sigma>)" for c \<sigma>
      by (rule gi_exact_fixed_glued_constants_typed[
        where A=A and k=k and \<kappa>=\<kappa> and K=K, OF family K_typed])
    show "Elem (pp_e_Bacon_completed_constants A n c \<sigma>) (pp_e_domain \<sigma>)" for c \<sigma>
      by (rule pp_e_Bacon_completed_constants_typed[OF family])
    show "pp_b_action \<sigma> [n] (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) =
      pp_e_Bacon_completed_constants A n c \<sigma>" for \<sigma> c
      by (rule gi_exact_fixed_glued_completed_action[
        where A=A and k=k and \<kappa>=\<kappa> and K=K, OF family fragment_type invariant fixed])
  qed
  have evaluated: "pp_b_action \<tau> [n]
      (pp_e_eval (gi_exact_fixed_glued_constants A k \<kappa> K) pp_e_closed_env M) =
      pp_e_eval (pp_e_Bacon_completed_constants A n) pp_e_closed_env M"
    by (rule Related.pp_e_eval_action_related[OF typed pp_e_empty_env_typed pp_e_closed_env_action])
  show ?thesis using evaluated
    by (simp only: pp_e_eval_completed_constants_propositional[OF fragment])
qed

theorem gi_exact_fixed_glued_named_term_action:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and K_typed: "Elem K (pp_e_domain \<kappa>)"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "pp_b_action \<tau> [n]
      (gi_exact_named_denote (gi_exact_fixed_glued_constants A k \<kappa> K) G g M) =
    gi_exact_named_denote (A n) G h M"
proof -
  have decoded_type: "[] \<turnstile> gi_exact_decode G M : \<tau>"
    by (rule gi_closed_named_decode_type[OF language closed_term])
  have decoded_fragment: "pp_e_propositional_term (gi_exact_decode G M)"
    by (simp only: gi_exact_named_propositional_decode_iff; rule fragment)
  have action: "pp_b_action \<tau> [n]
      (pp_e_eval (gi_exact_fixed_glued_constants A k \<kappa> K) pp_e_closed_env (gi_exact_decode G M)) =
      pp_e_eval (A n) pp_e_closed_env (gi_exact_decode G M)"
    by (rule gi_exact_fixed_glued_closed_term_action[
      where A=A and k=k and \<kappa>=\<kappa> and K=K,
      OF family fragment_type K_typed invariant fixed decoded_type decoded_fragment])
  show ?thesis
    by (simp only: gi_exact_closed_named_decoder_value[OF closed_term]; rule action)
qed

corollary gi_exact_fixed_glued_named_truth_branch:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and K_typed: "Elem K (pp_e_domain \<kappa>)"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
    and language: "book_theory_formula \<Sigma> G M"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "pp_e_holds (gi_exact_named_denote (gi_exact_fixed_glued_constants A k \<kappa> K) G g M) [n] =
    pp_e_holds (gi_exact_named_denote (A n) G h M) []"
proof -
  have action: "pp_b_action Prop [n]
      (gi_exact_named_denote (gi_exact_fixed_glued_constants A k \<kappa> K) G g M) =
      gi_exact_named_denote (A n) G h M"
    by (rule gi_exact_fixed_glued_named_term_action[
      where A=A and k=k and \<kappa>=\<kappa> and K=K,
      OF family fragment_type K_typed invariant fixed language closed_term fragment])
  have at_root: "pp_e_holds (pp_b_action Prop [n]
      (gi_exact_named_denote (gi_exact_fixed_glued_constants A k \<kappa> K) G g M)) [] =
      pp_e_holds (gi_exact_named_denote (A n) G h M) []"
    by (rule arg_cong[where f="\<lambda>p. pp_e_holds p []", OF action])
  show ?thesis using at_root by simp
qed

section \<open>The fixed-primitive version of Theorem 10.1\<close>

theorem gi_exact_Bacon_10_1_fixed_constant_named:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
      Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and fragment_type: "pp_e_propositional_type \<kappa>"
    and K_typed: "Elem K (pp_e_domain \<kappa>)"
    and invariant: "\<And>i. pp_b_action \<kappa> i K = K"
    and fixed: "\<And>n. A n k \<kappa> = K"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_e_domain \<sigma>)) \<and>
    C k \<kappa> = K \<and>
    (\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
      pp_b_action \<sigma> [n] (C c \<sigma>) = A n c \<sigma>) \<and>
    (\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow> gi_exact_named_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n] (gi_exact_named_denote C G g M) = gi_exact_named_denote (A n) G h M)"
proof (rule exI[where x="gi_exact_fixed_glued_constants A k \<kappa> K"], intro conjI)
  show "\<forall>c \<sigma>. Elem (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) (pp_e_domain \<sigma>)"
    by (intro allI; rule gi_exact_fixed_glued_constants_typed[
      where A=A and k=k and \<kappa>=\<kappa> and K=K, OF family K_typed])
next
  show "gi_exact_fixed_glued_constants A k \<kappa> K k \<kappa> = K"
    by (rule gi_exact_fixed_glued_constant_at)
next
  show "\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
      pp_b_action \<sigma> [n] (gi_exact_fixed_glued_constants A k \<kappa> K c \<sigma>) = A n c \<sigma>"
    by (intro allI impI; rule gi_exact_fixed_glued_branch_action[
      where A=A and k=k and \<kappa>=\<kappa> and K=K,
      OF family fragment_type invariant fixed]; assumption)
next
  show "\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow> gi_exact_named_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n]
        (gi_exact_named_denote (gi_exact_fixed_glued_constants A k \<kappa> K) G g M) =
        gi_exact_named_denote (A n) G h M"
    by (intro allI impI; rule gi_exact_fixed_glued_named_term_action[
      where A=A and k=k and \<kappa>=\<kappa> and K=K,
      OF family fragment_type K_typed invariant fixed]; assumption)
qed

text \<open>
  The final theorem retains the explicit t-generated type and term
  restrictions, the common primitive interpretation in every member of
  the countable family, and action invariance of K. K's typing is displayed
  separately for use as a construction certificate; it also follows from
  family typing, the fixed-coordinate premise, and κ's fragment condition.

  The result covers arbitrary declared string signatures and all closed
  named terms of this fragment, not only a forward-translation image.
  Arbitrary assignments on both sides are permitted because terms are
  closed. No claim is made about gluing arbitrary e-containing data, about
  the unmodified glued value at (k,κ), or about a rebuilt Pure/Fun model.
  The carriers and action are Bacon's exact HOL–ZF construction.
\<close>

end
