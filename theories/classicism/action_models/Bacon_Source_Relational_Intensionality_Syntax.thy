theory Bacon_Source_Relational_Intensionality_Syntax
  imports Bacon_Source_Relational_Binder_Vectors
    Bacon_Source_Relational_Substitution_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Logical_Syntax
begin

section \<open>Capture-safe replacement of a scalar guard under a λ prefix\<close>

lemma paper_R_intensionality_lam_subst:
  assumes marker: "r \<notin> set ns"
  shows "named_subst r B (named_lam_vec ns A) = named_lam_vec ns (named_subst r B A)"
  using marker by (induction ns) auto

lemma paper_R_intensionality_lam_free_for:
  assumes marker: "r \<notin> set ns" and avoid: "set ns \<inter> named_fv B = {}"
    and body: "named_free_for B r A"
  shows "named_free_for B r (named_lam_vec ns A)"
  using marker avoid body by (induction ns) auto

lemma paper_R_intensionality_guard_test_beta:
  assumes fixed_left: "r \<notin> named_fv L" and fixed_body: "r \<notin> named_fv P"
    and marker: "r \<notin> set ns" and avoid: "set ns \<inter> named_fv B = {}"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam r (named_paper_eq \<theta> L
      (named_lam_vec ns (named_paper_and P (NVar r))))) B)
    (named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P B)))"
proof -
  have left_free: "named_free_for B r L" by (rule named_free_for_fresh[OF fixed_left])
  have body_free: "named_free_for B r P" by (rule named_free_for_fresh[OF fixed_body])
  have and_free: "named_free_for B r (named_paper_and P (NVar r))"
    by (simp add: named_paper_and_def body_free)
  have vector_free: "named_free_for B r (named_lam_vec ns (named_paper_and P (NVar r)))"
    by (rule paper_R_intensionality_lam_free_for[OF marker avoid and_free])
  have free_for: "named_free_for B r
      (named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P (NVar r))))"
    by (simp add: named_paper_eq_def left_free vector_free)
  have and_subst: "named_subst r B (named_paper_and P (NVar r)) = named_paper_and P B"
    by (simp add: named_paper_and_def named_subst_fresh[OF fixed_body])
  have replacement: "named_subst r B
      (named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P (NVar r)))) =
      named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P B))"
    by (simp only: named_paper_eq_def named_subst.simps named_subst_fresh[OF fixed_left]
      paper_R_intensionality_lam_subst[OF marker] and_subst)
  have contraction: "named_beta_contract
      (NApp (NLam r (named_paper_eq \<theta> L
        (named_lam_vec ns (named_paper_and P (NVar r))))) B)
      (named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P B)))"
    using named_beta_contract.beta[OF free_for] by (simp only: replacement)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam r (named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P (NVar r))))) B"
    and N="named_paper_eq \<theta> L (named_lam_vec ns (named_paper_and P B))", OF contraction])
qed

text \<open>
  The payload B may be open. Its free variables must avoid the
  displayed prefix, while the marker r is fresh in the fixed terms
  and is not one of those binders. These are literal substitution
  and β facts, not a general λ-congruence rule.
  Source role: the guarded replacement in the Intensionality proof, p.17.
\<close>

end
