theory Bacon_Source_Relational_Classicism_A2_H
  imports Bacon_Source_Relational_Closed_LE_Generators Bacon_Source_Relational_Quantifier_Duality
begin

section \<open>The literal truth abbreviation of Figure 1\<close>

definition paper_R_named_top :: "sgcontext \<Rightarrow> 'c paper_named_term" where
  "paper_R_named_top G =
    named_paper_or
      (named_paper_all Prop (NLam (named_paper_p G) (NVar (named_paper_p G))))
      (named_paper_not (named_paper_all Prop (NLam (named_paper_p G) (NVar (named_paper_p G)))))"

lemma paper_R_named_top_closed:
  "named_fv (paper_R_named_top G) = {}"
  by (simp add: paper_R_named_top_def named_paper_primitive_fv)

lemma paper_R_named_top_atom_language:
  assumes rich: "paper_R_rich G"
  shows "paper_R_in_language \<Sigma> G
    (named_paper_all Prop (NLam (named_paper_p G) (NVar (named_paper_p G)))) Prop"
proof -
  let ?p = "named_paper_p G"
  have pt: "G ?p = Prop" by (rule paper_R_named_paper_p_type[OF rich])
  have rt: "paper_R_type Prop" by simp
  have variable: "paper_R_in_language \<Sigma> G (NVar ?p) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n="?p", OF pt rt])
  have pr: "paper_R_type (G ?p)" by (simp only: pt; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam ?p (NVar ?p)) (Arr Prop Prop)"
    using paper_R_named_identity_test_language[OF variable pr] by (simp only: pt)
  show ?thesis by (rule paper_R_predicate_all_language[OF predicate])
qed

lemma paper_R_named_top_language:
  assumes rich: "paper_R_rich G"
  shows "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop"
  unfolding paper_R_named_top_def
  by (rule paper_R_named_or_language[OF paper_R_named_top_atom_language[OF rich]
    paper_R_named_not_language[OF paper_R_named_top_atom_language[OF rich]]])

lemma paper_R_named_H_top:
  assumes rich: "paper_R_rich G"
  shows "paper_R_named_H \<Sigma> G (paper_R_named_top G)"
proof -
  let ?P = "SPOr (SPAtom (0::nat)) (SPNot (SPAtom 0))"
  let ?A = "named_paper_all Prop (NLam (named_paper_p G) (NVar (named_paper_p G)))"
  have tautology: "sprop_tautology ?P" by (simp add: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[
    OF paper_R_named_top_language[OF rich] tautology, where v="\<lambda>_. ?A"];
    simp add: paper_R_named_top_def)
qed

section \<open>The H-inclusion case of A.2 in the native p.12 presentation\<close>

text \<open>
  Figure 1, p.6 defines ⊤ literally as (∀p p)∨¬(∀p p).
  We use its existing chosen proposition name, not a primitive truth
  constant or a substituted easier tautology.

  If ⊢HᴿP, native PC gives ⊢HᴿP↔⊤. The p.12 Logical
  Equivalence constructor therefore gives (λn⃗.P)=(λn⃗.⊤).
  This is the H-inclusion base case of the native A.2 proof.
  It does not repeat the ten H cases needed in the separate finite
  Figures 3–4 presentation, nor establish that presentation's equivalence.
  No Equivalence rule, model premise or general λ-congruence is used.
\<close>

theorem paper_R_named_H_iff_top:
  assumes rich: "paper_R_rich G" and theorem_H: "paper_R_named_H \<Sigma> G P"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G P (paper_R_named_top G))"
proof -
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule paper_R_named_H_language[OF theorem_H])
  have tl: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPImp (SPAtom 1) (SPIff (SPAtom 0) (SPAtom 1))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G
    (named_paper_imp G P (named_paper_imp G (paper_R_named_top G) (named_paper_iff G P (paper_R_named_top G))))"
    using paper_R_named_H_binary_PC[OF rich pl tl tautology] by simp
  show ?thesis by (rule paper_R_named_H_MP2[OF rich theorem_H paper_R_named_H_top[OF rich] schema
    paper_R_named_paper_iff_language[OF rich pl tl]])
qed

theorem paper_R_classicism_A2_H:
  assumes rich: "paper_R_rich G" and theorem_H: "paper_R_named_H \<Sigma> G P"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns P) (named_lam_vec ns (paper_R_named_top G)))"
  by (rule paper_R_classicism_proves.Logical_Equivalence[
    OF paper_R_named_H_iff_top[OF rich theorem_H] paper_R_named_H_language[OF theorem_H]
      paper_R_named_top_language[OF rich] binders])

end
