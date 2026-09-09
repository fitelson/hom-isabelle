theory Bacon_Source_Relational_Intensionality_Certificates
  imports Bacon_Source_Relational_Universal_Closure_Syntax
    Bacon_Source_Relational_Distribution_PC
begin

section \<open>The global H certificates for abstraction-form Intensionality\<close>

theorem paper_R_named_H_intensionality_guards:
  assumes rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_iff G
      (named_paper_and P (paper_R_all_vec G ns (named_paper_iff G P Q)))
      (named_paper_and Q (paper_R_all_vec G ns (named_paper_iff G P Q))))"
proof -
  let ?R = "paper_R_all_vec G ns (named_paper_iff G P Q)"
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G P Q) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich pl ql])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_all_vec_language[OF il binders])
  have instance_H: "paper_R_named_H \<Sigma> G (named_paper_imp G ?R (named_paper_iff G P Q))"
    by (rule paper_R_named_H_all_vec_instance[OF rich il binders])
  have tautology: "sprop_tautology
    (SPImp (SPImp (SPAtom (2::nat)) (SPIff (SPAtom 0) (SPAtom 1)))
      (SPIff (SPAnd (SPAtom 0) (SPAtom 2)) (SPAnd (SPAtom 1) (SPAtom 2))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G
      (named_paper_imp G (named_paper_imp G ?R (named_paper_iff G P Q))
        (named_paper_iff G (named_paper_and P ?R) (named_paper_and Q ?R)))"
    using paper_R_named_H_ternary_PC[OF rich pl ql rl tautology] by simp
  have result_language: "paper_R_in_language \<Sigma> G
      (named_paper_iff G (named_paper_and P ?R) (named_paper_and Q ?R)) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich
      paper_R_named_and_language[OF pl rl] paper_R_named_and_language[OF ql rl]])
  show ?thesis by (rule paper_R_named_H.MP[OF instance_H schema result_language])
qed

lemma paper_R_named_H_intensionality_true_guard:
  assumes rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and rl: "paper_R_in_language \<Sigma> G R Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_iff G (named_paper_and P (named_paper_or R (named_paper_not R))) P)"
proof -
  have tautology: "sprop_tautology
    (SPIff (SPAnd (SPAtom (0::nat)) (SPOr (SPAtom 1) (SPNot (SPAtom 1)))) (SPAtom 0))"
    by (auto simp: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich pl rl tautology] by simp
qed

text \<open>
  These certificates are H theorems before introducing a Box
  assumption. The guard R is literally ∀n⃗.(P↔Q), and its
  excluded middle is R∨¬R, exactly the expression in Box's
  λ definition. Native PC and universal instantiation suffice;
  no C rule, local ζ, model or semantic tautology is invoked.
  Source: the two outer steps of the Intensionality argument, p.17.
\<close>

end
