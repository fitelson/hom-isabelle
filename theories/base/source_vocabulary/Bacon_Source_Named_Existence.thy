theory Bacon_Source_Named_Existence
  imports Bacon_Source_Named_H_Correspondence Bacon_Source_Global_Existence
begin

section \<open>All-type Existence is a derived native named H theorem\<close>

text \<open>
  For each variable n of type σ, H proves ∃n(n =σ n).
  Source: the derived Existence schema following Bacon–Dorr Figure 2,
  pp.7–9. The represented types are full F and the named stock is rich.

  Isabelle representation. The formula applies the first-class ∃σ and
  =σ constants and binds n by NLam. Its literal closed encoding is the
  already derived global source Existence theorem. The checked syntactic
  decoding theorem transfers that proof to native named H; no semantic
  nonemptiness, completion premise, or new Existence constructor is used.
\<close>

lemma named_existence_encoding:
  assumes variable: "G n = \<sigma>"
  shows "named_to_source G [] (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n)))) =
    SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0)))"
  by (simp add: named_paper_ex_def named_paper_eq_def variable)

theorem paper_named_type_existence:
  assumes variable: "G n = \<sigma>" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n))))"
proof -
  have source: "paper_global_H \<Sigma> G
    (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0))))"
    by (rule paper_global_type_existence[OF rich])
  have encoded: "paper_global_H \<Sigma> G (named_to_source G []
    (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n)))))"
    by (simp only: named_existence_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF variable]; rule source)
  show ?thesis by (rule paper_named_H_decoding[OF encoded rich])
qed

end
