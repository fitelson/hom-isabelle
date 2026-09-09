theory Bacon_Source_Named_Logical_Encoding
  imports Bacon_Source_Named_Logical_Syntax
begin

section \<open>Literal encoding of the named logical basis\<close>

text \<open>
  Encoding → and ↔ gives exactly the closed λ operators in Figure 1,
  and encoding their applications gives the corresponding literal source
  applications. Source: Bacon–Dorr Figure 1, p.6, and §1.1, pp.5–6.

  Isabelle representation. The equations hold under every surrounding
  binder stack ns. The two chosen propositional names are bound inside
  each closed operator, so their nearest slots are 1 and 0 regardless of
  ns. The argument terms stay outside those internal binders. No β step,
  direct Boolean expansion, substitution, theoremhood, or semantic claim
  is used in these equalities.
\<close>

lemma named_paper_not_encoding:
  "named_to_source G ns (named_paper_not A) = paper_not (named_to_source G ns A)"
  by (simp only: named_paper_not_def paper_not_def named_to_source.simps)

lemma named_paper_and_encoding:
  "named_to_source G ns (named_paper_and A B) = paper_and (named_to_source G ns A) (named_to_source G ns B)"
  by (simp only: named_paper_and_def paper_and_def named_to_source.simps)

lemma named_paper_or_encoding:
  "named_to_source G ns (named_paper_or A B) = paper_or (named_to_source G ns A) (named_to_source G ns B)"
  by (simp only: named_paper_or_def paper_or_def named_to_source.simps)

lemma named_paper_eq_encoding:
  "named_to_source G ns (named_paper_eq \<sigma> A B) =
    SApp (SApp (SLogical (SEq \<sigma>)) (named_to_source G ns A)) (named_to_source G ns B)"
  by (simp only: named_paper_eq_def named_to_source.simps)

lemma named_paper_all_encoding:
  "named_to_source G ns (named_paper_all \<sigma> F) = SApp (SLogical (SAll \<sigma>)) (named_to_source G ns F)"
  by (simp only: named_paper_all_def named_to_source.simps)

lemma named_paper_ex_encoding:
  "named_to_source G ns (named_paper_ex \<sigma> F) = SApp (SLogical (SEx \<sigma>)) (named_to_source G ns F)"
  by (simp only: named_paper_ex_def named_to_source.simps)

lemma named_paper_imp_const_encoding:
  assumes rich: "sg_rich G"
  shows "named_to_source G ns (named_paper_imp_const G) = paper_imp_const"
  by (simp add: named_paper_imp_const_def named_paper_not_def named_paper_or_def
    paper_imp_const_def paper_not_def paper_or_def named_paper_p_type[OF rich]
    named_paper_q_type[OF rich] named_paper_names_distinct[OF rich])

lemma named_paper_iff_const_encoding:
  assumes rich: "sg_rich G"
  shows "named_to_source G ns (named_paper_iff_const G) = paper_iff_const"
  by (simp add: named_paper_iff_const_def named_paper_not_def named_paper_or_def named_paper_and_def
    paper_iff_const_def paper_not_def paper_or_def paper_and_def named_paper_p_type[OF rich]
    named_paper_q_type[OF rich] named_paper_names_distinct[OF rich])

lemma named_paper_imp_encoding:
  assumes rich: "sg_rich G"
  shows "named_to_source G ns (named_paper_imp G A B) = paper_imp (named_to_source G ns A) (named_to_source G ns B)"
  by (simp only: named_paper_imp_def paper_imp_def named_to_source.simps named_paper_imp_const_encoding[OF rich])

lemma named_paper_iff_encoding:
  assumes rich: "sg_rich G"
  shows "named_to_source G ns (named_paper_iff G A B) = paper_iff (named_to_source G ns A) (named_to_source G ns B)"
  by (simp only: named_paper_iff_def paper_iff_def named_to_source.simps named_paper_iff_const_encoding[OF rich])

end
