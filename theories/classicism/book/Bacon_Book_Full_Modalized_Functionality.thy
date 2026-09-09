theory Bacon_Book_Full_Modalized_Functionality
  imports Bacon_Book_Classicism_Propositional_Equivalence
begin

section \<open>Bacon §8.1: Modalized Functionality throughout F\<close>

definition book_MF_left where
  "book_MF_left G \<sigma> \<tau> = named_chart_fresh G [] (Arr \<sigma> \<tau>)"
definition book_MF_right where
  "book_MF_right G \<sigma> \<tau> = named_chart_fresh G [book_MF_left G \<sigma> \<tau>] (Arr \<sigma> \<tau>)"
definition book_MF_argument where
  "book_MF_argument G \<sigma> \<tau> = named_chart_fresh G [book_MF_left G \<sigma> \<tau>, book_MF_right G \<sigma> \<tau>] \<sigma>"

definition book_MF_body where
  "book_MF_body G \<sigma> \<tau> =
    book_imp (book_box G (book_all G (book_MF_argument G \<sigma> \<tau>)
      (book_leibniz G \<tau>
        (NApp (NVar (book_MF_left G \<sigma> \<tau>)) (NVar (book_MF_argument G \<sigma> \<tau>)))
        (NApp (NVar (book_MF_right G \<sigma> \<tau>)) (NVar (book_MF_argument G \<sigma> \<tau>))))))
      (book_leibniz G (Arr \<sigma> \<tau>) (NVar (book_MF_left G \<sigma> \<tau>)) (NVar (book_MF_right G \<sigma> \<tau>)))"

definition book_MF_axiom where
  "book_MF_axiom G \<sigma> \<tau> = book_all G (book_MF_left G \<sigma> \<tau>)
    (book_all G (book_MF_right G \<sigma> \<tau>) (book_MF_body G \<sigma> \<tau>))"

lemma book_MF_names_type:
  assumes rich: "sg_rich G"
  shows "G (book_MF_left G \<sigma> \<tau>) = Arr \<sigma> \<tau>"
    and "G (book_MF_right G \<sigma> \<tau>) = Arr \<sigma> \<tau>"
    and "G (book_MF_argument G \<sigma> \<tau>) = \<sigma>"
  unfolding book_MF_left_def book_MF_right_def book_MF_argument_def
  by (rule named_chart_fresh_type[OF rich])+

lemma book_MF_names_distinct:
  assumes rich: "sg_rich G"
  shows "distinct [book_MF_left G \<sigma> \<tau>, book_MF_right G \<sigma> \<tau>, book_MF_argument G \<sigma> \<tau>]"
  using named_chart_fresh_notin[where ns="[book_MF_left G \<sigma> \<tau>]" and \<sigma>="Arr \<sigma> \<tau>", OF rich]
    named_chart_fresh_notin[where ns="[book_MF_left G \<sigma> \<tau>, book_MF_right G \<sigma> \<tau>]" and \<sigma>=\<sigma>, OF rich]
  unfolding book_MF_right_def[symmetric] book_MF_argument_def[symmetric] by auto

lemma book_MF_body_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula \<Sigma> G (book_MF_body G \<sigma> \<tau>)"
proof -
  let ?x = "book_MF_left G \<sigma> \<tau>"
  let ?y = "book_MF_right G \<sigma> \<tau>"
  let ?z = "book_MF_argument G \<sigma> \<tau>"
  have xl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?x) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule book_MF_names_type(1)[OF rich, symmetric])
  have yl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?y) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule book_MF_names_type(2)[OF rich, symmetric])
  have zl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?z) \<sigma>"
    by (simp only: book_language_var_iff; rule book_MF_names_type(3)[OF rich, symmetric])
  show ?thesis unfolding book_MF_body_def
    by (rule book_imp_language[OF book_box_language[OF rich book_all_language[
      OF book_leibniz_language[OF rich book_language_App[OF xl zl] book_language_App[OF yl zl]]]]
      book_leibniz_language[OF rich xl yl]])
qed

theorem book_MF_axiom_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula \<Sigma> G (book_MF_axiom G \<sigma> \<tau>)"
  unfolding book_MF_axiom_def by (rule book_all_language, rule book_all_language, rule book_MF_body_language[OF rich])

theorem book_MF_axiom_closed:
  "named_fv (book_MF_axiom G \<sigma> \<tau>) = {}"
  unfolding book_MF_axiom_def book_MF_body_def
  by (auto simp: book_all_fv book_box_fv book_imp_fv book_leibniz_fv)

text \<open>
  MFστ is literally ∀X:σ→τ.∀Y:σ→τ.(□∀z:σ.(Xz=τYz) → X=σ→τY).
  The three typed binders are chosen distinctly from the rich stock.
  Both σ and τ range over F, including function types ending in e.
  Source: p.159 for the formula, p.160 for its inclusion at all F types,
  and endnote 5 on p.178 for the full-type presentation. This file proves
  syntax/closedness only; MF is not asserted to follow from the older
  Equivalence-rule base or to hold in an arbitrary H model.
\<close>

end
