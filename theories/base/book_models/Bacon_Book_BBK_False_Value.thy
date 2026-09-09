theory Bacon_Book_BBK_False_Value
  imports Bacon_Book_Total_Assignments
    Bacon_Parametric_Signature_Development.Bacon_Parametric_BBK_Semantics
begin

section \<open>Actual assignments and a false proposition supplied by a BBK model\<close>

text \<open>
  BBK domains are nonempty at every type. They therefore supply a total
  typed assignment in the book's sense, for every fixed variable stock.
  Independently, a propositional value assigned to one variable lets us
  interpret p∧¬p and obtain an actual false member of Dt.

  Source role: discharge assignment availability and the false-proposition
  requirement of Bacon's Definition 15.1, pp.314–315, in the BBK-to-book
  construction. This does not assert those conditions for a raw book
  applicative structure. The BBK model is an explicit input; no book
  model, book completeness, or Functionality is assumed.
\<close>

context pbbk_model
begin

theorem pbbk_book_assignment_exists:
  "\<exists>g. book_env_typed domain G g"
  by (rule book_total_assignment_exists, rule domain_nonempty)

theorem pbbk_book_false_value:
  "\<exists>p \<in> domain Prop. \<not> valuation p"
proof -
  obtain a where member: "a \<in> domain Prop" using domain_nonempty[where \<sigma>=Prop] by blast
  let ?g = "pbbk_extend a (\<lambda>_. undefined)"
  let ?F = "PConj (PVar 0) (PNeg (PVar 0))"
  have typed: "pbbk_env_typed domain [Prop] ?g"
    by (rule pbbk_env_extend[where D=domain and \<sigma>=Prop, OF pbbk_env_empty member])
  have variable: "has_ptype [Prop] (PVar 0) Prop" by (rule has_ptype.PVar) simp
  have negation: "has_ptype [Prop] (PNeg (PVar 0)) Prop" by (rule has_ptype.PNeg[OF variable])
  have formula: "has_ptype [Prop] ?F Prop" by (rule has_ptype.PConj[OF variable negation])
  have variable_signature: "pterm_in_signature signature (PVar 0)" by simp
  have negation_signature: "pterm_in_signature signature (PNeg (PVar 0))" by simp
  have formula_signature: "pterm_in_signature signature ?F" by simp
  have result_type: "denote ?g ?F \<in> domain Prop"
    by (rule denote_type[OF formula formula_signature typed])
  have negated: "valuation (denote ?g (PNeg (PVar 0))) = (\<not> valuation (denote ?g (PVar 0)))"
    by (rule valuation_neg[OF variable variable_signature typed])
  have conjunctive: "valuation (denote ?g ?F) =
    (valuation (denote ?g (PVar 0)) \<and> valuation (denote ?g (PNeg (PVar 0))))"
    by (rule valuation_conj[OF variable negation variable_signature negation_signature typed])
  have falsehood: "\<not> valuation (denote ?g ?F)" by (simp only: conjunctive negated; simp)
  show ?thesis by (rule bexI[where x="denote ?g ?F"]; fact)
qed

end

end
