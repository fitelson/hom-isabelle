theory Bacon_Book_BBK_Model
  imports Bacon_Book_BBK_Environment Bacon_Book_BBK_Logical_Values
    Bacon_Book_BBK_Implication_Truth Bacon_Book_BBK_Universal_Truth
    Bacon_Book_BBK_False_Value Bacon_Book_Full_Minimal_Model
begin

section \<open>A BBK model supplies the full minimal book model\<close>

text \<open>
  Keep the original domains and valuation. Interpret the book's named
  terms through the minimal-basis translation, use variable applications
  for typed App, and take the closed logical wrappers as κ values.
  Every field of the full minimal book model is then satisfied.

  Source role: an explicit bridge from the represented Bacon–Dorr BBK
  models to the full-language minimal-basis case of Bacon's Definition
  15.1, pp.314–315. The intersection environment clause, logical truth
  clauses, and an actual false proposition are proved, not added as
  premises. A total typed assignment witnesses the closed logical values.

  The input is a BBK model and a rich named-variable stock. No book-model
  existence or book completeness theorem, Functionality, restriction to
  closed denotations, alternative carrier, or PER domain is used.
  The converse model bridge and arbitrary general-language scope are not
  asserted here.
\<close>

context pbbk_model
begin

theorem pbbk_to_book_full_minimal_model:
  assumes rich: "sg_rich G"
  shows "book_full_minimal_model domain pbbk_book_app signature G
    (pbbk_book_denote G) valuation pbbk_book_logical_value"
proof -
  interpret Book: book_full_environment domain pbbk_book_app book_minimal_logical_type UNIV
    signature G "pbbk_book_denote G"
    by (rule pbbk_book_full_environment[OF rich])
  obtain g0 where typed: "book_env_typed domain G g0"
    using pbbk_book_assignment_exists[where G=G] by (elim exE)
  have logicals: "Book.book_closed_value (book_minimal_logical_type l) (NLogical l)
    (pbbk_book_logical_value l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV signature G
      (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have logical_value: "pbbk_book_denote G g0 (NLogical l) = pbbk_book_logical_value l"
      by (simp only: pbbk_book_denote_def book_named_translation_Logical pbbk_book_logical_value_at)
    have witness: "Book.book_closed_value (book_minimal_logical_type l) (NLogical l)
      (pbbk_book_denote G g0 (NLogical l))"
      by (rule Book.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using witness by (simp only: logical_value)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def, rule conjI[OF Book.book_full_environment_axioms], unfold_locales)
    fix l
    show "Book.book_closed_value (book_minimal_logical_type l) (NLogical l) (pbbk_book_logical_value l)"
      by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> domain Prop" and qm: "q \<in> domain Prop"
    show "valuation (pbbk_book_app Prop Prop (pbbk_book_app Prop (Arr Prop Prop)
      (pbbk_book_logical_value SImp) p) q) = (valuation p \<longrightarrow> valuation q)"
      by (rule pbbk_book_implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> domain (Arr \<sigma> Prop)"
    show "valuation (pbbk_book_app (Arr \<sigma> Prop) Prop (pbbk_book_logical_value (SBAll \<sigma>)) f) =
      (\<forall>a \<in> domain \<sigma>. valuation (pbbk_book_app \<sigma> Prop f a))"
      by (rule pbbk_book_forall_truth[OF fm])
  next
    show "\<exists>f \<in> domain Prop. \<not> valuation f" by (rule pbbk_book_false_value)
  qed
qed

end

end
