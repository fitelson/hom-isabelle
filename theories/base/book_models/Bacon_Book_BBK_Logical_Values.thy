theory Bacon_Book_BBK_Logical_Values
  imports Bacon_Book_BBK_Application
    Bacon_Source_Vocabulary_Development.Bacon_Source_Logical_Applications
    Bacon_Source_Vocabulary_Development.Bacon_Source_Conversion
begin

section \<open>Closed logical values from the literal minimal-basis translation\<close>

text \<open>
  Let κ(l) be the BBK denotation of the already defined closed wrapper
  for l. These wrappers have their required types in the empty context
  and contain no nonlogical constants. Hence their denotations belong
  to the required domains and are independent of the assignment.

  The arbitrary assignment used in the definition is typed at the EMPTY
  BBK context. It is not asserted to be a total typed book assignment.
  The later book-model constructor supplies an actual book assignment
  and proves that these same values have the required closed witnesses.
  Source role: the logical denotations in Definition 15.1, pp.314–315.
  No book model, Functionality, or identity between the book's primitive
  implication and the paper's material connective is assumed.
\<close>

context pbbk_model
begin

definition pbbk_book_logical_value :: "book_minimal_logical \<Rightarrow> 'v" where
  "pbbk_book_logical_value l = denote (\<lambda>_. undefined) (book_minimal_logical_translation l)"

theorem pbbk_book_logical_value_type:
  "pbbk_book_logical_value l \<in> domain (book_minimal_logical_type l)"
  unfolding pbbk_book_logical_value_def
  by (rule denote_type[where \<Gamma>="[]", OF book_minimal_logical_translation_closed
    book_minimal_logical_translation_signature pbbk_env_empty])

theorem pbbk_book_logical_value_at:
  "denote g (book_minimal_logical_translation l) = pbbk_book_logical_value l"
  unfolding pbbk_book_logical_value_def
proof (rule denote_locality[where \<Gamma>="[]" and \<Delta>="[]",
    OF book_minimal_logical_translation_closed book_minimal_logical_translation_closed
      book_minimal_logical_translation_signature pbbk_env_empty pbbk_env_empty])
  fix n
  assume free: "n \<in> pbbk_fv (book_minimal_logical_translation l)"
  then show "g n = (\<lambda>_. undefined) n" by (simp only: book_minimal_logical_translation_fv) simp
qed

lemma pbbk_book_implication_value_type:
  "pbbk_book_logical_value SImp \<in> domain (Arr Prop (Arr Prop Prop))"
  using pbbk_book_logical_value_type[where l=SImp] by simp

lemma pbbk_book_universal_value_type:
  "pbbk_book_logical_value (SBAll \<sigma>) \<in> domain (Arr (Arr \<sigma> Prop) Prop)"
  using pbbk_book_logical_value_type[where l="SBAll \<sigma>"] by simp

end

end
