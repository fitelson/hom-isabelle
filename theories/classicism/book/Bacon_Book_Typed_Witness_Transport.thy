theory Bacon_Book_Typed_Witness_Transport
  imports Bacon_Book_Typed_Name_Inverse Bacon_Book_Classicism_Henkin_Extension
begin

section \<open>Literal witness formulas and universal closures under name maps\<close>

lemma book_typed_name_map_exists_const:
  "book_typed_name_map \<rho> (book_exists_const G \<sigma>) = book_exists_const G \<sigma>"
  by (simp only: book_exists_const_def book_typed_name_map.simps book_typed_name_map_not)

lemma book_typed_name_map_witness_axiom:
  "book_typed_name_map \<rho> (book_witness_axiom G \<sigma> F c) =
    book_witness_axiom G \<sigma> (book_typed_name_map \<rho> F) (\<rho> \<sigma> c)"
  by (simp only: book_witness_axiom_def book_typed_name_map_imp
    book_typed_name_map.simps book_typed_name_map_exists_const)

lemma book_typed_name_map_all_list:
  "book_typed_name_map \<rho> (book_all_list G ns A) =
    book_all_list G ns (book_typed_name_map \<rho> A)"
  by (induction ns) (simp_all only: book_all_list.simps book_typed_name_map_all)

lemma book_typed_name_map_universal_closure:
  "book_typed_name_map \<rho> (book_universal_closure G A) =
    book_universal_closure G (book_typed_name_map \<rho> A)"
  by (simp only: book_universal_closure_def book_typed_name_map_all_list book_typed_name_map_fv)

lemma book_typed_name_map_fixes_original:
  assumes names: "named_in_signature \<Sigma> A"
    and fixed_names: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> (BookOriginal c) = c"
  shows "book_typed_name_map \<rho> (book_constant_rename BookOriginal A) = A"
  using book_typed_name_map_roundtrip[where \<rho>="\<lambda>_. BookOriginal" and \<pi>=\<rho> and \<Sigma>=\<Sigma>,
    OF names fixed_names] by (simp only: book_typed_name_map_uniform)

text \<open>
  The conditional witness (∃x:σ. F x) → F c is transported as an
  actual term, not replaced by a semantically equivalent formula.
  Since variables and binders are unchanged, universal closure commutes
  with the map. Fixing the old declared constants therefore fixes every
  old-language formula, including formulas with free variables.
\<close>

end
