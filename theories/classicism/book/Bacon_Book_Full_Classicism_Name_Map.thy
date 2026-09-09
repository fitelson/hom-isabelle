theory Bacon_Book_Full_Classicism_Name_Map
  imports Bacon_Book_Full_Classicism_Structural Bacon_Book_C_Typed_Name_Map
begin

section \<open>Typed name transport preserves every full-C constructor\<close>

lemma book_full_typed_name_map_box_const:
  "book_typed_name_map \<rho> (book_box_const G) = book_box_const G"
  by (simp only: book_box_const_def book_typed_name_map.simps book_C_typed_rename_leibniz
    book_top_def book_typed_name_map_not book_typed_name_map_bottom)

lemma book_full_typed_name_map_box:
  "book_typed_name_map \<rho> (book_box G A) = book_box G (book_typed_name_map \<rho> A)"
  by (simp only: book_box_def book_typed_name_map.simps book_full_typed_name_map_box_const)

lemma book_MF_typed_name_map:
  "book_typed_name_map \<rho> (book_MF_axiom G \<sigma> \<tau>) = book_MF_axiom G \<sigma> \<tau>"
  by (simp only: book_MF_axiom_def book_MF_body_def book_typed_name_map_all book_typed_name_map_imp
    book_full_typed_name_map_box book_C_typed_rename_leibniz book_typed_name_map.simps)

theorem book_full_C_typed_name_map:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "book_full_C_proves \<Omega> G (book_typed_name_map \<rho> A)"
  using derivation
proof (induction rule: book_full_C_proves.induct)
  case (H A)
  have base: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
  have mapped: "book_theory_derivable \<Omega> G {} (book_typed_name_map \<rho> A)"
    using book_theory_typed_name_map[OF base maps] by (simp only: image_empty)
  show ?case by (rule book_full_C_from_empty_theory[OF rich mapped])
next
  case MF
  show ?case by (simp only: book_MF_typed_name_map; rule book_full_C_proves.MF)
next
  case (MP A B)
  have conditional: "book_full_C_proves \<Omega> G (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using MP.IH(2) by (simp only: book_typed_name_map_imp)
  show ?case by (rule book_full_C_proves.MP[OF MP.IH(1) conditional book_typed_name_map_language[OF MP.hyps(3) maps]])
next
  case (Gen A B n)
  have conditional: "book_full_C_proves \<Omega> G (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using Gen.IH by (simp only: book_typed_name_map_imp)
  have fresh: "n \<notin> named_fv (book_typed_name_map \<rho> A)"
    by (simp only: book_typed_name_map_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_typed_name_map_imp book_typed_name_map_all;
    rule book_full_C_proves.Gen[OF conditional book_typed_name_map_language[OF Gen.hyps(2) maps]
      book_typed_name_map_language[OF Gen.hyps(3) maps] fresh])
next
  case (PE P Q)
  have premise: "book_full_C_proves \<Omega> G (book_iff G (book_typed_name_map \<rho> P) (book_typed_name_map \<rho> Q))"
    using PE.IH by (simp only: book_C_typed_rename_iff)
  show ?case by (simp only: book_C_typed_rename_leibniz;
    rule book_full_C_proves.PE[OF premise book_typed_name_map_language[OF PE.hyps(2) maps]
      book_typed_name_map_language[OF PE.hyps(3) maps]])
qed

text \<open>
  Every source full-C proof is preserved by a type-indexed constant
  map respecting the declared signatures. The MF case is checked
  explicitly: the logical axiom contains no nonlogical constants and
  the map fixes its syntax, including all binders and defined operators.
  No injectivity is needed in this forward theorem. Reflection and
  consistency transport require their own inverse hypotheses.
\<close>

end
