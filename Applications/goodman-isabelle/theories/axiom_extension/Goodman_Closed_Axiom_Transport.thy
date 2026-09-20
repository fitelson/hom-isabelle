theory Goodman_Closed_Axiom_Transport
  imports Goodman_Book_Vector_Extension
begin

section \<open>A closed old term keeps its meaning when the slot chart grows\<close>

lemma gi_old_rename_identity:
  "rename id A = A"
proof -
  have lifted: "lift_ren (\<lambda>n. n) = (\<lambda>n. n)" by (rule ext, rename_tac n, case_tac n) simp_all
  have identity: "rename (\<lambda>n. n) A = A" by (induction A) (simp_all only: rename.simps lifted)
  show ?thesis using identity by (simp only: id_def)
qed

lemma gi_old_closed_weaken:
  assumes typed: "[] \<turnstile> A : \<tau>"
  shows "\<Gamma> \<turnstile> A : \<tau>"
proof -
  have renamed: "\<Gamma> \<turnstile> rename id A : \<tau>"
    by (rule renaming_preserves_typing[OF typed]; simp add: lookup_def)
  show ?thesis using renamed by (simp only: gi_old_rename_identity)
qed

lemma gi_closed_expansion:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> A : \<tau>"
  shows "sfv (gi_expand G k A) = {}"
proof -
  have encoded: "named_to_source G [] (gi_to_book G [] k A) = gi_expand G k A"
    by (rule gi_to_book_relative_encoding[OF rich typed]; simp)
  have closed: "named_fv (gi_to_book G [] k A) = {}" by (rule gi_closed_translation[OF rich typed])
  show ?thesis using named_to_source_closed[OF closed, where G=G] by (simp only: encoded)
qed

theorem gi_closed_chart_alpha:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> A : \<tau>" and distinct: "distinct ns"
  shows "named_alpha G (gi_to_book G ns k A) (gi_to_book G [] k A)"
proof -
  have typed_ns: "map G ns \<turnstile> A : \<tau>" by (rule gi_old_closed_weaken[OF typed])
  have at_ns: "named_to_source G [] (gi_to_book G ns k A) =
    srename (\<lambda>i. ns ! i) (gi_expand G k A)"
    by (rule gi_to_book_empty_encoding[OF rich typed_ns refl distinct])
  have at_empty: "named_to_source G [] (gi_to_book G [] k A) = gi_expand G k A"
    by (rule gi_to_book_relative_encoding[OF rich typed]; simp)
  have unchanged: "srename (\<lambda>i. ns ! i) (gi_expand G k A) = gi_expand G k A"
    by (rule srename_closed[OF gi_closed_expansion[OF rich typed]])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich]; simp only: at_ns unchanged at_empty)
qed

section \<open>Use one fixed image of the closed axiom stock in every context\<close>

theorem gi_goodman_closed_axiom:
  assumes rich: "sg_rich G" and member: "A \<in> T" and typed: "[] \<turnstile> A : Prop"
    and distinct: "distinct ns" and constants: "gi_constants_admitted k \<Sigma> A"
  shows "goodman_book_proves \<Sigma> G (image (gi_to_book G [] k) T) (gi_to_book G ns k A)"
proof -
  have member': "gi_to_book G [] k A \<in> image (gi_to_book G [] k) T" by (rule imageI[OF member])
  have language: "book_theory_formula \<Sigma> G (gi_to_book G [] k A)"
    by (rule gi_to_book_language[OF rich typed _ constants]; simp)
  have canonical: "goodman_book_proves \<Sigma> G (image (gi_to_book G [] k) T) (gi_to_book G [] k A)"
    by (rule goodman_book_proves.Axiom[OF member' language])
  have alpha: "named_alpha G (gi_to_book G [] k A) (gi_to_book G ns k A)"
    by (rule named_alpha.Sym, rule gi_closed_chart_alpha[OF rich typed distinct])
  have conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop
    (gi_to_book G [] k A) (gi_to_book G ns k A)"
    by (rule named_alpha_implies_beta_eta[OF alpha book_language_named[OF language]])
  show ?thesis by (rule gi_goodman_conversion_transport[OF rich conversion canonical])
qed

text \<open>
  The target stock is the fixed empty-chart image of T. It is not enlarged
  by silently adding a different translation for every proof context.
  This proves the closed-axiom constructor obligation only; it does not
  identify the image stock with the independently written Goodman packages.
\<close>

end
