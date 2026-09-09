theory Bacon_Book_Typed_Name_Inverse
  imports Bacon_Book_C_Theory_Typed_Name_Map
begin

section \<open>Inversion is required only on declared type components\<close>

definition book_typed_image_signature where
  "book_typed_image_signature \<rho> \<Sigma> \<tau> = \<rho> \<tau> ` \<Sigma> \<tau>"

definition book_typed_name_inverse where
  "book_typed_name_inverse \<rho> \<Sigma> \<tau> = inv_into (\<Sigma> \<tau>) (\<rho> \<tau>)"

lemma book_typed_image_maps:
  "c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> book_typed_image_signature \<rho> \<Sigma> \<tau>"
  unfolding book_typed_image_signature_def by (rule imageI; assumption)

lemma book_typed_inverse_maps:
  "d \<in> book_typed_image_signature \<rho> \<Sigma> \<tau> \<Longrightarrow>
    book_typed_name_inverse \<rho> \<Sigma> \<tau> d \<in> \<Sigma> \<tau>"
  unfolding book_typed_image_signature_def book_typed_name_inverse_def by (rule inv_into_into; assumption)

lemma book_typed_inverse_left:
  assumes injective: "inj_on (\<rho> \<tau>) (\<Sigma> \<tau>)" and member: "c \<in> \<Sigma> \<tau>"
  shows "book_typed_name_inverse \<rho> \<Sigma> \<tau> (\<rho> \<tau> c) = c"
  unfolding book_typed_name_inverse_def by (rule inv_into_f_f[OF injective member])

lemma book_typed_inverse_right:
  assumes member: "d \<in> book_typed_image_signature \<rho> \<Sigma> \<tau>"
  shows "\<rho> \<tau> (book_typed_name_inverse \<rho> \<Sigma> \<tau> d) = d"
  using member unfolding book_typed_image_signature_def book_typed_name_inverse_def by (rule f_inv_into_f)

theorem book_C_theory_typed_image_iff:
  assumes rich: "sg_rich G" and injective: "\<And>\<tau>. inj_on (\<rho> \<tau>) (\<Sigma> \<tau>)"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and names: "named_in_signature \<Sigma> A"
  shows "book_C_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_C_theory_derivable (book_typed_image_signature \<rho> \<Sigma>) G (book_typed_name_map \<rho> ` S) (book_typed_name_map \<rho> A)"
proof
  assume derivation: "book_C_theory_derivable \<Sigma> G S A"
  have maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> book_typed_image_signature \<rho> \<Sigma> \<tau>"
    by (rule book_typed_image_maps)
  show "book_C_theory_derivable (book_typed_image_signature \<rho> \<Sigma>) G (book_typed_name_map \<rho> ` S) (book_typed_name_map \<rho> A)"
    by (rule book_C_theory_typed_name_map[where \<rho>=\<rho> and \<Omega>="book_typed_image_signature \<rho> \<Sigma>",
      OF rich derivation language maps])
next
  let ?\<Omega> = "book_typed_image_signature \<rho> \<Sigma>"
  let ?\<pi> = "book_typed_name_inverse \<rho> \<Sigma>"
  assume derivation: "book_C_theory_derivable ?\<Omega> G (book_typed_name_map \<rho> ` S) (book_typed_name_map \<rho> A)"
  have back_maps: "\<And>\<tau> d. d \<in> ?\<Omega> \<tau> \<Longrightarrow> ?\<pi> \<tau> d \<in> \<Sigma> \<tau>"
    by (rule book_typed_inverse_maps)
  have left: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> ?\<pi> \<tau> (\<rho> \<tau> c) = c"
    by (rule book_typed_inverse_left[where \<rho>=\<rho> and \<Sigma>=\<Sigma>, OF injective]; assumption)
  have mapped_language: "book_theory_formula ?\<Omega> G B" if member: "B \<in> book_typed_name_map \<rho> ` S" for B
  proof -
    obtain P where pm: "P \<in> S" and shape: "B = book_typed_name_map \<rho> P" using member by blast
    show ?thesis by (simp only: shape; rule book_typed_name_map_language[OF language[OF pm]];
      rule book_typed_image_maps; assumption)
  qed
  have restored: "book_C_theory_derivable \<Sigma> G (book_typed_name_map ?\<pi> ` (book_typed_name_map \<rho> ` S))
      (book_typed_name_map ?\<pi> (book_typed_name_map \<rho> A))"
    by (rule book_C_theory_typed_name_map[where \<rho>="?\<pi>", OF rich derivation mapped_language back_maps])
  have original: "book_typed_name_map ?\<pi> (book_typed_name_map \<rho> A) = A"
    by (rule book_typed_name_map_roundtrip[where \<rho>=\<rho> and \<pi>="?\<pi>" and \<Sigma>=\<Sigma>, OF names left])
  have each: "book_typed_name_map ?\<pi> (book_typed_name_map \<rho> B) = B" if "B \<in> S" for B
    by (rule book_typed_name_map_roundtrip[where \<rho>=\<rho> and \<pi>="?\<pi>" and \<Sigma>=\<Sigma>,
      OF book_language_signature[OF language[OF that]] left])
  have premises_back: "book_typed_name_map ?\<pi> ` (book_typed_name_map \<rho> ` S) = S" using each by (auto simp: image_image)
  show "book_C_theory_derivable \<Sigma> G S A" using restored by (simp only: original premises_back)
qed

theorem book_C_consistent_typed_image_iff:
  assumes rich: "sg_rich G" and injective: "\<And>\<tau>. inj_on (\<rho> \<tau>) (\<Sigma> \<tau>)"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_C_theory_consistent (book_typed_image_signature \<rho> \<Sigma>) G (book_typed_name_map \<rho> ` S)"
proof -
  have names: "named_in_signature \<Sigma> (book_bottom G)" by (simp add: book_bottom_def)
  have equivalent: "book_C_theory_derivable \<Sigma> G S (book_bottom G) \<longleftrightarrow>
      book_C_theory_derivable (book_typed_image_signature \<rho> \<Sigma>) G (book_typed_name_map \<rho> ` S)
        (book_typed_name_map \<rho> (book_bottom G))"
    by (rule book_C_theory_typed_image_iff[OF rich injective language names])
  show ?thesis using equivalent by (simp only: book_C_theory_consistent_def book_typed_name_map_bottom)
qed

text \<open>
  Injectivity is typewise and only on Στ. The inverse maps each
  exact image component back to that declared component; it has no
  required behavior elsewhere. Thus the proof does not assume that
  the entire old name carrier embeds into an already occupied one.
  Roundtrips retain the explicit old-language guard on the conclusion.
  This is consistency transport, not a fixed-ambient embedding theorem.
\<close>

end
