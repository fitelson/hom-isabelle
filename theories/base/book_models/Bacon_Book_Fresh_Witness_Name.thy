theory Bacon_Book_Fresh_Witness_Name
  imports Bacon_Book_Constant_Renaming_Reflection Bacon_Book_Closed_Witness_Choice
begin

section \<open>A fresh witness name for every original signature\<close>

text \<open>
  Embed old names as Inl(c) and take the new name w=Inr(⋆).
  In the signature Inl[Σ][w:σ], at least one of S′∪{F′w} and
  S′∪{¬∃σF′} is consistent, where S′=Inl[S] and F′=Inl(F).
  Source role: the fresh-name premise of Bacon, Proposition 15.4, p.319.

  Representation. The new carrier is 'c + unit. Its right-hand name is
  outside the exact old image at every type, even if Σ already uses every
  element of 'c. The proof first transports consistency to the exact image
  signature, then invokes the closed-predicate witness-choice theorem.
  S may be infinite and contain open formulas; only F must be closed.
  No cardinality bound, old unused-name premise, complete Henkin theory,
  model, or reflection from an arbitrary larger signature is assumed.
\<close>

definition book_fresh_witness_signature ::
  "'c ssignature \<Rightarrow> otype \<Rightarrow> ('c + unit) ssignature" where
  "book_fresh_witness_signature \<Sigma> \<sigma> =
    book_add_constant (\<lambda>\<tau>. image Inl (\<Sigma> \<tau>)) (Inr ()) \<sigma>"

lemma book_fresh_witness_signature_old:
  fixes \<Sigma> :: "'c ssignature"
  assumes member: "c \<in> \<Sigma> \<tau>"
  shows "Inl c \<in> book_fresh_witness_signature \<Sigma> \<sigma> \<tau>"
proof -
  have old_member: "Inl c \<in> image (Inl :: 'c \<Rightarrow> 'c + unit) (\<Sigma> \<tau>)"
    by (rule imageI[OF member])
  show ?thesis using old_member
    by (auto simp: book_fresh_witness_signature_def book_add_constant_def)
qed

lemma book_fresh_witness_signature_new:
  "Inr () \<in> book_fresh_witness_signature \<Sigma> \<sigma> \<sigma>"
  unfolding book_fresh_witness_signature_def by (rule book_add_constant_member)

theorem book_theory_fresh_witness_name_choice:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and consistent: "book_theory_consistent \<Sigma> G S"
    and premise_names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "book_theory_consistent (book_fresh_witness_signature \<Sigma> \<sigma>) G
      (insert (NApp (book_constant_rename Inl F) (NConst (Inr ()) \<sigma>))
        (image (book_constant_rename Inl) S)) \<or>
    book_theory_consistent (book_fresh_witness_signature \<Sigma> \<sigma>) G
      (insert (book_not G (NApp (book_exists_const G \<sigma>) (book_constant_rename Inl F)))
        (image (book_constant_rename Inl) S))"
proof -
  let ?f = "Inl :: 'c \<Rightarrow> 'c + unit"
  let ?old = "\<lambda>\<tau>. image ?f (\<Sigma> \<tau>)"
  let ?S = "image (book_constant_rename ?f) S"
  let ?F = "book_constant_rename ?f F"
  have image_consistent: "book_theory_consistent ?old G ?S"
    by (rule iffD1[OF book_theory_consistent_Inl_rename_iff consistent])
  have image_names: "named_in_signature ?old A" if "A \<in> ?S" for A
  proof -
    have in_image: "A \<in> ?S" by (rule that)
    obtain B where member: "B \<in> S" and renamed: "A = book_constant_rename ?f B"
      using in_image by blast
    have old_names: "named_in_signature \<Sigma> B" by (rule premise_names[OF member])
    have mapped_names: "named_in_signature ?old (book_constant_rename ?f B)"
      by (rule book_constant_rename_signature[OF old_names]; rule imageI; assumption)
    show "named_in_signature ?old A" by (simp only: renamed; rule mapped_names)
  qed
  have image_predicate: "book_in_language book_minimal_logical_type UNIV ?old G ?F (Arr \<sigma> Prop)"
    by (rule book_constant_rename_image_language[OF predicate])
  have image_closed: "named_fv ?F = {}" by (simp only: book_constant_rename_fv closed)
  have fresh: "Inr () \<notin> ?old \<sigma>" by (rule book_Inr_fresh_image_signature)
  show ?thesis unfolding book_fresh_witness_signature_def
    by (rule book_theory_closed_witness_choice[OF rich image_consistent image_names
      image_predicate image_closed fresh])
qed

end
