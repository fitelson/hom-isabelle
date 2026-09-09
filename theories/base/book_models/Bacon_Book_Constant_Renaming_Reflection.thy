theory Bacon_Book_Constant_Renaming_Reflection
  imports Bacon_Book_Theory_Constant_Renaming Bacon_Book_Theory_Consistency
begin

section \<open>Injective renaming into the exact image signature\<close>

text \<open>
  For injective f, S ⊢Σ A iff f[S] ⊢f[Σ] f(A). Applying the
  left inverse of f to the second derivation restores every raw term
  and premise. Source role: conservative naming of the old language
  inside the enlarged signatures of Bacon, Proposition 15.4, p.319.

  Representation. The target signature is exactly f[Σ], not an arbitrary
  larger signature. No richness, formula guard on A, or language guard
  on all members of S is needed: the syntactic left inverse acts on all
  raw terms, including unused malformed premises. Injectivity is explicit.
  No reflection result is claimed for a noninjective map, and no model
  existence or addition of actual witness axioms is established here.
\<close>

lemma book_constant_rename_inverse:
  assumes injective: "inj f"
  shows "book_constant_rename (inv f) (book_constant_rename f A) = A"
proof -
  have functions_equal: "inv f \<circ> f = id"
    by (rule ext; simp only: comp_apply id_apply inv_f_f[OF injective])
  show ?thesis by (simp only: book_constant_rename_comp functions_equal book_constant_rename_id)
qed

lemma book_constant_rename_inverse_image:
  assumes injective: "inj f"
  shows "image (book_constant_rename (inv f)) (image (book_constant_rename f) S) = S"
  by (simp add: image_image book_constant_rename_inverse[OF injective])

theorem book_theory_constant_rename_iff:
  assumes injective: "inj f"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
      (image (book_constant_rename f) S) (book_constant_rename f A)"
proof
  assume original: "book_theory_derivable \<Sigma> G S A"
  show "book_theory_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
      (image (book_constant_rename f) S) (book_constant_rename f A)"
    by (rule book_theory_constant_rename_image[OF original])
next
  assume renamed: "book_theory_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
      (image (book_constant_rename f) S) (book_constant_rename f A)"
  have inverse_maps: "inv f d \<in> \<Sigma> \<tau>" if "d \<in> image f (\<Sigma> \<tau>)" for \<tau> d
  proof -
    have in_image: "d \<in> image f (\<Sigma> \<tau>)" by (rule that)
    obtain c where member: "c \<in> \<Sigma> \<tau>" and encoded: "d = f c"
      using in_image by blast
    show "inv f d \<in> \<Sigma> \<tau>" by (simp only: encoded inv_f_f[OF injective]; rule member)
  qed
  have restored: "book_theory_derivable \<Sigma> G
      (image (book_constant_rename (inv f)) (image (book_constant_rename f) S))
      (book_constant_rename (inv f) (book_constant_rename f A))"
    by (rule book_theory_constant_rename[OF renamed inverse_maps])
  show "book_theory_derivable \<Sigma> G S A"
    using restored by (simp only: book_constant_rename_inverse_image[OF injective]
      book_constant_rename_inverse[OF injective])
qed

theorem book_theory_consistent_constant_rename_iff:
  assumes injective: "inj f"
  shows "book_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_theory_consistent (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G (image (book_constant_rename f) S)"
proof -
  have equivalence: "book_theory_derivable \<Sigma> G S (book_bottom G) \<longleftrightarrow>
    book_theory_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
      (image (book_constant_rename f) S) (book_constant_rename f (book_bottom G))"
    by (rule book_theory_constant_rename_iff[OF injective])
  show ?thesis unfolding book_theory_consistent_def
    using equivalence by (simp only: book_constant_rename_bottom)
qed

section \<open>A disjoint sum supplies names outside the old signature\<close>

corollary book_theory_Inl_rename_iff:
  fixes \<Sigma> :: "'c ssignature"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable (\<lambda>\<tau>. image (Inl :: 'c \<Rightarrow> 'c + 'd) (\<Sigma> \<tau>)) G
      (image (book_constant_rename Inl) S) (book_constant_rename Inl A)"
  by (rule book_theory_constant_rename_iff; rule inj_Inl)

corollary book_theory_consistent_Inl_rename_iff:
  fixes \<Sigma> :: "'c ssignature"
  shows "book_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_theory_consistent (\<lambda>\<tau>. image (Inl :: 'c \<Rightarrow> 'c + 'd) (\<Sigma> \<tau>)) G
      (image (book_constant_rename Inl) S)"
  by (rule book_theory_consistent_constant_rename_iff; rule inj_Inl)

lemma book_Inr_fresh_image_signature:
  "Inr u \<notin> image (Inl :: 'c \<Rightarrow> 'c + 'd) (\<Sigma> \<tau>)"
  by auto

corollary book_sum_image_has_fresh_name:
  fixes \<Sigma> :: "'c ssignature"
  shows "\<exists>c :: 'c + unit. \<forall>\<tau>. c \<notin> image Inl (\<Sigma> \<tau>)"
  by (rule exI[where x="Inr ()"]; rule allI; rule book_Inr_fresh_image_signature)

end
