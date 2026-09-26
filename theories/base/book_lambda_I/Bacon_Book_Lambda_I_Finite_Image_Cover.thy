theory Bacon_Book_Lambda_I_Finite_Image_Cover
  imports Bacon_Book_Lambda_I_Theory_Signature_Conservativity Bacon_Book_Lambda_I_Theory_Consistency
begin

section \<open>A finite part of a family uses finitely many indices\<close>

text \<open>
  If B is finite and B ⊆ S∪f[K], there is a finite I⊆K with
  B⊆S∪f[I]. The proof chooses a preimage only when the newly added
  element of B is outside S. Neither K nor S need be countable or
  finite, and f need not be injective. There is no global inverse or
  enumeration. Source role: finite-proof support in the witness
  construction of Bacon, Proposition 15.4, p.319.
\<close>

lemma book_lambda_I_finite_image_cover:
  assumes finite: "finite B" and cover: "B \<subseteq> S \<union> image f K"
  shows "\<exists>I. finite I \<and> I \<subseteq> K \<and> B \<subseteq> S \<union> image f I"
  using finite cover
proof (induction rule: finite_induct)
  case empty
  show ?case by (rule exI[where x="{}"]; simp)
next
  case (insert b B)
  have body_cover: "B \<subseteq> S \<union> image f K" using insert.prems by blast
  obtain I where finite_I: "finite I" and subset_I: "I \<subseteq> K"
    and cover_I: "B \<subseteq> S \<union> image f I"
    using insert.IH[OF body_cover] by blast
  show ?case
  proof (cases "b \<in> S")
    case True
    have covered: "insert b B \<subseteq> S \<union> image f I" using True cover_I by blast
    show ?thesis by (rule exI[where x=I]; rule conjI[OF finite_I conjI[OF subset_I covered]])
  next
    case False
    have in_image: "b \<in> image f K" using insert.prems False by blast
    obtain k where member: "k \<in> K" and represented: "b = f k"
      using in_image by blast
    have finite_more: "finite (insert k I)" using finite_I by simp
    have subset_more: "insert k I \<subseteq> K" using member subset_I by blast
    have image_more: "image f I \<subseteq> image f (insert k I)" by (rule image_mono[OF subset_insertI])
    have covered: "insert b B \<subseteq> S \<union> image f (insert k I)"
      using cover_I image_more represented by blast
    show ?thesis by (rule exI[where x="insert k I"];
      rule conjI[OF finite_more conjI[OF subset_more covered]])
  qed
qed

section \<open>Transporting nonderivability of falsity between signatures\<close>

text \<open>
  If S is consistent in Σ and all its nonlogical names belong to Σ,
  it remains consistent in each signature Ω on the same name carrier.
  A proposed Ω-proof of ⊥ retracts to Σ: ⊥ contains no nonlogical
  constants, and the premise names are already in Σ.

  No inclusion hypothesis is needed for this syntactic statement. When
  Ω does not include Σ, some raw premises may fail to belong to Ω;
  the conclusion still says precisely that the existing Ω-judgment
  derives no ⊥. To regard all premises as formulas of an enlarged
  language, separately supply their typing and Σ⊆Ω. This lemma makes
  no model or family-consistency claim by itself.
\<close>

theorem book_lambda_I_consistent_signature_transport:
  assumes rich: "sg_rich G"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
    and names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
  shows "book_lambda_I_consistent \<Omega> G S"
proof (unfold book_lambda_I_consistent_def, rule notI)
  assume contradiction: "book_lambda_I_derivable \<Omega> G S (book_bottom G)"
  have bottom_names: "named_in_signature \<Sigma> (book_bottom G)"
    by (simp add: book_bottom_def)
  have original: "book_lambda_I_derivable \<Sigma> G S (book_bottom G)"
    by (rule book_lambda_I_foreign_constants_eliminate[OF rich contradiction bottom_names names])
  show False using consistent original unfolding book_lambda_I_consistent_def by blast
qed

end
