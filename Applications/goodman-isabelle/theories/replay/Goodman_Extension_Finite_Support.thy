theory Goodman_Extension_Finite_Support
  imports Goodman_Extension_Retraction
begin

section \<open>Finite support in the actual axiom-extension calculus\<close>

text \<open>
  Write C+[T] ⊢ A for goodman_book_proves Σ G T A. Every such
  derivation uses only finitely many members of T. The induction below
  is on that very derivation: PE and Generalization remain available
  above the selected added axioms. We do not replace this consequence
  relation by ordinary consequence from local assumptions.

  No richness, closedness, or global well-formedness premise on T is
  needed for finite support. Each actual Axiom step already checks the
  language of the axiom that it uses. The finite subset may be empty.
\<close>

theorem goodman_book_finite_support:
  assumes derivation: "goodman_book_proves \<Sigma> G T A"
  shows "\<exists>U. finite U \<and> U \<subseteq> T \<and> goodman_book_proves \<Sigma> G U A"
  using derivation
proof (induction rule: goodman_book_proves.induct)
  case (Axiom A)
  have derivation: "goodman_book_proves \<Sigma> G {A} A"
    by (rule goodman_book_proves.Axiom; simp add: Axiom.hyps(2))
  show ?case
    by (rule exI[where x="{A}"])
      (use Axiom.hyps(1) derivation in auto)
next
  case (Base A)
  have derivation: "goodman_book_proves \<Sigma> G {} A"
    by (rule goodman_book_proves.Base[OF Base.hyps])
  show ?case by (rule exI[where x="{}"]) (simp add: derivation)
next
  case (MP A B)
  obtain U where uf: "finite U" and us: "U \<subseteq> T"
    and ua: "goodman_book_proves \<Sigma> G U A"
    using MP.IH(1) by blast
  obtain V where vf: "finite V" and vs: "V \<subseteq> T"
    and vi: "goodman_book_proves \<Sigma> G V (book_imp A B)"
    using MP.IH(2) by blast
  have a: "goodman_book_proves \<Sigma> G (U \<union> V) A"
    by (rule goodman_book_mono[OF ua Un_upper1])
  have implication: "goodman_book_proves \<Sigma> G (U \<union> V) (book_imp A B)"
    by (rule goodman_book_mono[OF vi Un_upper2])
  have conclusion: "goodman_book_proves \<Sigma> G (U \<union> V) B"
    by (rule goodman_book_proves.MP[OF a implication MP.hyps(3)])
  show ?case
    by (rule exI[where x="U \<union> V"])
      (use uf vf us vs conclusion in auto)
next
  case (Gen A B n)
  obtain U where uf: "finite U" and us: "U \<subseteq> T"
    and premise: "goodman_book_proves \<Sigma> G U (book_imp A B)"
    using Gen.IH by blast
  have conclusion: "goodman_book_proves \<Sigma> G U (book_imp A (book_all G n B))"
    by (rule goodman_book_proves.Gen[OF premise Gen.hyps(2,3,4)])
  show ?case using uf us conclusion by blast
next
  case (PE P Q)
  obtain U where uf: "finite U" and us: "U \<subseteq> T"
    and premise: "goodman_book_proves \<Sigma> G U (book_iff G P Q)"
    using PE.IH by blast
  have conclusion: "goodman_book_proves \<Sigma> G U (book_leibniz G Prop P Q)"
    by (rule goodman_book_proves.PE[OF premise PE.hyps(2,3)])
  show ?case using uf us conclusion by blast
qed

theorem goodman_book_proves_iff_finite_support:
  "goodman_book_proves \<Sigma> G T A \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> T \<and> goodman_book_proves \<Sigma> G U A)"
proof
  assume "goodman_book_proves \<Sigma> G T A"
  then show "\<exists>U. finite U \<and> U \<subseteq> T \<and> goodman_book_proves \<Sigma> G U A"
    by (rule goodman_book_finite_support)
next
  assume "\<exists>U. finite U \<and> U \<subseteq> T \<and> goodman_book_proves \<Sigma> G U A"
  then obtain U where subset: "U \<subseteq> T"
    and derivation: "goodman_book_proves \<Sigma> G U A" by blast
  show "goodman_book_proves \<Sigma> G T A"
    by (rule goodman_book_mono[OF derivation subset])
qed

section \<open>Consistency and finite inconsistent subsets\<close>

lemma goodman_book_consistent_subset:
  assumes consistent: "goodman_book_consistent \<Sigma> G T"
    and subset: "U \<subseteq> T"
  shows "goodman_book_consistent \<Sigma> G U"
  using consistent goodman_book_mono[OF _ subset]
  unfolding goodman_book_consistent_def by blast

theorem goodman_book_consistent_iff_finite_subsets:
  "goodman_book_consistent \<Sigma> G T \<longleftrightarrow>
    (\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow> goodman_book_consistent \<Sigma> G U)"
  unfolding goodman_book_consistent_def
  using goodman_book_proves_iff_finite_support[where \<Sigma>=\<Sigma> and G=G
    and T=T and A="book_bottom G"] by blast

theorem goodman_book_inconsistent_iff_finite_refutation:
  "\<not> goodman_book_consistent \<Sigma> G T \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> T \<and>
      goodman_book_proves \<Sigma> G U (book_bottom G))"
  using goodman_book_proves_iff_finite_support[where \<Sigma>=\<Sigma> and G=G
    and T=T and A="book_bottom G"]
  unfolding goodman_book_consistent_def by blast

corollary goodman_book_inconsistent_iff_finite_inconsistent_subset:
  "\<not> goodman_book_consistent \<Sigma> G T \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> T \<and> \<not> goodman_book_consistent \<Sigma> G U)"
  using goodman_book_consistent_iff_finite_subsets[where \<Sigma>=\<Sigma> and G=G and T=T]
  by blast

section \<open>The native Recombination-plus-PP stock\<close>

corollary gb_recombination_PP_consistent_iff_finite_subsets:
  "goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G) \<longleftrightarrow>
    (\<forall>U. finite U \<longrightarrow> U \<subseteq> gb_recombination_PP_axioms G \<longrightarrow>
      goodman_book_consistent gb_signature G U)"
  by (rule goodman_book_consistent_iff_finite_subsets)

corollary gb_recombination_PP_negative_answer_iff_finite_refutation:
  "\<not> goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G) \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> gb_recombination_PP_axioms G \<and>
      goodman_book_proves gb_signature G U (book_bottom G))"
  by (rule goodman_book_inconsistent_iff_finite_refutation)

text \<open>
  These are proof-theoretic compactness statements. They neither construct
  a model for a finite fragment nor assert that every finite fragment is
  consistent. Each fragment retains exactly the same axiom-extension
  rules, including theorem-level PE, as the complete stock.
\<close>

end
