theory Bacon_Book_Classicism_Closed_Successor
  imports Bacon_Book_Classicism_Closed_Maximal Bacon_Book_Classicism_Boxed_Consequence
begin

section \<open>A closed negation-complete successor for an absent Box\<close>

definition book_C_unboxed_sentences ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term set" where
  "book_C_unboxed_sentences \<Sigma> G w =
    {A. book_theory_formula \<Sigma> G A \<and> named_fv A = {} \<and> book_box G A \<in> w}"

theorem book_C_closed_successor_exists:
  assumes rich: "sg_rich G" and world: "book_C_closed_maximal_extension \<Sigma> G T w"
    and pl: "book_theory_formula \<Sigma> G P" and closed: "named_fv P = {}"
    and missing: "book_box G P \<notin> w"
  shows "\<exists>v. book_C_closed_maximal_extension \<Sigma> G
      (insert (book_not G P) (book_C_unboxed_sentences \<Sigma> G w)) v \<and>
    book_not G P \<in> v \<and> P \<notin> v \<and> book_C_unboxed_sentences \<Sigma> G w \<subseteq> v"
proof -
  let ?S = "book_C_unboxed_sentences \<Sigma> G w"
  have sentences: "book_theory_formula \<Sigma> G A \<and> named_fv A = {}" if "A \<in> ?S" for A
    using that unfolding book_C_unboxed_sentences_def by blast
  have boxes: "book_box G ` ?S \<subseteq> w" unfolding book_C_unboxed_sentences_def by blast
  have absent_proof: "\<not> book_C_theory_derivable \<Sigma> G w (book_box G P)"
  proof
    assume derivation: "book_C_theory_derivable \<Sigma> G w (book_box G P)"
    have box_closed: "named_fv (book_box G P) = {}" by (simp only: book_box_fv closed)
    have member: "book_box G P \<in> w" by (rule book_C_closed_maximal_consequence[OF rich world derivation box_closed])
    show False by (rule notE[OF missing member])
  qed
  have consistent: "book_C_theory_consistent \<Sigma> G (insert (book_not G P) ?S)"
    by (rule book_C_successor_seed_consistent[OF rich sentences pl closed boxes absent_proof])
  have negative_type: "book_theory_formula \<Sigma> G (book_not G P)" by (rule book_not_language[OF rich pl])
  have negative_closed: "named_fv (book_not G P) = {}" by (simp only: book_not_fv closed)
  have closed_seed: "book_closed_formula_set \<Sigma> G (insert (book_not G P) ?S)"
    using sentences negative_type negative_closed unfolding book_closed_formula_set_def by blast
  obtain v where maximal: "book_C_closed_maximal_extension \<Sigma> G (insert (book_not G P) ?S) v"
    using book_C_closed_maximal_extension_exists[OF rich closed_seed consistent] by blast
  have seed: "insert (book_not G P) ?S \<subseteq> v" by (rule book_C_closed_maximal_data(4)[OF maximal])
  have negative: "book_not G P \<in> v" using seed by blast
  have old_maximal: "book_closed_maximal_extension \<Sigma> G
    (book_C_closed_theorems \<Sigma> G \<union> insert (book_not G P) ?S) v"
    using maximal unfolding book_C_closed_maximal_extension_def .
  have absent: "P \<notin> v" using negative book_closed_maximal_negation_iff[OF rich old_maximal pl closed] by blast
  show ?thesis using maximal seed absent by blast
qed

text \<open>
  This gives an actual closed maximal successor with ¬P and every
  closed A whose □A belongs to w. It is the fixed-signature,
  negation-complete part of Proposition 18.3, not yet that proposition
  for the book's witness-complete varying-language canonical worlds.
  No missing witness or fresh-name-reserve condition is silently added
  to the constructed set. Full modal completeness is assembled separately
  in Bacon_Book_ZF_Full_C_Completeness for countably declared signatures.
\<close>

end
