theory Bacon_Book_Classicism_Henkin_Union
  imports Bacon_Book_Classicism_Henkin_Stages
    Bacon_Book_Environment_Development.Bacon_Book_Henkin_Union
begin

lemma book_C_consistent_directed_Union:
  assumes nonempty: "\<C> \<noteq> {}"
    and directed: "\<And>U V. U \<in> \<C> \<Longrightarrow> V \<in> \<C> \<Longrightarrow> \<exists>W\<in>\<C>. U \<union> V \<subseteq> W"
    and consistent: "\<And>U. U \<in> \<C> \<Longrightarrow> book_C_theory_consistent \<Sigma> G U"
  shows "book_C_theory_consistent \<Sigma> G (\<Union>\<C>)"
proof (rule iffD2[OF book_C_theory_consistent_finite_character], intro allI impI)
  fix F
  assume finite_F: "finite F" and included: "F \<subseteq> \<Union>\<C>"
  obtain U where member: "U \<in> \<C>" and covered: "F \<subseteq> U"
    using book_finite_directed_cover[OF finite_F included nonempty directed] by blast
  show "book_C_theory_consistent \<Sigma> G F" by (rule book_C_consistent_subset[OF consistent[OF member] covered])
qed

theorem book_C_henkin_full_premises_consistent:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (book_henkin_full_premises \<Sigma> G S)"
proof -
  let ?P = "book_henkin_premises \<Sigma> G S"
  let ?F = "range ?P"
  have nonempty: "?F \<noteq> {}" by simp
  have stages: "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (?P n)" for n
  proof -
    have previous: "book_C_theory_consistent (book_henkin_signature \<Sigma> G n) G (?P n)"
      by (rule book_C_henkin_premises_consistent[OF rich language consistent])
    have stage_language: "book_theory_formula (book_henkin_signature \<Sigma> G n) G A" if "A \<in> ?P n" for A
      by (rule book_henkin_premises_language[OF rich language that])
    show ?thesis by (rule book_C_theory_consistency_signature_preservation[OF rich previous stage_language])
  qed
  have all_consistent: "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G U" if "U \<in> ?F" for U
    using that stages by blast
  have directed: "\<exists>W\<in>?F. U \<union> V \<subseteq> W" if um: "U \<in> ?F" and vm: "V \<in> ?F" for U V
  proof -
    obtain n where us: "U = ?P n" using um by blast
    obtain m where vs: "V = ?P m" using vm by blast
    have first: "?P n \<subseteq> ?P (max n m)" by (rule book_henkin_premises_mono; simp)
    have second: "?P m \<subseteq> ?P (max n m)" by (rule book_henkin_premises_mono; simp)
    have subset: "U \<union> V \<subseteq> ?P (max n m)" by (simp only: us vs; rule Un_least[OF first second])
    show ?thesis by (rule bexI[where x="?P (max n m)"], rule subset, rule rangeI)
  qed
  have union: "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (\<Union>?F)"
    by (rule book_C_consistent_directed_Union[OF nonempty directed all_consistent])
  show ?thesis using union by (simp only: book_henkin_full_premises_def)
qed

text \<open>
  Every stage is first transported to the final signature, with the
  full C theorem set at that signature retained. The directed union
  argument therefore takes place over one fixed background. The
  existing syntax theorem supplies a witness conditional for every
  closed predicate of the final language, not merely the original one.
  This still constructs premises, not a negation-complete world.
\<close>

end
