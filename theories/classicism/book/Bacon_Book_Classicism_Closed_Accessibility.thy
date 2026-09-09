theory Bacon_Book_Classicism_Closed_Accessibility
  imports Bacon_Book_Classicism_Closed_Successor Bacon_Book_Classicism_Modal_Four
    Bacon_Book_Classicism_Modal_T
begin

section \<open>Accessibility between closed maximal C sets\<close>

definition book_C_closed_worlds :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set set" where
  "book_C_closed_worlds \<Sigma> G = {w. book_C_closed_maximal_extension \<Sigma> G {} w}"

definition book_C_accessible :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    'c book_named_term set \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_C_accessible \<Sigma> G w v \<longleftrightarrow> book_C_unboxed_sentences \<Sigma> G w \<subseteq> v"

lemma book_C_closed_maximal_is_world:
  assumes maximal: "book_C_closed_maximal_extension \<Sigma> G S w"
  shows "w \<in> book_C_closed_worlds \<Sigma> G"
  using maximal unfolding book_C_closed_worlds_def book_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast

lemma book_C_closed_world_maximal:
  "w \<in> book_C_closed_worlds \<Sigma> G \<Longrightarrow> book_C_closed_maximal_extension \<Sigma> G {} w"
  by (simp only: book_C_closed_worlds_def mem_Collect_eq)

lemma book_C_closed_world_apply_theorem:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_closed_worlds \<Sigma> G"
    and theorem_C: "book_C_proves \<Sigma> G (book_imp A B)"
    and member: "A \<in> w" and closed: "named_fv B = {}"
  shows "B \<in> w"
proof -
  have operands: "book_theory_formula \<Sigma> G A \<and> book_theory_formula \<Sigma> G B"
    by (rule book_theory_imp_operands[OF book_C_proves_language[OF rich theorem_C]])
  have premise: "book_C_theory_derivable \<Sigma> G w A" by (rule book_C_theory_assume[OF member conjunct1[OF operands]])
  have conditional: "book_C_theory_derivable \<Sigma> G w (book_imp A B)" by (rule book_C_theory_from_C[OF rich theorem_C])
  have result: "book_C_theory_derivable \<Sigma> G w B" by (rule book_C_theory_MP[OF premise conditional conjunct2[OF operands]])
  show ?thesis by (rule book_C_closed_maximal_consequence[OF rich book_C_closed_world_maximal[OF world] result closed])
qed

theorem book_C_accessible_reflexive:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_closed_worlds \<Sigma> G"
  shows "book_C_accessible \<Sigma> G w w"
proof (unfold book_C_accessible_def, rule subsetI)
  fix A
  assume member: "A \<in> book_C_unboxed_sentences \<Sigma> G w"
  have al: "book_theory_formula \<Sigma> G A" and closed: "named_fv A = {}" and box: "book_box G A \<in> w"
    using member unfolding book_C_unboxed_sentences_def by blast+
  show "A \<in> w" by (rule book_C_closed_world_apply_theorem[OF rich world book_C_modal_T[OF rich al] box closed])
qed

theorem book_C_accessible_transitive:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_closed_worlds \<Sigma> G"
    and first: "book_C_accessible \<Sigma> G w v" and second: "book_C_accessible \<Sigma> G v u"
  shows "book_C_accessible \<Sigma> G w u"
proof (unfold book_C_accessible_def, rule subsetI)
  fix A
  assume member: "A \<in> book_C_unboxed_sentences \<Sigma> G w"
  have al: "book_theory_formula \<Sigma> G A" and closed: "named_fv A = {}" and box: "book_box G A \<in> w"
    using member unfolding book_C_unboxed_sentences_def by blast+
  have bc: "named_fv (book_box G A) = {}" by (simp only: book_box_fv closed)
  have bbc: "named_fv (book_box G (book_box G A)) = {}" by (simp only: book_box_fv closed)
  have iterated: "book_box G (book_box G A) \<in> w"
    by (rule book_C_closed_world_apply_theorem[OF rich world book_C_modal_4[OF rich al] box bbc])
  have first_kernel: "book_box G A \<in> book_C_unboxed_sentences \<Sigma> G w"
    using book_box_language[OF rich al] bc iterated by (simp add: book_C_unboxed_sentences_def)
  have box_at_v: "book_box G A \<in> v" using first first_kernel unfolding book_C_accessible_def by blast
  have second_kernel: "A \<in> book_C_unboxed_sentences \<Sigma> G v"
    using al closed box_at_v by (simp add: book_C_unboxed_sentences_def)
  show "A \<in> u" using second second_kernel unfolding book_C_accessible_def by blast
qed

theorem book_C_closed_world_box_iff:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_closed_worlds \<Sigma> G"
    and pl: "book_theory_formula \<Sigma> G P" and closed: "named_fv P = {}"
  shows "book_box G P \<in> w \<longleftrightarrow>
    (\<forall>v\<in>book_C_closed_worlds \<Sigma> G. book_C_accessible \<Sigma> G w v \<longrightarrow> P \<in> v)"
proof
  assume boxed: "book_box G P \<in> w"
  have member: "P \<in> book_C_unboxed_sentences \<Sigma> G w" using pl closed boxed by (simp add: book_C_unboxed_sentences_def)
  show "\<forall>v\<in>book_C_closed_worlds \<Sigma> G. book_C_accessible \<Sigma> G w v \<longrightarrow> P \<in> v"
    using member unfolding book_C_accessible_def by blast
next
  assume every: "\<forall>v\<in>book_C_closed_worlds \<Sigma> G. book_C_accessible \<Sigma> G w v \<longrightarrow> P \<in> v"
  show "book_box G P \<in> w"
  proof (rule ccontr)
    assume missing: "book_box G P \<notin> w"
    obtain v where maximal: "book_C_closed_maximal_extension \<Sigma> G
        (insert (book_not G P) (book_C_unboxed_sentences \<Sigma> G w)) v"
      and absent: "P \<notin> v" and extends: "book_C_unboxed_sentences \<Sigma> G w \<subseteq> v"
      using book_C_closed_successor_exists[OF rich book_C_closed_world_maximal[OF world] pl closed missing] by blast
    have vw: "v \<in> book_C_closed_worlds \<Sigma> G" by (rule book_C_closed_maximal_is_world[OF maximal])
    have accessible: "book_C_accessible \<Sigma> G w v" using extends unfolding book_C_accessible_def .
    show False using every vw accessible absent by blast
  qed
qed

text \<open>
  T and 4 prove reflexivity and transitivity. The final equivalence
  uses an actual closed maximal successor, not an assumed existence
  axiom. Its worlds are fixed-signature closed maximal C sets.
  They need not have witnesses: this is the modal part of the canonical
  construction, not Definition 18.8's completed varying-language worlds
  and not higher-order modal completeness.
\<close>

end
