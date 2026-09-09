theory Bacon_Book_Henkin_Union
  imports Bacon_Book_Henkin_Premise_Stages Bacon_Book_Henkin_Witness_Coverage
    Bacon_Book_Consistency_Unions
begin

section \<open>The union of the constructed witness-premise stages\<close>

text \<open>
  S∞=⋃ₙSₙ is considered in the FULL signature Σ∞. Each Sₙ is
  first transported from its own signature Σₙ to Σ∞, retaining all
  premise-name guards. The increasing family then has a consistent union
  by finite proof support. Source role: the limiting step of Bacon's
  Proposition 15.4, p.319, for the explicitly closed-predicate witnesses.

  Each stage can have arbitrary cardinality. The natural-number index
  counts stages, not formulas or constants. S may be open and infinite.
  This constructs consistent premises with all closed-predicate witness
  conditionals; it is not yet a negation-complete set or a general model.
\<close>

definition book_henkin_full_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow>
    ('c book_henkin_name) book_named_term set" where
  "book_henkin_full_premises \<Sigma> G S = (\<Union>n. book_henkin_premises \<Sigma> G S n)"

lemma book_henkin_premises_in_full:
  "book_henkin_premises \<Sigma> G S n \<subseteq> book_henkin_full_premises \<Sigma> G S"
  unfolding book_henkin_full_premises_def by blast

lemma book_henkin_original_in_full:
  "image (book_constant_rename BookOriginal) S \<subseteq> book_henkin_full_premises \<Sigma> G S"
proof -
  have initial: "book_henkin_premises \<Sigma> G S 0 \<subseteq> book_henkin_full_premises \<Sigma> G S"
    by (rule book_henkin_premises_in_full)
  show ?thesis using initial by (simp only: book_henkin_premises.simps)
qed

theorem book_henkin_full_premises_language:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and member: "A \<in> book_henkin_full_premises \<Sigma> G S"
  shows "book_theory_formula (book_henkin_full_signature \<Sigma> G) G A"
proof -
  obtain n where in_stage: "A \<in> book_henkin_premises \<Sigma> G S n"
    using member unfolding book_henkin_full_premises_def by blast
  have stage_language: "book_theory_formula (book_henkin_signature \<Sigma> G n) G A"
    by (rule book_henkin_premises_language[OF rich language in_stage])
  show ?thesis by (rule book_language_signature_mono[OF stage_language]; rule book_henkin_stage_in_full)
qed

theorem book_henkin_full_premises_consistent:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_theory_consistent \<Sigma> G S"
  shows "book_theory_consistent (book_henkin_full_signature \<Sigma> G) G
    (book_henkin_full_premises \<Sigma> G S)"
proof -
  let ?P = "book_henkin_premises \<Sigma> G S"
  let ?C = "range ?P"
  have nonempty: "?C \<noteq> {}" by simp
  have stage_consistent: "book_theory_consistent (book_henkin_full_signature \<Sigma> G) G (?P n)" for n
  proof -
    have original_stage: "book_theory_consistent (book_henkin_signature \<Sigma> G n) G (?P n)"
      by (rule book_henkin_premises_consistent[OF rich language consistent])
    have names: "named_in_signature (book_henkin_signature \<Sigma> G n) A" if "A \<in> ?P n" for A
      by (rule book_language_signature[OF book_henkin_premises_language[OF rich language that]])
    show ?thesis by (rule book_theory_consistent_signature_transport[OF rich original_stage names])
  qed
  have all_consistent: "book_theory_consistent (book_henkin_full_signature \<Sigma> G) G U"
    if "U \<in> ?C" for U
    using that stage_consistent by blast
  have directed: "\<And>U V. U \<in> ?C \<Longrightarrow> V \<in> ?C \<Longrightarrow> \<exists>W\<in>?C. U \<union> V \<subseteq> W"
  proof -
    fix U V
    assume U_member: "U \<in> ?C" and V_member: "V \<in> ?C"
    obtain n where U_shape: "U = ?P n" using U_member by blast
    obtain m where V_shape: "V = ?P m" using V_member by blast
    have member: "?P (max n m) \<in> ?C" by (rule rangeI)
    have first: "?P n \<subseteq> ?P (max n m)"
      by (rule book_henkin_premises_mono; simp)
    have second: "?P m \<subseteq> ?P (max n m)"
      by (rule book_henkin_premises_mono; simp)
    have covered: "U \<union> V \<subseteq> ?P (max n m)"
      by (simp only: U_shape V_shape; rule Un_least[OF first second])
    show "\<exists>W\<in>?C. U \<union> V \<subseteq> W" by (rule bexI[where x="?P (max n m)"]; fact)
  qed
  have union_consistent: "book_theory_consistent (book_henkin_full_signature \<Sigma> G) G (\<Union>?C)"
    by (rule book_theory_consistent_directed_Union[OF nonempty directed all_consistent])
  show ?thesis using union_consistent by (simp only: book_henkin_full_premises_def)
qed

lemma book_henkin_full_premises_closed:
  assumes rich: "sg_rich G" and closed: "\<And>B. B \<in> S \<Longrightarrow> named_fv B = {}"
    and member: "A \<in> book_henkin_full_premises \<Sigma> G S"
  shows "named_fv A = {}"
proof -
  obtain n where in_stage: "A \<in> book_henkin_premises \<Sigma> G S n"
    using member unfolding book_henkin_full_premises_def by blast
  show ?thesis by (rule book_henkin_premises_closed[OF rich closed in_stage])
qed

theorem book_henkin_all_witness_axioms_in_premises:
  "book_henkin_all_witness_axioms \<Sigma> G \<subseteq> book_henkin_full_premises \<Sigma> G S"
proof
  fix A
  assume member: "A \<in> book_henkin_all_witness_axioms \<Sigma> G"
  obtain n where in_stage: "A \<in> book_henkin_stage_axioms \<Sigma> G n"
    using member unfolding book_henkin_all_witness_axioms_def by blast
  have in_next: "A \<in> book_henkin_premises \<Sigma> G S (Suc n)"
    using in_stage by simp
  show "A \<in> book_henkin_full_premises \<Sigma> G S"
    by (rule subsetD[OF book_henkin_premises_in_full in_next])
qed

theorem book_henkin_full_premises_witness:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "\<exists>c. c \<in> book_henkin_full_signature \<Sigma> G \<sigma> \<and>
    book_witness_axiom G \<sigma> F c \<in> book_henkin_full_premises \<Sigma> G S"
proof -
  obtain c where declared: "c \<in> book_henkin_full_signature \<Sigma> G \<sigma>"
    and axiom_member: "book_witness_axiom G \<sigma> F c \<in> book_henkin_all_witness_axioms \<Sigma> G"
    using book_henkin_witness_coverage[OF predicate closed] by blast
  have in_premises: "book_witness_axiom G \<sigma> F c \<in> book_henkin_full_premises \<Sigma> G S"
    by (rule subsetD[OF book_henkin_all_witness_axioms_in_premises axiom_member])
  show ?thesis by (rule exI[where x=c], rule conjI[OF declared in_premises])
qed

end
