theory Bacon_Book_Lambda_I_Henkin_Witness_Coverage
  imports Bacon_Book_Lambda_I_Henkin_Stage_Witnesses Bacon_Book_Lambda_I_Henkin_Full_Signature
begin

section \<open>The union of stage axioms covers every closed λI predicate\<close>

text \<open>
  Let W∞=⋃ₙWₙ. Every closed λI predicate F:σ→t in Σ∞ already belongs
  to some Σₙ. The same n supplies c=Witness(n,σ,F), declared in Σₙ₊₁
  (belonging to a stage does not allocate a name for a nonrelevant
  predicate),
  and the premise (∃σF)→Fc belongs to Wₙ and hence W∞.
  Source role: witness availability in the construction supporting
  Bacon, Proposition 15.4 and Theorem 15.3, pp.319–321.

  Representation. The index is exactly (σ,F); the predicate and witness
  are not selected independently from unrelated stages. Constants remain
  atomic even when their names store syntax. The index families can be
  uncountable although each individual term appears at a finite stage.
  Coverage is a pure syntax fact. Richness is needed below only for the
  formula-language guard on the literal existential witness axioms.
  No consistency, complete theory, semantic truth, or model is assumed.
\<close>

definition book_lambda_I_henkin_all_witness_axioms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c book_henkin_name) book_named_term set" where
  "book_lambda_I_henkin_all_witness_axioms \<Sigma> G = (\<Union>n. book_lambda_I_henkin_stage_axioms \<Sigma> G n)"

lemma book_lambda_I_henkin_stage_axioms_in_all:
  "book_lambda_I_henkin_stage_axioms \<Sigma> G n \<subseteq> book_lambda_I_henkin_all_witness_axioms \<Sigma> G"
  unfolding book_lambda_I_henkin_all_witness_axioms_def by blast

theorem book_lambda_I_henkin_witness_coverage:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "\<exists>c. c \<in> book_lambda_I_henkin_full_signature \<Sigma> G \<sigma> \<and>
    book_witness_axiom G \<sigma> F c \<in> book_lambda_I_henkin_all_witness_axioms \<Sigma> G"
proof -
  obtain n where stage: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_signature \<Sigma> G n) G F (Arr \<sigma> Prop)"
    and declared: "BookWitness n \<sigma> F \<in> book_lambda_I_henkin_full_signature \<Sigma> G \<sigma>"
    using book_lambda_I_henkin_full_closed_predicate_witness[OF predicate closed lambda_I] by blast
  have index: "(\<sigma>,F) \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
    using closed lambda_I stage by (simp add: book_lambda_I_henkin_stage_indices_def)
  have encoded: "(\<lambda>i. book_witness_axiom G (fst i) (snd i) (book_lambda_I_henkin_stage_name n i)) (\<sigma>,F)
      \<in> image (\<lambda>i. book_witness_axiom G (fst i) (snd i) (book_lambda_I_henkin_stage_name n i))
        (book_lambda_I_henkin_stage_indices \<Sigma> G n)"
    by (rule imageI[OF index])
  have stage_axiom: "book_witness_axiom G \<sigma> F (BookWitness n \<sigma> F)
      \<in> book_lambda_I_henkin_stage_axioms \<Sigma> G n"
    using encoded by (simp only: book_lambda_I_henkin_stage_axioms_def book_witness_family_axioms_def
      book_lambda_I_henkin_stage_name_def fst_conv snd_conv)
  have all_axiom: "book_witness_axiom G \<sigma> F (BookWitness n \<sigma> F)
      \<in> book_lambda_I_henkin_all_witness_axioms \<Sigma> G"
    by (rule subsetD[OF book_lambda_I_henkin_stage_axioms_in_all stage_axiom])
  show ?thesis by (rule exI[where x="BookWitness n \<sigma> F"]; rule conjI[OF declared all_axiom])
qed

theorem book_lambda_I_henkin_all_witness_axioms_member:
  assumes rich: "sg_rich G" and member: "A \<in> book_lambda_I_henkin_all_witness_axioms \<Sigma> G"
  shows "book_lambda_I_formula (book_lambda_I_henkin_full_signature \<Sigma> G) G A \<and> named_fv A = {}"
proof -
  obtain n where stage_member: "A \<in> book_lambda_I_henkin_stage_axioms \<Sigma> G n"
    using member unfolding book_lambda_I_henkin_all_witness_axioms_def by blast
  have stage_facts: "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G A \<and>
    named_fv A = {}"
    by (rule book_lambda_I_henkin_stage_axioms_member[OF rich stage_member])
  have full_language: "book_lambda_I_formula (book_lambda_I_henkin_full_signature \<Sigma> G) G A"
    by (rule book_lambda_I_formula_signature_mono[OF conjunct1[OF stage_facts]]; rule book_lambda_I_henkin_stage_in_full)
  show ?thesis by (rule conjI[OF full_language conjunct2[OF stage_facts]])
qed

corollary book_lambda_I_henkin_all_witness_axioms_closed_set:
  assumes rich: "sg_rich G"
  shows "book_lambda_I_closed_formula_set (book_lambda_I_henkin_full_signature \<Sigma> G) G
    (book_lambda_I_henkin_all_witness_axioms \<Sigma> G)"
  unfolding book_lambda_I_closed_formula_set_def
  by (intro ballI; rule book_lambda_I_henkin_all_witness_axioms_member[OF rich]; assumption)

end
