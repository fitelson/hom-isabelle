theory Bacon_Source_Relational_Henkin_Witness_Coverage
  imports Bacon_Source_Relational_Henkin_Full_Premises
begin

section \<open>Every full-language closed predicate has its actual conditional axiom\<close>

lemma paper_R_henkin_stage_witness_axiom:
  assumes index: "i \<in> paper_R_henkin_stage_indices \<Sigma> G k"
  shows "paper_R_witness_axiom G (fst i) (snd i) (paper_R_henkin_stage_name k i)
    \<in> paper_R_henkin_stage_axioms \<Sigma> G k"
  unfolding paper_R_henkin_stage_axioms_def paper_R_witness_family_axioms_def
  by (rule imageI[OF index])

lemma paper_R_henkin_stage_axiom_in_full:
  assumes member: "A \<in> paper_R_henkin_stage_axioms \<Sigma> G k"
  shows "A \<in> paper_R_henkin_full_premises \<Sigma> G S"
proof -
  have next_stage: "A \<in> paper_R_henkin_premises \<Sigma> G S (Suc k)"
    using member by (simp only: paper_R_henkin_premises.simps; blast)
  show ?thesis by (rule subsetD[OF paper_R_henkin_premise_stage_in_full next_stage])
qed

text \<open>
  A closed predicate F in Σ∞ already belongs to some Σₖ.
  The actual index (σ,F) therefore inserts its conditional witness
  axiom into Tₖ₊₁, and hence T∞. The corresponding name is
  declared in Σₖ₊₁ and therefore in Σ∞ as well.
  Source: the witness coverage required by Theorem 3.2, footnote 64.

  Coverage itself needs no consistency or richness premise. Turning
  these conditionals into witnesses in a maximal closed theory requires
  that theory's separate closure properties; it is not claimed here.
\<close>

theorem paper_R_henkin_full_witness_axiom:
  assumes predicate: "paper_R_in_language (paper_R_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  obtains k where "RWitness k \<sigma> F \<in> paper_R_henkin_full_signature \<Sigma> G \<sigma>"
    "paper_R_witness_axiom G \<sigma> F (RWitness k \<sigma> F) \<in> paper_R_henkin_full_premises \<Sigma> G S"
proof -
  obtain k where index: "(\<sigma>,F) \<in> paper_R_henkin_stage_indices \<Sigma> G k"
    and declared: "RWitness k \<sigma> F \<in> paper_R_henkin_full_signature \<Sigma> G \<sigma>"
    using paper_R_henkin_full_closed_predicate_witness[OF predicate closed] by blast
  have raw_axiom: "paper_R_witness_axiom G (fst (\<sigma>,F)) (snd (\<sigma>,F))
    (paper_R_henkin_stage_name k (\<sigma>,F)) \<in> paper_R_henkin_stage_axioms \<Sigma> G k"
    by (rule paper_R_henkin_stage_witness_axiom[OF index])
  have stage_axiom: "paper_R_witness_axiom G \<sigma> F (RWitness k \<sigma> F) \<in> paper_R_henkin_stage_axioms \<Sigma> G k"
    using raw_axiom by (simp only: paper_R_henkin_stage_name_def fst_conv snd_conv)
  have full_axiom: "paper_R_witness_axiom G \<sigma> F (RWitness k \<sigma> F) \<in> paper_R_henkin_full_premises \<Sigma> G S"
    by (rule paper_R_henkin_stage_axiom_in_full[OF stage_axiom])
  show thesis by (rule that[OF declared full_axiom])
qed

end
