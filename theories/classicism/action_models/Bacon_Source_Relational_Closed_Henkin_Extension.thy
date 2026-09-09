theory Bacon_Source_Relational_Closed_Henkin_Extension
  imports Bacon_Source_Relational_Closed_Henkin_Theory Bacon_Source_Relational_Lindenbaum
    Bacon_Source_Relational_Henkin_Union_Consistency Bacon_Source_Relational_Henkin_Witness_Coverage
begin

section \<open>The actual witness union survives maximal closed extension\<close>

lemma paper_R_henkin_maximal_conditional_witness:
  assumes maximal: "paper_R_closed_maximal_extension (paper_R_henkin_full_signature \<Sigma> G) G
      (paper_R_henkin_full_premises \<Sigma> G S) M"
    and predicate: "paper_R_in_language (paper_R_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "\<exists>c\<in>paper_R_henkin_full_signature \<Sigma> G \<sigma>. paper_R_witness_axiom G \<sigma> F c \<in> M"
proof -
  obtain k where declared: "RWitness k \<sigma> F \<in> paper_R_henkin_full_signature \<Sigma> G \<sigma>"
    and witness: "paper_R_witness_axiom G \<sigma> F (RWitness k \<sigma> F) \<in> paper_R_henkin_full_premises \<Sigma> G S"
    by (rule paper_R_henkin_full_witness_axiom[where S=S, OF predicate closed])
  have in_M: "paper_R_witness_axiom G \<sigma> F (RWitness k \<sigma> F) \<in> M"
    by (rule subsetD[OF paper_R_closed_maximal_extends[OF maximal] witness])
  show ?thesis by (rule bexI[where x="RWitness k \<sigma> F"], rule in_M, rule declared)
qed

section \<open>A closed Henkin theory exists over the arbitrary original signature\<close>

text \<open>
  Start with the actual staged witness premises T∞. Their closedness
  and native R consistency have been proved, including transport of
  stage proofs to the full signature. Zorn supplies a maximal closed
  consistent M above T∞. Every original embedded sentence lies in M;
  every full-language closed predicate's conditional witness also lies
  in M. Local MP and closed-consequence closure produce actual witness
  instances. Richness supplies closed negation decisions separately.

  This constructs all the displayed Henkin properties from consistency
  of the original CLOSED S; none is an extra premise of the existence
  theorem. Source: Theorem 3.2, p.45 n.64, with the closed-formula
  scope kept explicit. The constant-name carrier and S are arbitrary;
  there is no enumeration or countability hypothesis. No canonical
  interpretation, model existence or completeness theorem is concluded.
\<close>

theorem paper_R_closed_Henkin_extension_exists:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>M. paper_R_closed_maximal_extension (paper_R_henkin_full_signature \<Sigma> G) G
      (paper_R_henkin_full_premises \<Sigma> G S) M \<and>
    image (paper_R_constant_map ROriginal) S \<subseteq> M \<and>
    paper_R_closed_Henkin_theory (paper_R_henkin_full_signature \<Sigma> G) G M"
proof -
  let ?\<Omega> = "paper_R_henkin_full_signature \<Sigma> G"
  let ?T = "paper_R_henkin_full_premises \<Sigma> G S"
  have closed_union: "paper_R_closed_theory ?\<Omega> G ?T"
    by (rule paper_R_henkin_full_premises_closed[OF rich source])
  have consistent_union: "paper_R_named_consistent ?\<Omega> G ?T"
    by (rule paper_R_henkin_full_premises_consistent[OF rich source consistent])
  obtain M where maximal: "paper_R_closed_maximal_extension ?\<Omega> G ?T M"
    using paper_R_closed_maximal_extension_exists[OF closed_union consistent_union] by blast
  have conditionals: "\<exists>c\<in>?\<Omega> \<sigma>. paper_R_witness_axiom G \<sigma> F c \<in> M"
    if predicate: "paper_R_in_language ?\<Omega> G F (Arr \<sigma> Prop)" and closed: "named_fv F = {}" for \<sigma> F
    by (rule paper_R_henkin_maximal_conditional_witness[OF maximal predicate closed])
  have henkin: "paper_R_closed_Henkin_theory ?\<Omega> G M"
    by (rule paper_R_closed_maximal_Henkin[OF maximal rich conditionals])
  have original: "image (paper_R_constant_map ROriginal) S \<subseteq> M"
    by (rule subset_trans[OF paper_R_henkin_full_premises_original_inclusion paper_R_closed_maximal_extends[OF maximal]])
  show ?thesis by (rule exI[where x=M], rule conjI[OF maximal conjI[OF original henkin]])
qed

end
