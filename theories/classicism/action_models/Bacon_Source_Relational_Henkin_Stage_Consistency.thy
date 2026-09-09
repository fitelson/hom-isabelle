theory Bacon_Source_Relational_Henkin_Stage_Consistency
  imports Bacon_Source_Relational_Henkin_Premise_Stages
    Bacon_Source_Relational_Witness_Family_Consistency Bacon_Source_Relational_Constant_Map_Consistency
begin

section \<open>Initial consistency is proved by the actual Original embedding\<close>

lemma paper_R_henkin_original_consistent:
  fixes \<Sigma> :: "'c ssignature"
  assumes consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "paper_R_named_consistent (paper_R_henkin_signature \<Sigma> G 0) G
    (paper_R_henkin_premises \<Sigma> G S 0)"
proof -
  have injective: "inj (ROriginal :: 'c \<Rightarrow> 'c paper_R_henkin_name)" by (rule injI; simp)
  have mapped: "paper_R_named_consistent (\<lambda>\<rho>. image ROriginal (\<Sigma> \<rho>)) G
    (image (paper_R_constant_map ROriginal) S)"
    by (rule iffD1[OF paper_R_named_consistent_injective_constant_map_iff[
      where f=ROriginal and \<Sigma>=\<Sigma> and G=G and S=S, OF injective] consistent])
  show ?thesis by (simp only: paper_R_henkin_signature.simps paper_R_henkin_premises.simps; rule mapped)
qed

section \<open>Every constructed stage is closed and consistent\<close>

text \<open>
  Starting with closed consistent S, its actual Original-name image
  is consistent by native proof reflection. At stage k, the previously
  proved family theorem applies to ALL indices Iₖ: their predicates
  are closed in Σₖ, and their Witness(k,σ,F) names are proved
  fresh and typed-name injective. It yields consistency of Tₖ₊₁
  in the signature that is proved equal to Σₖ₊₁.

  Source: Theorem 3.2, footnote 64, p.45. Neither initial-image
  consistency nor the fresh-name family is an additional premise.
  S may be infinite and its name carrier arbitrary. No enumeration,
  countability, limit union, maximal theory or model is asserted here.
\<close>

theorem paper_R_henkin_premises_consistent:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "paper_R_named_consistent (paper_R_henkin_signature \<Sigma> G k) G (paper_R_henkin_premises \<Sigma> G S k)"
proof (induction k rule: nat.induct[case_names zero Suc])
  case zero
  show ?case by (rule paper_R_henkin_original_consistent[OF consistent])
next
  case (Suc k)
  have closed_stage: "paper_R_closed_theory (paper_R_henkin_signature \<Sigma> G k) G
    (paper_R_henkin_premises \<Sigma> G S k)"
    by (rule paper_R_henkin_premises_closed[OF rich source])
  have predicates: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G (snd i) (Arr (fst i) Prop)"
    if "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" for i
    by (rule paper_R_henkin_stage_index_language[OF that])
  have closed: "named_fv (snd i) = {}" if "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" for i
    by (rule paper_R_henkin_stage_index_closed[OF that])
  have fresh: "paper_R_henkin_stage_name k i \<notin> paper_R_henkin_signature \<Sigma> G k (fst i)"
    if "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" for i
    by (rule paper_R_henkin_stage_name_fresh)
  show ?case
    by (simp only: paper_R_henkin_signature_family paper_R_henkin_premises.simps paper_R_henkin_stage_axioms_def;
      rule paper_R_named_consistent_witness_family[OF rich closed_stage Suc.IH predicates closed fresh
        paper_R_henkin_stage_typed_names_inj_on])
qed

end
