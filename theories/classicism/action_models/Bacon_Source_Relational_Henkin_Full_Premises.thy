theory Bacon_Source_Relational_Henkin_Full_Premises
  imports Bacon_Source_Relational_Henkin_Premise_Stages Bacon_Source_Relational_Henkin_Full_Signature
begin

section \<open>The union of the actual premise stages\<close>

definition paper_R_henkin_full_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    ('c paper_R_henkin_name) paper_named_term set" where
  "paper_R_henkin_full_premises \<Sigma> G S = (\<Union>k. paper_R_henkin_premises \<Sigma> G S k)"

lemma paper_R_henkin_premise_stage_in_full:
  "paper_R_henkin_premises \<Sigma> G S k \<subseteq> paper_R_henkin_full_premises \<Sigma> G S"
  by (auto simp: paper_R_henkin_full_premises_def)

lemma paper_R_henkin_full_premises_original_inclusion:
  "image (paper_R_constant_map ROriginal) S \<subseteq> paper_R_henkin_full_premises \<Sigma> G S"
  by (rule subset_trans[OF paper_R_henkin_premises_original_inclusion[where k=0]
    paper_R_henkin_premise_stage_in_full])

theorem paper_R_henkin_full_premises_closed:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
  shows "paper_R_closed_theory (paper_R_henkin_full_signature \<Sigma> G) G (paper_R_henkin_full_premises \<Sigma> G S)"
proof (unfold paper_R_closed_theory_def, intro ballI)
  fix A
  assume member: "A \<in> paper_R_henkin_full_premises \<Sigma> G S"
  obtain k where stage_member: "A \<in> paper_R_henkin_premises \<Sigma> G S k"
    using member unfolding paper_R_henkin_full_premises_def by blast
  have stage_closed: "paper_R_closed_theory (paper_R_henkin_signature \<Sigma> G k) G (paper_R_henkin_premises \<Sigma> G S k)"
    by (rule paper_R_henkin_premises_closed[OF rich source])
  have sentence: "paper_R_sentence (paper_R_henkin_signature \<Sigma> G k) G A"
    by (rule paper_R_closed_theory_member[OF stage_closed stage_member])
  show "paper_R_sentence (paper_R_henkin_full_signature \<Sigma> G) G A"
    by (rule paper_R_sentence_signature_mono[OF sentence]; rule paper_R_henkin_stage_in_full)
qed

section \<open>Every finite premise subset is contained in one actual stage\<close>

text \<open>
  Empty finite support is contained in T₀. For an added premise,
  take the maximum of its stage and the previous finite bound.
  This argument uses increasing stages, not an enumeration of all
  formulas or all names. Source role: the Henkin union in Theorem 3.2,
  footnote 64, p.45.
\<close>

theorem paper_R_henkin_finite_premises_stage_bound:
  assumes finite: "finite U" and subset: "U \<subseteq> paper_R_henkin_full_premises \<Sigma> G S"
  shows "\<exists>k. U \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
  using finite subset
proof (induction U rule: finite_induct)
  case empty
  show ?case by (rule exI[where x=0]; simp)
next
  case (insert A U)
  have member: "A \<in> paper_R_henkin_full_premises \<Sigma> G S"
    and subset: "U \<subseteq> paper_R_henkin_full_premises \<Sigma> G S" using insert.prems by blast+
  obtain j where aj: "A \<in> paper_R_henkin_premises \<Sigma> G S j"
    using member unfolding paper_R_henkin_full_premises_def by blast
  obtain k where uk: "U \<subseteq> paper_R_henkin_premises \<Sigma> G S k" using insert.IH[OF subset] by blast
  have amax: "A \<in> paper_R_henkin_premises \<Sigma> G S (max j k)"
    by (rule subsetD[OF paper_R_henkin_premises_mono[OF max.cobounded1] aj])
  have umax: "U \<subseteq> paper_R_henkin_premises \<Sigma> G S (max j k)"
    by (rule subset_trans[OF uk paper_R_henkin_premises_mono[OF max.cobounded2]])
  show ?case by (rule exI[where x="max j k"]; use amax umax in blast)
qed

end
