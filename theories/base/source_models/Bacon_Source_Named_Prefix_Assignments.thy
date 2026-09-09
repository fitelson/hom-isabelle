theory Bacon_Source_Named_Prefix_Assignments
  imports Bacon_Source_Chart_Assignments Bacon_Source_Named_Model_Tag_Assignments
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Prefix_Roundtrip
begin

section \<open>Finite prefix assignments and completion agreement\<close>

text \<open>
  Assign the names 0,…,m−1 the values ρ(0),…,ρ(m−1).
  If h completes a typed named assignment g, use the tagged environment
  ρ(n) = ⟨G(n),h(n)⟩. Removing the finite assignment's tags recovers
  g at every assigned name below m.
  Source role: adequate typed partial assignments in Bacon–Dorr
  Definition 3.1, pp.43–44.

  Isabelle representation. The prefix assignment is the existing chart
  assignment for [0..<m], not a new assignment mechanism. For an arbitrary
  ρ, only its typing in source_prefix G m is required: no constraint on
  ρ beyond m is introduced. Adequacy follows separately from FV(A) ⊆
  {0,…,m−1}. The total h appears only when explicitly given as a total
  typed assignment or a completion.

  Status. Assignment facts only, with no model, denotation, rich-stock,
  signature-inhabitant, or semantic-domain-inhabitant premise.
\<close>

definition named_prefix_assignment :: "nat \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'v named_assignment" where
  "named_prefix_assignment m \<rho> = named_chart_assignment [0..<m] \<rho>"

lemma named_prefix_assignment_lookup:
  assumes bound: "n < m"
  shows "named_prefix_assignment m \<rho> n = Some (\<rho> n)"
proof -
  have distinct: "distinct [0..<m]" by simp
  have index: "n < length [0..<m]" using bound by simp
  have at_n: "named_chart_assignment [0..<m] \<rho> ([0..<m] ! n) = Some (\<rho> n)"
    by (rule named_chart_assignment_lookup[OF distinct index])
  show ?thesis using at_n bound by (simp add: named_prefix_assignment_def)
qed

lemma named_prefix_assignment_domain:
  "dom (named_prefix_assignment m \<rho>) = {..<m}"
  by (auto simp: named_prefix_assignment_def named_chart_assignment_domain)

lemma named_prefix_assignment_typed:
  assumes typed: "pbbk_env_typed D (source_prefix G m) \<rho>"
  shows "named_env_typed D G (named_prefix_assignment m \<rho>)"
  unfolding named_prefix_assignment_def
  by (rule named_chart_assignment_typed[OF named_identity_prefix_chart typed])

lemma named_prefix_assignment_adequate:
  assumes support: "named_fv A \<subseteq> {..<m}"
  shows "named_adequate (named_prefix_assignment m \<rho>) A"
  by (simp only: named_adequate_def named_prefix_assignment_domain; rule support)

lemma named_untagged_prefix_typed:
  assumes typed: "pbbk_env_typed (named_tag_domain D) (source_prefix G m) \<rho>"
  shows "named_env_typed D G (named_untag_assignment (named_prefix_assignment m \<rho>))"
  by (rule named_untag_assignment_typed[OF named_prefix_assignment_typed[OF typed]])

lemma named_untagged_prefix_adequate:
  assumes support: "named_fv A \<subseteq> {..<m}"
  shows "named_adequate (named_untag_assignment (named_prefix_assignment m \<rho>)) A"
  by (rule iffD2[OF named_untag_assignment_adequate named_prefix_assignment_adequate[OF support]])

lemma named_tagged_prefix_env_from_total:
  assumes typed: "paper_global_env_typed D G h"
  shows "pbbk_env_typed (named_tag_domain D) (source_prefix G m) (\<lambda>n. (G n, h n))"
proof -
  have tagged: "paper_global_env_typed (named_tag_domain D) G (\<lambda>n. (G n, h n))"
  proof (unfold paper_global_env_typed_def, rule allI)
    fix n
    have member: "h n \<in> D (G n)" by (rule paper_global_env_at[OF typed])
    show "(G n, h n) \<in> named_tag_domain D (G n)"
      by (simp only: named_tag_domain_pair_iff; rule conjI[OF refl member])
  qed
  show ?thesis by (rule paper_global_env_prefix[OF tagged])
qed

corollary named_tagged_prefix_env_from_completion:
  assumes completion: "named_completion D G g h"
  shows "pbbk_env_typed (named_tag_domain D) (source_prefix G m) (\<lambda>n. (G n, h n))"
  by (rule named_tagged_prefix_env_from_total[OF named_completion_typed[OF completion]])

lemma named_prefix_completion_value:
  assumes completion: "named_completion D G g h"
    and bound: "n < m" and assigned: "g n = Some a"
  shows "named_untag_assignment (named_prefix_assignment m (\<lambda>i. (G i, h i))) n = Some a"
proof -
  have prefix: "named_prefix_assignment m (\<lambda>i. (G i, h i)) n = Some (G n, h n)"
    by (rule named_prefix_assignment_lookup[OF bound])
  have projected: "named_untag_assignment (named_prefix_assignment m (\<lambda>i. (G i, h i))) n =
    Some (snd (G n, h n))"
    by (rule named_untag_assignment_value[where g="named_prefix_assignment m (\<lambda>i. (G i, h i))"
      and n=n and v="(G n, h n)", OF prefix])
  have preserved: "h n = a" by (rule named_completion_value[OF completion assigned])
  show ?thesis using projected by (simp only: snd_conv preserved)
qed

lemma named_prefix_completion_agree:
  assumes completion: "named_completion D G g h"
    and bound: "n < m" and assigned: "g n = Some a"
  shows "named_untag_assignment (named_prefix_assignment m (\<lambda>i. (G i, h i))) n = g n"
  by (rule trans[OF named_prefix_completion_value[OF completion bound assigned] sym[OF assigned]])

lemma named_prefix_completion_fv_agree:
  assumes completion: "named_completion D G g h"
    and adequate: "named_adequate g A" and support: "named_fv A \<subseteq> {..<m}"
    and free: "n \<in> named_fv A"
  shows "named_untag_assignment (named_prefix_assignment m (\<lambda>i. (G i, h i))) n = g n"
proof -
  obtain a where assigned: "g n = Some a" by (rule named_adequate_value[OF adequate free])
  have bound: "n < m" using subsetD[OF support free] by simp
  show ?thesis by (rule named_prefix_completion_agree[OF completion bound assigned])
qed

end
