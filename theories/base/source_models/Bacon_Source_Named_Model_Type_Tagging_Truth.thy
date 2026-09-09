theory Bacon_Source_Named_Model_Type_Tagging_Truth
  imports Bacon_Source_Named_Model_Type_Tagging Bacon_Source_Named_Tagged_Quantifiers
begin

section \<open>The six primitive truth clauses survive type tagging\<close>

text \<open>
  V′⟦A⟧′ᵍ = V⟦A⟧ᵘⁿᵗᵃᵍ⁽ᵍ⁾. Quantification over D′σ amounts to
  quantification over the second coordinates a ∈ Dσ. Removing assignment
  tags sends an update by ⟨σ,a⟩ to the update by a.
  Source: Bacon–Dorr Definition 3.1(iii.a–f), p.44.

  Representation: the premises are the fields of an arbitrary independent
  paper_named_bbk_model. Only the global tagged-domain quantifier lemmas
  are reused from the earlier construction. Identity compares values of
  the same displayed type, so the common tags do not change equality.

  Status: all six primitive truth clauses, with partial-assignment typing,
  adequacy, and fresh quantifier-variable guards retained. No primitive
  implication operator is identified with a defined connective.
\<close>

context paper_named_bbk_model
begin

lemma model_tag_neg:
  assumes al: "named_in_language paper_logical_type signature stock A Prop"
    and typed: "named_env_typed (named_tag_domain domain) stock g" and ga: "named_adequate g A"
  shows "model_tag_valuation (model_tag_denote g (NApp (NLogical SNot) A)) =
    (\<not> model_tag_valuation (model_tag_denote g A))"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  show ?thesis by (simp only: model_tag_truth;
    rule valuation_neg[OF al named_untag_assignment_typed[OF typed] old_ga])
qed

lemma model_tag_conj:
  assumes al: "named_in_language paper_logical_type signature stock A Prop"
    and bl: "named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  shows "model_tag_valuation (model_tag_denote g (NApp (NApp (NLogical SAnd) A) B)) =
    (model_tag_valuation (model_tag_denote g A) \<and> model_tag_valuation (model_tag_denote g B))"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_gb: "named_adequate (named_untag_assignment g) B"
    by (rule iffD2[OF named_untag_assignment_adequate gb])
  show ?thesis by (simp only: model_tag_truth;
    rule valuation_conj[OF al bl named_untag_assignment_typed[OF typed] old_ga old_gb])
qed

lemma model_tag_disj:
  assumes al: "named_in_language paper_logical_type signature stock A Prop"
    and bl: "named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  shows "model_tag_valuation (model_tag_denote g (NApp (NApp (NLogical SOr) A) B)) =
    (model_tag_valuation (model_tag_denote g A) \<or> model_tag_valuation (model_tag_denote g B))"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_gb: "named_adequate (named_untag_assignment g) B"
    by (rule iffD2[OF named_untag_assignment_adequate gb])
  show ?thesis by (simp only: model_tag_truth;
    rule valuation_disj[OF al bl named_untag_assignment_typed[OF typed] old_ga old_gb])
qed

lemma model_tag_forall:
  assumes language: "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and adequate: "named_adequate g F"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "model_tag_valuation (model_tag_denote g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>v \<in> named_tag_domain domain \<sigma>.
      model_tag_valuation (model_tag_denote (g(n := Some v)) (NApp F (NVar n))))"
proof -
  have old_adequate: "named_adequate (named_untag_assignment g) F"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (denote (named_untag_assignment g) (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_forall[OF language named_untag_assignment_typed[OF typed]
      old_adequate n_type fresh])
  have projected: "(\<forall>v \<in> named_tag_domain domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some (snd v))) (NApp F (NVar n)))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule named_tag_domain_ball_snd[where P="\<lambda>a. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n)))"])
  show ?thesis using old
    by (simp only: model_tag_truth named_untag_assignment_update projected)
qed

lemma model_tag_exists:
  assumes language: "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and adequate: "named_adequate g F"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "model_tag_valuation (model_tag_denote g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>v \<in> named_tag_domain domain \<sigma>.
      model_tag_valuation (model_tag_denote (g(n := Some v)) (NApp F (NVar n))))"
proof -
  have old_adequate: "named_adequate (named_untag_assignment g) F"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (denote (named_untag_assignment g) (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_exists[OF language named_untag_assignment_typed[OF typed]
      old_adequate n_type fresh])
  have projected: "(\<exists>v \<in> named_tag_domain domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some (snd v))) (NApp F (NVar n)))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n))))"
    by (rule named_tag_domain_bex_snd[where P="\<lambda>a. valuation (denote
      ((named_untag_assignment g)(n := Some a)) (NApp F (NVar n)))"])
  show ?thesis using old
    by (simp only: model_tag_truth named_untag_assignment_update projected)
qed

lemma model_tag_identity:
  assumes al: "named_in_language paper_logical_type signature stock A \<sigma>"
    and bl: "named_in_language paper_logical_type signature stock B \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  shows "model_tag_valuation (model_tag_denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (model_tag_denote g A = model_tag_denote g B)"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_gb: "named_adequate (named_untag_assignment g) B"
    by (rule iffD2[OF named_untag_assignment_adequate gb])
  have old: "valuation (denote (named_untag_assignment g) (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (denote (named_untag_assignment g) A = denote (named_untag_assignment g) B)"
    by (rule valuation_identity[OF al bl named_untag_assignment_typed[OF typed] old_ga old_gb])
  have equal_values: "(model_tag_denote g A = model_tag_denote g B) =
    (denote (named_untag_assignment g) A = denote (named_untag_assignment g) B)"
    by (simp only: model_tag_denote_eq[OF al] model_tag_denote_eq[OF bl] prod.inject; simp)
  show ?thesis using old by (simp only: model_tag_truth equal_values)
qed

end

end
