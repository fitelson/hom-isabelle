theory Bacon_H_BBK_Countable_Completeness
  imports Bacon_H_BBK_Countable_Model
begin

section \<open>Bacon--Dorr Theorem 3.2: closed completeness on the naturals\<close>

text \<open>
  ⊢ₕ A ⇔ ∀𝔐 with Dσ ⊆ ℕ, 𝔐 ⊨ A, for typed closed A. Bacon–Dorr, Theorem 3.2, pp.
  44–45, countable-domain refinement.

  Isabelle representation: An unprovable sentence has a canonical countermodel whose
  domains and interpretation are transported to natural-number codes.

  Status: Closed-sentence completeness over F and universal string names. Arbitrary
  starting theories are handled in Countable_Arbitrary_Model.
\<close>

theorem H_BBK_nat_closed_countermodel:
  assumes typed: "[] \<turnstile> A : Prop" and unprovable: "\<not> [] \<turnstile>\<^sub>H A"
  obtains D :: "otype \<Rightarrow> nat set"
    and J :: "(nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> nat"
    and V :: "nat \<Rightarrow> bool"
  where "bbk_model (\<lambda>_. UNIV) D J V"
    and "\<forall>\<sigma>. D \<sigma> \<subseteq> (UNIV :: nat set)"
    and "\<forall>g. \<not> V (J g A)"
proof -
  obtain body_enum where bodies: "enumerates_witness_bodies [] body_enum"
    using enumerates_witness_bodies_exists[where \<Gamma>="[]"] by (elim exE)
  obtain formula_enum where formulas: "enumerates_formulas [] formula_enum"
    using enumerates_formulas_exists[where \<Gamma>="[]"] by (elim exE)
  obtain U where henkin_U: "H_Henkin_theory [] U" and neg_in: "Neg A \<in> U"
    by (rule H_canonical_Henkin_theory_for_unprovable_staged
      [OF typed unprovable bodies formulas])
  have not_in: "A \<notin> U" by (rule iffD1[OF H_Henkin_neg_mem_iff[OF henkin_U typed] neg_in])
  interpret C: H_closed_Henkin U by (unfold_locales) (rule henkin_U)
  let ?D = "H_closed_Henkin.H_BBK_nat_domain U"
  let ?J = "H_closed_Henkin.H_BBK_nat_denote U"
  let ?V = "H_closed_Henkin.H_BBK_nat_holds U"
  have model: "bbk_model (\<lambda>_. UNIV) ?D ?J ?V" by (rule C.H_BBK_nat_model)
  have domains: "\<forall>\<sigma>. ?D \<sigma> \<subseteq> (UNIV :: nat set)"
    by (rule allI) (rule C.H_BBK_nat_domain_subset_nat)
  have falsifies: "\<forall>g. \<not> ?V (?J g A)"
  proof (rule allI)
    fix g
    show "\<not> ?V (?J g A)"
    proof
      assume true_at: "?V (?J g A)"
      have member: "A \<in> U"
        by (rule iffD1[OF C.H_BBK_nat_closed_truth_lemma[OF typed] true_at])
      show False by (rule notE[OF not_in member])
    qed
  qed
  show thesis
    by (rule that[where D="?D" and J="?J" and V="?V", OF model domains falsifies])
qed

theorem H_BBK_nat_closed_valid_iff_proves:
  "H_BBK_closed_valid TYPE(nat) A \<longleftrightarrow> [] \<turnstile>\<^sub>H A"
proof
  assume valid: "H_BBK_closed_valid TYPE(nat) A"
  have typed: "[] \<turnstile> A : Prop" by (rule H_BBK_closed_valid_typed[OF valid])
  show "[] \<turnstile>\<^sub>H A"
  proof (rule ccontr)
    assume unprovable: "\<not> [] \<turnstile>\<^sub>H A"
    obtain D :: "otype \<Rightarrow> nat set"
      and J :: "(nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> nat"
      and V :: "nat \<Rightarrow> bool"
      where model: "bbk_model (\<lambda>_. UNIV) D J V"
        and domains: "\<forall>\<sigma>. D \<sigma> \<subseteq> (UNIV :: nat set)"
        and falsifies: "\<forall>g. \<not> V (J g A)"
      by (rule H_BBK_nat_closed_countermodel[OF typed unprovable])
    have all_true: "\<forall>g. V (J g A)" by (rule H_BBK_closed_validD[OF valid model])
    have true_at: "V (J (\<lambda>_. 0) A)" by (rule spec[OF all_true])
    have false_at: "\<not> V (J (\<lambda>_. 0) A)" by (rule spec[OF falsifies])
    show False by (rule notE[OF false_at true_at])
  qed
next
  assume derivation: "[] \<turnstile>\<^sub>H A"
  show "H_BBK_closed_valid TYPE(nat) A" by (rule H_BBK_closed_soundness[OF derivation])
qed

corollary H_BBK_nat_closed_valid_every_carrier:
  assumes valid: "H_BBK_closed_valid TYPE(nat) A"
  shows "H_BBK_closed_valid TYPE('v) A"
proof -
  have derivation: "[] \<turnstile>\<^sub>H A"
    by (rule iffD1[OF H_BBK_nat_closed_valid_iff_proves valid])
  show ?thesis by (rule H_BBK_closed_soundness[OF derivation])
qed

end
