theory Bacon_Parametric_Countable_Model_Existence
  imports Bacon_Parametric_Countable_Model
    Bacon_Parametric_Canonical_Development.Bacon_Parametric_Henkin_Bridge
    Bacon_Parametric_Signature_Development.Bacon_Parametric_BBK_Name_Transport
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Refutation_Consistency
begin

section \<open>Consistent sentence theories over countable names have models in ℕ\<close>

text \<open>
  If S ⊆ ℒ(Σ) is a consistent set of sentences and the original names
  form a countable set, then some BBK model ℳ satisfies S with Dσ ⊆ ℕ
  for every σ.  Source: Bacon–Dorr, Theorem 3.2, pp.44–45,
  countable-signature refinement and p.45 n.64.

  Isabelle representation: the original name type is 'c::countable.
  The checked nested-tree coding proves that its disjoint witness-name
  enlargement is also countable.  Obtain a Henkin extension T, transport
  its canonical model to natural-number codes, and restrict the
  interpretation along PFOriginal.  Domain subsets of ℕ need not equal ℕ.

  Status: the final theorem has only typing and H-consistency premises
  for S.  It assumes a countable ambient name type, not merely countably
  many declared names inside a possibly uncountable ambient type.  No
  claim for uncountable name types is made by this leaf.
\<close>

context pH_countable_closed_Henkin
begin

lemma pHct_nat_pullback_model_exists:
  fixes old_signature :: "'d psignature" and S :: "'d pterm set" and k :: "'d \<Rightarrow> 'c"
  assumes names: "\<And>c \<sigma>. c \<in> old_signature \<sigma> \<Longrightarrow> k c \<in> signature \<sigma>"
    and extends: "image (phenkin_map k) S \<subseteq> T"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'd pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model old_signature D J V \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  let ?J = "pbbk_pullback_denote k pHct_nat_denote"
  have model: "pbbk_model old_signature pHct_nat_domain ?J pHct_nat_holds"
    by (rule pbbk_model_name_pullback[where k=k, OF pHct_nat_model names])
  have subsets: "\<forall>\<sigma>. pHct_nat_domain \<sigma> \<subseteq> UNIV" by (intro allI subset_UNIV)
  have realizes: "\<forall>A \<in> S. \<forall>g. pHct_nat_holds (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have image_member: "phenkin_map k A \<in> image (phenkin_map k) S" by (rule imageI[OF member])
    have mapped_member: "phenkin_map k A \<in> T" by (rule subsetD[OF extends image_member])
    have lang: "pterm_in_language signature [] (phenkin_map k A) Prop"
      by (rule pH_member_language[OF mapped_member])
    have truth: "pHct_nat_holds (pHct_nat_denote g (phenkin_map k A))"
      by (rule iffD2[OF pHct_nat_closed_truth_lemma[OF lang] mapped_member])
    show "pHct_nat_holds (?J g A)" unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=pHct_nat_domain], rule exI[where x="?J"], rule exI[where x=pHct_nat_holds])
    show "pbbk_model old_signature pHct_nat_domain ?J pHct_nat_holds \<and>
      (\<forall>\<sigma>. pHct_nat_domain \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. pHct_nat_holds (?J g A))"
      by (rule conjI[OF model conjI[OF subsets realizes]])
  qed
qed

end

theorem pH_BBK_nat_model_existence:
  fixes \<Sigma> :: "'c::countable psignature" and S :: "'c pterm set"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model \<Sigma> D J V \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  obtain T where extends: "image phenkin_full_embed S \<subseteq> T"
    and canonical: "pH_Henkin_theory (phenkin_full_signature \<Sigma>) [] T"
    and locale_instance: "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (rule phenkin_canonical_Henkin_extension[OF typed consistent])
  interpret Expanded: pH_countable_closed_Henkin "phenkin_full_signature \<Sigma>" T
    by (unfold_locales) (rule canonical)
  have names: "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma>"
    if declared: "c \<in> \<Sigma> \<sigma>" for c \<sigma>
  proof -
    have membership: "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
      by (rule phenkin_full_original_membership)
    show ?thesis by (rule iffD2[OF membership declared])
  qed
  have mapped_extends: "image (phenkin_map PFOriginal) S \<subseteq> T"
    using extends unfolding phenkin_full_embed_def .
  show ?thesis
    by (rule Expanded.pHct_nat_pullback_model_exists[
      where old_signature=\<Sigma> and S=S and k=PFOriginal, OF names mapped_extends])
qed

subsection \<open>Nonderivability has a natural-number countermodel\<close>

text \<open>
  S ⊬H A implies ℳ ⊨ S and ℳ ⊭ A for a BBK model with Dσ ⊆ ℕ,
  provided S and A are sentences over the countable original name type.
  Source: the countable-signature clause of Bacon–Dorr Theorem 3.2.
  Apply model existence to S ∪ {¬A}; the exact negation clause falsifies A
  under every assignment.  This is a countermodel statement, not HOL
  quantification over semantic carrier types.
\<close>

theorem pH_BBK_nat_closed_countermodel:
  fixes \<Sigma> :: "'c::countable psignature" and S :: "'c pterm set" and A :: "'c pterm"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and lang: "pterm_in_language \<Sigma> [] A Prop"
    and not_derivable: "\<not> pH_set_derivable \<Sigma> [] S A"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model \<Sigma> D J V \<and> (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<and> (\<forall>g. \<not> V (J g A))"
proof -
  have A_type: "has_ptype [] A Prop" using lang unfolding pterm_in_language_def by (rule conjunct1)
  have A_sig: "pterm_in_signature \<Sigma> A" using lang unfolding pterm_in_language_def by (rule conjunct2)
  have neg_type: "has_ptype [] (PNeg A) Prop" by (rule has_ptype.PNeg[OF A_type])
  have neg_sig: "pterm_in_signature \<Sigma> (PNeg A)" using A_sig by simp
  have old_typed: "\<forall>B \<in> S. has_ptype [] B Prop \<and> pterm_in_signature \<Sigma> B"
    using typed unfolding pH_typed_theory_def .
  have extended_typed: "pH_typed_theory \<Sigma> [] (insert (PNeg A) S)"
  proof (unfold pH_typed_theory_def, rule ballI)
    fix B
    assume member: "B \<in> insert (PNeg A) S"
    show "has_ptype [] B Prop \<and> pterm_in_signature \<Sigma> B"
    proof (rule insertE[OF member])
      assume eq: "B = PNeg A"
      show ?thesis unfolding eq by (rule conjI[OF neg_type neg_sig])
    next
      assume member: "B \<in> S"
      show ?thesis by (rule bspec[OF old_typed member])
    qed
  qed
  have extended_consistent: "pH_consistent \<Sigma> [] (insert (PNeg A) S)"
    by (rule pH_consistent_neg_of_not_set_derivable[OF A_type A_sig not_derivable])
  obtain D :: "otype \<Rightarrow> nat set" and J :: "(nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat"
    and V :: "nat \<Rightarrow> bool" where model: "pbbk_model \<Sigma> D J V"
      and subsets: "\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV"
      and realizes: "\<forall>B \<in> insert (PNeg A) S. \<forall>g. V (J g B)"
    using pH_BBK_nat_model_existence[OF extended_typed extended_consistent] by (elim exE conjE)
  interpret M: pbbk_model \<Sigma> D J V by (rule model)
  have premise_truths: "\<forall>B \<in> S. \<forall>g. V (J g B)"
  proof (rule ballI)
    fix B
    assume member: "B \<in> S"
    show "\<forall>g. V (J g B)" by (rule bspec[OF realizes insertI2[OF member]])
  qed
  have neg_true: "\<forall>g. V (J g (PNeg A))" by (rule bspec[OF realizes insertI1])
  have conclusion_false: "\<forall>g. \<not> V (J g A)"
  proof (rule allI)
    fix g
    have truth: "V (J g (PNeg A))" by (rule spec[OF neg_true])
    have clause: "V (J g (PNeg A)) = (\<not> V (J g A))"
      by (rule M.valuation_neg[OF A_type A_sig pbbk_env_empty])
    show "\<not> V (J g A)" by (rule iffD1[OF clause truth])
  qed
  show ?thesis
  proof (rule exI[where x=D], rule exI[where x=J], rule exI[where x=V])
    show "pbbk_model \<Sigma> D J V \<and> (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<and> (\<forall>g. \<not> V (J g A))"
      by (rule conjI[OF model conjI[OF subsets conjI[OF premise_truths conclusion_false]]])
  qed
qed

end
