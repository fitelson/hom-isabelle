theory Bacon_Parametric_Countable_Raw_Model_Existence
  imports Bacon_Parametric_Countable_Model_Existence Bacon_Parametric_Declared_Signature_Coding
    Bacon_Parametric_Canonical_Development.Bacon_Parametric_Raw_Conversion_Model_Existence
begin

section \<open>Natural-number models with the stronger conversion property\<close>

text \<open>
  Countable ⋃σΣσ and ConH(S) yield a BBK model ℳ ⊨ S with Dσ ⊆ ℕ,
  preserving raw βη conversion between endpoints in ℒ(Σ).  Source role:
  Bacon–Dorr Theorem 3.2, pp.44–45, countable-signature refinement, with
  the endpoint-only reading of Definition 3.1(ii.d).

  Isabelle representation: an inhabited Henkin signature gives the extra
  raw-conversion property for the already checked natural-number model.
  Both PFOriginal pullback and declared-name coding retain this property.
  No model field or earlier definition is changed.  The final theorem
  assumes countability only of the declared-name union, not the ambient
  name type, and does not assume that every BBK model has this property.
\<close>

context pH_countable_closed_Henkin
begin

lemma pHct_nat_preserves_raw_conversion:
  "pbbk_preserves_raw_conversion signature pHct_nat_domain pHct_nat_denote"
  by (rule pbbk_inhabited_preserves_raw_conversion[OF pHct_nat_model pHc_closed_inhabited])

lemma pHct_nat_denote_raw_beta_eta:
  assumes raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  shows "pHct_nat_denote g M = pHct_nat_denote g N"
  by (rule pbbk_preserves_raw_conversionD[OF pHct_nat_preserves_raw_conversion raw ms ns env])

lemma pHct_nat_pullback_model_exists_with_raw_conversion:
  fixes old_signature :: "'d psignature" and S :: "'d pterm set" and k :: "'d \<Rightarrow> 'c"
  assumes names: "\<And>c \<sigma>. c \<in> old_signature \<sigma> \<Longrightarrow> k c \<in> signature \<sigma>"
    and extends: "image (phenkin_map k) S \<subseteq> T"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'd pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model old_signature D J V \<and>
      pbbk_preserves_raw_conversion old_signature D J \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  let ?J = "pbbk_pullback_denote k pHct_nat_denote"
  have model: "pbbk_model old_signature pHct_nat_domain ?J pHct_nat_holds"
    by (rule pbbk_model_name_pullback[where k=k, OF pHct_nat_model names])
  have raw_property: "pbbk_preserves_raw_conversion old_signature pHct_nat_domain ?J"
    by (rule pbbk_raw_conversion_name_pullback[where k=k, OF pHct_nat_preserves_raw_conversion names])
  have subsets: "\<forall>\<sigma>. pHct_nat_domain \<sigma> \<subseteq> UNIV" by (intro allI subset_UNIV)
  have realizes: "\<forall>A \<in> S. \<forall>g. pHct_nat_holds (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have mapped_image: "phenkin_map k A \<in> image (phenkin_map k) S" by (rule imageI[OF member])
    have mapped_member: "phenkin_map k A \<in> T" by (rule subsetD[OF extends mapped_image])
    have lang: "pterm_in_language signature [] (phenkin_map k A) Prop"
      by (rule pH_member_language[OF mapped_member])
    have truth: "pHct_nat_holds (pHct_nat_denote g (phenkin_map k A))"
      by (rule iffD2[OF pHct_nat_closed_truth_lemma[OF lang] mapped_member])
    show "pHct_nat_holds (?J g A)" unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=pHct_nat_domain], rule exI[where x="?J"], rule exI[where x=pHct_nat_holds])
    show "pbbk_model old_signature pHct_nat_domain ?J pHct_nat_holds \<and>
      pbbk_preserves_raw_conversion old_signature pHct_nat_domain ?J \<and>
      (\<forall>\<sigma>. pHct_nat_domain \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. pHct_nat_holds (?J g A))"
      by (rule conjI[OF model conjI[OF raw_property conjI[OF subsets realizes]]])
  qed
qed

end

subsection \<open>Countable ambient name types\<close>

theorem pH_BBK_nat_model_existence_with_raw_conversion:
  fixes \<Sigma> :: "'c::countable psignature" and S :: "'c pterm set"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model \<Sigma> D J V \<and> pbbk_preserves_raw_conversion \<Sigma> D J \<and>
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
  show ?thesis by (rule Expanded.pHct_nat_pullback_model_exists_with_raw_conversion[
    where old_signature=\<Sigma> and S=S and k=PFOriginal, OF names mapped_extends])
qed

subsection \<open>Countable declared signatures in arbitrary name types\<close>

text \<open>
  Encode the countable union ⋃σΣσ into ℕ.  Proof reflection gives
  ConH(e(S)); its natural-number model preserves raw conversion.  Pulling
  back along e retains both the model fields and the raw-conversion
  property.  This is the exact declared-signature cardinality qualification
  in the countable clause of Bacon–Dorr Theorem 3.2.
\<close>

context pH_countable_signature
begin

lemma pHdecl_nat_model_existence_with_raw_conversion:
  assumes typed: "pH_typed_theory signature [] S" and consistent: "pH_consistent signature [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model signature D J V \<and>
      pbbk_preserves_raw_conversion signature D J \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  have encoded_typed: "pH_typed_theory pHdecl_signature [] (phenkin_map pHdecl_code ` S)"
    by (rule pHdecl_encoded_typed[OF typed])
  have encoded_consistent: "pH_consistent pHdecl_signature [] (phenkin_map pHdecl_code ` S)"
    by (rule pHdecl_encoded_consistent[OF typed consistent])
  obtain D :: "otype \<Rightarrow> nat set" and J :: "(nat \<Rightarrow> nat) \<Rightarrow> nat pterm \<Rightarrow> nat"
    and V :: "nat \<Rightarrow> bool" where encoded_model: "pbbk_model pHdecl_signature D J V"
      and encoded_raw: "pbbk_preserves_raw_conversion pHdecl_signature D J"
      and subsets: "\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV"
      and encoded_truths: "\<forall>B \<in> phenkin_map pHdecl_code ` S. \<forall>g. V (J g B)"
    using pH_BBK_nat_model_existence_with_raw_conversion[OF encoded_typed encoded_consistent]
    by (elim exE conjE)
  let ?J = "pbbk_pullback_denote pHdecl_code J"
  have model: "pbbk_model signature D ?J V"
    by (rule pbbk_model_name_pullback[where k=pHdecl_code, OF encoded_model pHdecl_encode_name])
  have raw_property: "pbbk_preserves_raw_conversion signature D ?J"
    by (rule pbbk_raw_conversion_name_pullback[where k=pHdecl_code, OF encoded_raw pHdecl_encode_name])
  have realizes: "\<forall>A \<in> S. \<forall>g. V (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have encoded_member: "phenkin_map pHdecl_code A \<in> phenkin_map pHdecl_code ` S" by (rule imageI[OF member])
    have all_assignments: "\<forall>h. V (J h (phenkin_map pHdecl_code A))"
      by (rule bspec[OF encoded_truths encoded_member])
    have truth: "V (J g (phenkin_map pHdecl_code A))" by (rule spec[OF all_assignments])
    show "V (?J g A)" unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=D], rule exI[where x="?J"], rule exI[where x=V])
    show "pbbk_model signature D ?J V \<and> pbbk_preserves_raw_conversion signature D ?J \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (?J g A))"
      by (rule conjI[OF model conjI[OF raw_property conjI[OF subsets realizes]]])
  qed
qed

end

theorem pH_BBK_countable_signature_model_existence_with_raw_conversion:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model \<Sigma> D J V \<and> pbbk_preserves_raw_conversion \<Sigma> D J \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  interpret Code: pH_countable_signature \<Sigma> by (unfold_locales) (rule countable_signature)
  show ?thesis by (rule Code.pHdecl_nat_model_existence_with_raw_conversion[OF typed consistent])
qed

end
