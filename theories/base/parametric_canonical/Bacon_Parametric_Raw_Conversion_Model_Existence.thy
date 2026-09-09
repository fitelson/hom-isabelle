theory Bacon_Parametric_Raw_Conversion_Model_Existence
  imports Bacon_Parametric_BBK_Model_Existence Bacon_Parametric_Inhabited_Conversion
begin

section \<open>Constructed models preserve unrestricted βη conversion\<close>

text \<open>
  For M,N ∈ ℒ(Σ), raw M ≡βη N implies ⟦M⟧g = ⟦N⟧g in the
  models constructed below, even if the given conversion passes through
  terms outside ℒ(Σ).  Source role: discharges the stronger reading of
  Bacon–Dorr Definition 3.1(ii.d), pp.43–44, for the model-existence
  construction of Theorem 3.2, pp.44–45 and p.45 n.64.

  Isabelle representation: the extra property is a separate predicate,
  not a change to pbbk_model.  An inhabited target signature converts a
  raw chain into an in-signature chain.  Constant-name pullback preserves
  the extra property, even when the original signature lacks closed
  inhabitants.  Thus the final model-existence theorem does not rely on
  choosing between the two readings of intermediate signature guards.

  Status: arbitrary original name and semantic carrier types in the
  transport lemmas; the final existence theorem uses the already specified
  enlarged canonical carrier.  No countability or Functionality is assumed.
\<close>

definition pbbk_preserves_raw_conversion ::
  "'c psignature \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ((nat \<Rightarrow> 'v) \<Rightarrow> 'c pterm \<Rightarrow> 'v) \<Rightarrow> bool" where
  "pbbk_preserves_raw_conversion \<Sigma> D J \<longleftrightarrow>
    (\<forall>\<Gamma> \<tau> M N g. pbeta_eta_equiv \<Gamma> \<tau> M N \<longrightarrow>
      pterm_in_signature \<Sigma> M \<longrightarrow> pterm_in_signature \<Sigma> N \<longrightarrow>
      pbbk_env_typed D \<Gamma> g \<longrightarrow> J g M = J g N)"

lemma pbbk_preserves_raw_conversionD:
  assumes property: "pbbk_preserves_raw_conversion \<Sigma> D J"
    and raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
    and env: "pbbk_env_typed D \<Gamma> g"
  shows "J g M = J g N"
  using assms unfolding pbbk_preserves_raw_conversion_def by blast

lemma pbbk_inhabited_preserves_raw_conversion:
  assumes model: "pbbk_model \<Sigma> D J V"
    and inhabitants: "\<And>\<sigma>. \<exists>W. pterm_in_language \<Sigma> [] W \<sigma>"
  shows "pbbk_preserves_raw_conversion \<Sigma> D J"
proof (unfold pbbk_preserves_raw_conversion_def, intro allI impI)
  fix \<Gamma> \<tau> M N g
  assume raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
    and env: "pbbk_env_typed D \<Gamma> g"
  interpret Target: pbbk_model \<Sigma> D J V by (rule model)
  have indexed: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
    by (rule pbeta_eta_raw_to_inhabited_signature[OF inhabitants raw ms ns])
  show "J g M = J g N" by (rule Target.denote_beta_eta[OF indexed ms ns env])
qed

subsection \<open>Pullback retains the stronger conversion property\<close>

text \<open>
  Set ⟦A⟧pull,g = ⟦k(A)⟧target,g.  A raw conversion of A to B gives a
  raw conversion of k(A) to k(B), while endpoint language guards follow
  from k[Σσ] ⊆ Δσ.  The domain and typed assignments are unchanged.
  This is the signature-restriction step in the cited model construction.
\<close>

lemma pbbk_raw_conversion_name_pullback:
  fixes k :: "'c \<Rightarrow> 'd"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'd pterm \<Rightarrow> 'v"
  assumes property: "pbbk_preserves_raw_conversion \<Delta> D J"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pbbk_preserves_raw_conversion \<Sigma> D (pbbk_pullback_denote k J)"
proof (unfold pbbk_preserves_raw_conversion_def, intro allI impI)
  fix \<Gamma> \<tau> M N g
  assume raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
    and env: "pbbk_env_typed D \<Gamma> g"
  have mapped: "pbeta_eta_equiv \<Gamma> \<tau> (phenkin_map k M) (phenkin_map k N)"
    by (rule pbbk_name_map_conversion[OF raw])
  have mapped_ms: "pterm_in_signature \<Delta> (phenkin_map k M)"
    by (rule phenkin_map_signature[OF ms names])
  have mapped_ns: "pterm_in_signature \<Delta> (phenkin_map k N)"
    by (rule phenkin_map_signature[OF ns names])
  have eq: "J g (phenkin_map k M) = J g (phenkin_map k N)"
    by (rule pbbk_preserves_raw_conversionD[OF property mapped mapped_ms mapped_ns env])
  show "pbbk_pullback_denote k J g M = pbbk_pullback_denote k J g N"
    unfolding pbbk_pullback_denote_def by (rule eq)
qed

corollary pbbk_inhabited_name_pullback_raw:
  assumes model: "pbbk_model \<Delta> D J V"
    and inhabitants: "\<And>\<sigma>. \<exists>W. pterm_in_language \<Delta> [] W \<sigma>"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pbbk_model \<Sigma> D (pbbk_pullback_denote k J) V \<and>
    pbbk_preserves_raw_conversion \<Sigma> D (pbbk_pullback_denote k J)"
proof -
  have target_raw: "pbbk_preserves_raw_conversion \<Delta> D J"
    by (rule pbbk_inhabited_preserves_raw_conversion[OF model inhabitants])
  have pulled_model: "pbbk_model \<Sigma> D (pbbk_pullback_denote k J) V"
    by (rule pbbk_model_name_pullback[where k=k, OF model names])
  have pulled_raw: "pbbk_preserves_raw_conversion \<Sigma> D (pbbk_pullback_denote k J)"
    by (rule pbbk_raw_conversion_name_pullback[where k=k, OF target_raw names])
  show ?thesis by (rule conjI[OF pulled_model pulled_raw])
qed

context pH_closed_Henkin
begin

lemma pHc_preserves_raw_conversion:
  "pbbk_preserves_raw_conversion signature pHc_domain pHc_denote"
  by (rule pbbk_inhabited_preserves_raw_conversion[OF pHc_is_pbbk_model pHc_closed_inhabited])

lemma pHc_denote_raw_beta_eta:
  assumes raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M = pHc_denote g N"
  by (rule pbbk_preserves_raw_conversionD[OF pHc_preserves_raw_conversion raw ms ns env])

lemma pHc_pullback_model_exists_with_raw_conversion:
  fixes old_signature :: "'d psignature" and S :: "'d pterm set" and k :: "'d \<Rightarrow> 'c"
  assumes names: "\<And>c \<sigma>. c \<in> old_signature \<sigma> \<Longrightarrow> k c \<in> signature \<sigma>"
    and extends: "image (phenkin_map k) S \<subseteq> T"
  shows "\<exists>D :: otype \<Rightarrow> 'c pHc_value set.
    \<exists>J :: (nat \<Rightarrow> 'c pHc_value) \<Rightarrow> 'd pterm \<Rightarrow> 'c pHc_value.
    \<exists>V :: 'c pHc_value \<Rightarrow> bool.
      pbbk_model old_signature D J V \<and> pbbk_preserves_raw_conversion old_signature D J \<and>
      (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  let ?J = "pbbk_pullback_denote k pHc_denote"
  have model: "pbbk_model old_signature pHc_domain ?J pHc_holds"
    by (rule pbbk_model_name_pullback[where k=k, OF pHc_is_pbbk_model names])
  have raw_property: "pbbk_preserves_raw_conversion old_signature pHc_domain ?J"
    by (rule pbbk_raw_conversion_name_pullback[where k=k, OF pHc_preserves_raw_conversion names])
  have realizes: "\<forall>A \<in> S. \<forall>g. pHc_holds (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have mapped_image: "phenkin_map k A \<in> image (phenkin_map k) S" by (rule imageI[OF member])
    have mapped_member: "phenkin_map k A \<in> T" by (rule subsetD[OF extends mapped_image])
    have lang: "pterm_in_language signature [] (phenkin_map k A) Prop"
      by (rule pH_member_language[OF mapped_member])
    have truth: "pHc_holds (pHc_denote g (phenkin_map k A))"
      by (rule iffD2[OF pHc_closed_truth_lemma[OF lang] mapped_member])
    show "pHc_holds (?J g A)" unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=pHc_domain], rule exI[where x="?J"], rule exI[where x=pHc_holds])
    show "pbbk_model old_signature pHc_domain ?J pHc_holds \<and>
      pbbk_preserves_raw_conversion old_signature pHc_domain ?J \<and>
      (\<forall>A \<in> S. \<forall>g. pHc_holds (?J g A))"
      by (rule conjI[OF model conjI[OF raw_property realizes]])
  qed
qed

end

subsection \<open>Model existence under either conversion reading\<close>

text \<open>
  ConH(S) yields ℳ ⊨ S with the raw-conversion property just defined.
  Source: Bacon–Dorr Theorem 3.2 and Definition 3.1(ii.d).
  The original signature need not be inhabited: closed inhabitants are
  used only in its constructed Henkin enlargement, before pullback.
  The conclusion is existence on the displayed carrier, not quantification
  over all HOL carrier types or an assertion about every BBK model.
\<close>

theorem pH_BBK_model_existence_with_raw_conversion:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
      pbbk_model \<Sigma> D J V \<and> pbbk_preserves_raw_conversion \<Sigma> D J \<and>
      (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  obtain T where extends: "image phenkin_full_embed S \<subseteq> T"
    and canonical: "pH_Henkin_theory (phenkin_full_signature \<Sigma>) [] T"
    and locale_instance: "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (rule phenkin_canonical_Henkin_extension[OF typed consistent])
  interpret Expanded: pH_closed_Henkin "phenkin_full_signature \<Sigma>" T by (rule locale_instance)
  have names: "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma>"
    if declared: "c \<in> \<Sigma> \<sigma>" for c \<sigma>
  proof -
    have membership: "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
      by (rule phenkin_full_original_membership)
    show ?thesis by (rule iffD2[OF membership declared])
  qed
  have mapped_extends: "image (phenkin_map PFOriginal) S \<subseteq> T"
    using extends unfolding phenkin_full_embed_def .
  show ?thesis by (rule Expanded.pHc_pullback_model_exists_with_raw_conversion[
    where old_signature=\<Sigma> and S=S and k=PFOriginal, OF names mapped_extends])
qed

end
