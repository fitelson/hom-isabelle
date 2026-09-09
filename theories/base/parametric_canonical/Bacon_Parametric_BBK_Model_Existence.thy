theory Bacon_Parametric_BBK_Model_Existence
  imports Bacon_Parametric_Canonical_Model Bacon_Parametric_Henkin_Bridge
    Bacon_Parametric_Signature_Development.Bacon_Parametric_BBK_Name_Transport
begin

section \<open>Every consistent sentence theory has a BBK model\<close>

text \<open>
  If S ⊆ ℒ(Σ) consists of sentences and S is H-consistent, there is a
  BBK model ℳ of Σ with ℳ ⊨ S.  Enlarge Σ to Σ⁺, extend ι(S) to a
  maximal consistent Henkin theory T, and form its canonical model ℳ⁺.
  On the original language put ⟦A⟧g = ⟦ι(A)⟧⁺g; keep the same domains
  and valuation.  Source: Bacon–Dorr, Theorem 3.2, pp.44–45, especially
  p.45 n.64; Bacon, Theorem 15.3, pp.320–321.

  Isabelle representation: arbitrary constant names have type 'c.
  PFOriginal embeds them in the disjoint inductive witness-name carrier.
  The resulting values are tagged sets of terms over that enlarged
  carrier.  The original signature need not contain fresh constants or
  name every member of a semantic domain.

  Status: the conclusion below is model existence, not yet a separately
  packaged strong-completeness equivalence.  Neither the signature nor S
  is assumed countable.  No Functionality or pointwise identification of
  operations is used, and no countable-domain refinement is asserted.
\<close>

context pH_closed_Henkin
begin

subsection \<open>The closed truth lemma\<close>

text \<open>
  For a sentence A of ℒ(Σ), val(⟦A⟧g) = 1 iff A ∈ T, for every g.
  The assignment is immaterial because A is closed.  This is the closed
  instance of the truth lemma in the canonical construction just cited.
\<close>

lemma pHc_closed_truth_lemma:
  assumes lang: "pterm_in_language signature [] A Prop"
  shows "pHc_holds (pHc_denote g A) \<longleftrightarrow> A \<in> T"
proof -
  have typed: "has_ptype [] A Prop"
    using lang unfolding pterm_in_language_def by (rule conjunct1)
  show ?thesis
    by (simp only: pHc_denote_closed[OF typed] pHc_holds_class[OF lang])
qed

subsection \<open>Restricting a canonical model along a name map\<close>

text \<open>
  If k sends the constants of Σ₀ to declared constants of Σ and k(S) ⊆ T,
  the pullback of the canonical model satisfies every member of S.
  This is the restriction to the original language in the model-existence
  proof.  The helper is conditional on the present Henkin theory T; the
  theorem below supplies T using the checked witness construction.
\<close>

lemma pHc_pullback_model_exists:
  fixes old_signature :: "'d psignature" and S :: "'d pterm set"
    and k :: "'d \<Rightarrow> 'c"
  assumes names: "\<And>c \<sigma>. c \<in> old_signature \<sigma> \<Longrightarrow> k c \<in> signature \<sigma>"
    and extends: "image (phenkin_map k) S \<subseteq> T"
  shows "\<exists>D :: otype \<Rightarrow> 'c pHc_value set.
    \<exists>J :: (nat \<Rightarrow> 'c pHc_value) \<Rightarrow> 'd pterm \<Rightarrow> 'c pHc_value.
    \<exists>V :: 'c pHc_value \<Rightarrow> bool.
      pbbk_model old_signature D J V \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  let ?J = "pbbk_pullback_denote k pHc_denote"
  have model: "pbbk_model old_signature pHc_domain ?J pHc_holds"
    by (rule pbbk_model_name_pullback[where k=k,
          OF pHc_is_pbbk_model names])
  have realizes: "\<forall>A \<in> S. \<forall>g. pHc_holds (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have image_member: "phenkin_map k A \<in> image (phenkin_map k) S"
      by (rule imageI[OF member])
    have mapped_member: "phenkin_map k A \<in> T"
      by (rule subsetD[OF extends image_member])
    have mapped_lang: "pterm_in_language signature [] (phenkin_map k A) Prop"
      by (rule pH_member_language[OF mapped_member])
    have truth: "pHc_holds (pHc_denote g (phenkin_map k A))"
      by (rule iffD2[OF pHc_closed_truth_lemma[OF mapped_lang] mapped_member])
    show "pHc_holds (?J g A)"
      unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=pHc_domain], rule exI[where x="?J"],
      rule exI[where x=pHc_holds])
    show "pbbk_model old_signature pHc_domain ?J pHc_holds \<and>
      (\<forall>A \<in> S. \<forall>g. pHc_holds (?J g A))"
      by (rule conjI[OF model realizes])
  qed
qed

end

subsection \<open>Arbitrary-signature model existence\<close>

text \<open>
  H-consistency of S implies ℳ ⊨ S for some BBK model ℳ of Σ.
  Source: Bacon–Dorr, Theorem 3.2; Bacon, Theorem 15.3.

  The two hypotheses say precisely that S is a set of closed formulas of
  ℒ(Σ) and that no finite-support H derivation from S yields absurdity.
  All assignments are quantified in the conclusion; no assignment guard
  is needed for sentences.  Existence of T, all canonical model fields,
  and restriction along PFOriginal are proof dependencies, not additional
  assumptions of this theorem.
\<close>

theorem pH_BBK_model_existence:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set"
  assumes typed: "pH_typed_theory \<Sigma> [] S"
    and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
      pbbk_model \<Sigma> D J V \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  have extension: "\<exists>T. image phenkin_full_embed S \<subseteq> T \<and>
      pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (rule phenkin_canonical_Henkin_exists[OF typed consistent])
  from extension obtain T where extends: "image phenkin_full_embed S \<subseteq> T"
    and locale_instance: "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (elim exE conjE)
  interpret Expanded: pH_closed_Henkin "phenkin_full_signature \<Sigma>" T
    by (rule locale_instance)
  have names: "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma>"
    if declared: "c \<in> \<Sigma> \<sigma>" for c \<sigma>
  proof -
    have membership:
      "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
      by (rule phenkin_full_original_membership)
    show ?thesis by (rule iffD2[OF membership declared])
  qed
  have mapped_extends: "image (phenkin_map PFOriginal) S \<subseteq> T"
    using extends unfolding phenkin_full_embed_def .
  show ?thesis
    by (rule Expanded.pHc_pullback_model_exists[
          where old_signature=\<Sigma> and S=S and k=PFOriginal,
          OF names mapped_extends])
qed

end
