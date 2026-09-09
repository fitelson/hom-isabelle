theory Bacon_Parametric_Raw_Strong_Completeness
  imports Bacon_Parametric_Raw_Conversion_Model_Existence Bacon_Parametric_BBK_Strong_Completeness
begin

section \<open>Countermodels preserving raw βη conversion\<close>

text \<open>
  S ⊬H A yields a BBK model ℳ with ℳ ⊨ S, ℳ ⊭ A, and
  ⟦M⟧g = ⟦N⟧g whenever the guarded endpoints M,N are raw
  βη-equivalent.  Apply the strengthened model-existence theorem to
  S ∪ {¬A}, then use the exact negation clause.

  Source role: Bacon–Dorr Theorem 3.2, pp.44–45 and p.45 n.64, with
  the stronger endpoint-only reading of Definition 3.1(ii.d).
  Isabelle representation: pbbk_model is unchanged; the additional raw
  conversion predicate is retained as a separate conclusion.  The name
  type and S need not be countable, and Σ need not be inhabited.
\<close>

theorem pH_BBK_raw_closed_countermodel:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set" and A :: "'c pterm"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and lang: "pterm_in_language \<Sigma> [] A Prop"
    and not_derivable: "\<not> pH_set_derivable \<Sigma> [] S A"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
      pbbk_model \<Sigma> D J V \<and> pbbk_preserves_raw_conversion \<Sigma> D J \<and>
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
      assume old_member: "B \<in> S"
      show ?thesis by (rule bspec[OF old_typed old_member])
    qed
  qed
  have extended_consistent: "pH_consistent \<Sigma> [] (insert (PNeg A) S)"
    by (rule pH_consistent_neg_of_not_set_derivable[OF A_type A_sig not_derivable])
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and J :: "(nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value"
    and V :: "('c phenkin_full_name) pHc_value \<Rightarrow> bool"
    where model: "pbbk_model \<Sigma> D J V" and raw_property: "pbbk_preserves_raw_conversion \<Sigma> D J"
      and realizes: "\<forall>B \<in> insert (PNeg A) S. \<forall>g. V (J g B)"
    using pH_BBK_model_existence_with_raw_conversion[OF extended_typed extended_consistent]
    by (elim exE conjE)
  interpret M: pbbk_model \<Sigma> D J V by (rule model)
  have premise_truths: "\<forall>B \<in> S. \<forall>g. V (J g B)"
  proof (rule ballI)
    fix B
    assume member: "B \<in> S"
    show "\<forall>g. V (J g B)" by (rule bspec[OF realizes insertI2[OF member]])
  qed
  have neg_true: "\<forall>g. V (J g (PNeg A))" by (rule bspec[OF realizes insertI1])
  have falsifies: "\<forall>g. \<not> V (J g A)"
  proof (rule allI)
    fix g
    have truth: "V (J g (PNeg A))" by (rule spec[OF neg_true])
    have clause: "V (J g (PNeg A)) = (\<not> V (J g A))"
      by (rule M.valuation_neg[OF A_type A_sig pbbk_env_empty])
    show "\<not> V (J g A)" by (rule iffD1[OF clause truth])
  qed
  show ?thesis
  proof (rule exI[where x=D], rule exI[where x=J], rule exI[where x=V])
    show "pbbk_model \<Sigma> D J V \<and> pbbk_preserves_raw_conversion \<Sigma> D J \<and>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<and> (\<forall>g. \<not> V (J g A))"
      by (rule conjI[OF model conjI[OF raw_property conjI[OF premise_truths falsifies]]])
  qed
qed

section \<open>Strong completeness with the stronger conversion condition\<close>

text \<open>
  S ⊢H A iff every BBK structure on the enlarged canonical carrier that
  preserves raw βη conversion and satisfies S also satisfies A.
  Source: the sentence-consequence form of Bacon–Dorr Theorem 3.2.

  Isabelle representation: quantification is over D,J,V on the specified
  carrier, not over HOL types.  The soundness direction uses the existing
  theorem for arbitrary semantic carrier types; it needs no additional
  raw-conversion assumption.  The converse uses the countermodel above.
  This establishes the equivalence under either conversion reading without
  altering the BBK locale or assuming that every BBK model has the stronger
  property.  No claim about full function spaces is made.
\<close>

definition pH_BBK_raw_canonical_consequence ::
  "'c psignature \<Rightarrow> 'c pterm set \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pH_BBK_raw_canonical_consequence \<Sigma> S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
     \<forall>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
       'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
     \<forall>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
       pbbk_model \<Sigma> D J V \<longrightarrow> pbbk_preserves_raw_conversion \<Sigma> D J \<longrightarrow>
       (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A)))"

theorem pH_BBK_raw_closed_strong_completeness:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set" and A :: "'c pterm"
  assumes typed: "pH_typed_theory \<Sigma> [] S" and lang: "pterm_in_language \<Sigma> [] A Prop"
  shows "pH_set_derivable \<Sigma> [] S A \<longleftrightarrow> pH_BBK_raw_canonical_consequence \<Sigma> S A"
proof (rule iffI)
  assume derivation: "pH_set_derivable \<Sigma> [] S A"
  show "pH_BBK_raw_canonical_consequence \<Sigma> S A"
  proof (unfold pH_BBK_raw_canonical_consequence_def, intro allI)
    fix D J V
    show "pbbk_model \<Sigma> D J V \<longrightarrow> pbbk_preserves_raw_conversion \<Sigma> D J \<longrightarrow>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
    proof (intro impI)
      assume model: "pbbk_model \<Sigma> D J V" and raw_property: "pbbk_preserves_raw_conversion \<Sigma> D J"
        and premise_truths: "\<forall>B \<in> S. \<forall>g. V (J g B)"
      show "\<forall>g. V (J g A)" by (rule pH_set_BBK_closed_soundness[OF model derivation premise_truths])
    qed
  qed
next
  assume consequence: "pH_BBK_raw_canonical_consequence \<Sigma> S A"
  show "pH_set_derivable \<Sigma> [] S A"
  proof (rule ccontr)
    assume not_derivable: "\<not> pH_set_derivable \<Sigma> [] S A"
    obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
      and J :: "(nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
        'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value"
      and V :: "('c phenkin_full_name) pHc_value \<Rightarrow> bool"
      where model: "pbbk_model \<Sigma> D J V" and raw_property: "pbbk_preserves_raw_conversion \<Sigma> D J"
        and premise_truths: "\<forall>B \<in> S. \<forall>g. V (J g B)" and falsifies: "\<forall>g. \<not> V (J g A)"
      using pH_BBK_raw_closed_countermodel[OF typed lang not_derivable] by (elim exE conjE)
    have all_models: "\<forall>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
      \<forall>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
        'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
      \<forall>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
        pbbk_model \<Sigma> D J V \<longrightarrow> pbbk_preserves_raw_conversion \<Sigma> D J \<longrightarrow>
        (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
      using consequence unfolding pH_BBK_raw_canonical_consequence_def .
    have this_model: "pbbk_model \<Sigma> D J V \<longrightarrow> pbbk_preserves_raw_conversion \<Sigma> D J \<longrightarrow>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
      by (rule spec[where x=V, OF spec[where x=J, OF spec[where x=D, OF all_models]]])
    have satisfies_A: "\<forall>g. V (J g A)"
      by (rule mp[OF mp[OF mp[OF this_model model] raw_property] premise_truths])
    have yes: "V (J (\<lambda>_. undefined) A)" by (rule spec[OF satisfies_A])
    have no: "\<not> V (J (\<lambda>_. undefined) A)" by (rule spec[OF falsifies])
    show False by (rule notE[OF no yes])
  qed
qed

end
