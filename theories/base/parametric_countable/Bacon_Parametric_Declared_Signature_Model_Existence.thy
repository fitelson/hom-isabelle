theory Bacon_Parametric_Declared_Signature_Model_Existence
  imports Bacon_Parametric_Declared_Signature_Coding Bacon_Parametric_Countable_Model_Existence
begin

section \<open>Countably many declared names suffice for a model in ℕ\<close>

text \<open>
  If ⋃σΣσ is countable and S ⊆ ℒ(Σ) is an H-consistent set of
  sentences, there is a BBK model ℳ satisfying S with Dσ ⊆ ℕ for every σ.
  Source: Bacon–Dorr Theorem 3.2, pp.44–45, countable-signature refinement.

  Isabelle representation: first encode only the declared names into ℕ.
  The guarded inverse map reflects proofs, so e(S) remains consistent in
  the encoded signature.  Apply the checked natural-name model theorem,
  then pull its interpretation back along the name code.  The semantic
  domains and truth valuation are unchanged by this final pullback.

  Status: unlike the earlier countable-name-type theorem, the final theorem
  below has no typeclass constraint on the original name carrier.  Its only
  cardinality premise concerns the union of the declared name sets.  No
  enumeration of S, closed inhabitation of the original signature, or
  Functionality is assumed.  The domains are subsets of ℕ, not stipulated
  to be all of ℕ.
\<close>

context pH_countable_signature
begin

lemma pHdecl_nat_model_existence:
  assumes typed: "pH_typed_theory signature [] S" and consistent: "pH_consistent signature [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model signature D J V \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  have encoded_typed: "pH_typed_theory pHdecl_signature [] (phenkin_map pHdecl_code ` S)"
    by (rule pHdecl_encoded_typed[OF typed])
  have encoded_consistent: "pH_consistent pHdecl_signature [] (phenkin_map pHdecl_code ` S)"
    by (rule pHdecl_encoded_consistent[OF typed consistent])
  obtain D :: "otype \<Rightarrow> nat set" and J :: "(nat \<Rightarrow> nat) \<Rightarrow> nat pterm \<Rightarrow> nat"
    and V :: "nat \<Rightarrow> bool" where encoded_model: "pbbk_model pHdecl_signature D J V"
      and subsets: "\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV"
      and encoded_truths: "\<forall>B \<in> phenkin_map pHdecl_code ` S. \<forall>g. V (J g B)"
    using pH_BBK_nat_model_existence[OF encoded_typed encoded_consistent] by (elim exE conjE)
  let ?J = "pbbk_pullback_denote pHdecl_code J"
  have model: "pbbk_model signature D ?J V"
    by (rule pbbk_model_name_pullback[where k=pHdecl_code, OF encoded_model pHdecl_encode_name])
  have realizes: "\<forall>A \<in> S. \<forall>g. V (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have encoded_member: "phenkin_map pHdecl_code A \<in> phenkin_map pHdecl_code ` S"
      by (rule imageI[OF member])
    have all_assignments: "\<forall>h. V (J h (phenkin_map pHdecl_code A))"
      by (rule bspec[OF encoded_truths encoded_member])
    have truth: "V (J g (phenkin_map pHdecl_code A))" by (rule spec[OF all_assignments])
    show "V (?J g A)" unfolding pbbk_pullback_denote_def by (rule truth)
  qed
  show ?thesis
  proof (rule exI[where x=D], rule exI[where x="?J"], rule exI[where x=V])
    show "pbbk_model signature D ?J V \<and> (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and>
      (\<forall>A \<in> S. \<forall>g. V (?J g A))"
      by (rule conjI[OF model conjI[OF subsets realizes]])
  qed
qed

end

theorem pH_BBK_countable_signature_model_existence:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set. \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool. pbbk_model \<Sigma> D J V \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> UNIV) \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  interpret Code: pH_countable_signature \<Sigma> by (unfold_locales) (rule countable_signature)
  show ?thesis by (rule Code.pHdecl_nat_model_existence[OF typed consistent])
qed

end
