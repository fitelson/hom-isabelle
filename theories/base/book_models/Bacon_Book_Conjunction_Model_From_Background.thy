theory Bacon_Book_Conjunction_Model_From_Background
  imports Bacon_Book_Primitive_Conjunction_Model Bacon_Book_Conjunction_Encoding_Environment
    Bacon_Book_Conjunction_Background_Truth
begin

section \<open>Retaining the minimal logical values and adding the tag's value\<close>

fun book_conj_lifted_values ::
  "(book_minimal_logical \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> book_conj_logical \<Rightarrow> 'v" where
  "book_conj_lifted_values k a (BCMinimal l) = k l"
| "book_conj_lifted_values k a BCAnd = a"

text \<open>
  A minimal model of the fixed background Π∧ yields an actual model
  of the native primitive-conjunction language. Its domains, App and v
  stay fixed. The native denotation is Jg(enc(A)); the new conjunction
  value is the actual denotation of the distinguished constant at a typed
  assignment. Every native logical value has a closed-denotation witness.
  Source: §5.2, p.104, and Definition 15.1, p.314.

  The input-model premise is explicit in this transport theorem. The later
  existence theorem must discharge it using the proved consistency bridge.
  No λ-definition or identity condition replaces primitive conjunction.
\<close>

theorem book_conj_model_from_background_at:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> 'v"
  assumes model: "book_full_minimal_model D app (book_conj_target_signature \<Sigma>) G J V k"
    and rich: "sg_rich G"
    and background: "\<forall>A\<in>book_conj_axioms \<Sigma> G. book_formula_valid D G J V A"
    and typed: "book_env_typed D G g0"
  shows "book_conjunction_model D app \<Sigma> G (book_conj_encoded_denote J) V
    (book_conj_lifted_values k (J g0 (NConst (Inr ()) book_conj_type)))"
proof -
  let ?tag = "NConst (Inr ()) book_conj_type"
  let ?K = "book_conj_lifted_values k (J g0 ?tag)"
  interpret Target: book_full_minimal_model D app "book_conj_target_signature \<Sigma>" G J V k
    by (rule model)
  interpret Encoded: book_full_environment D app book_conj_logical_type UNIV \<Sigma> G "book_conj_encoded_denote J"
    by (rule book_conj_encoded_full_environment[OF Target.book_full_environment_axioms rich])
  have at_symbol: "book_conj_encoded_denote J g0 (NLogical l) = ?K l" for l
    by (cases l) (simp_all add: book_conj_encoded_denote_symbols Target.book_minimal_logical_value_at[OF typed])
  have logicals: "Encoded.book_closed_value (book_conj_logical_type l) (NLogical l) (?K l)" for l
  proof -
    have language: "book_in_language book_conj_logical_type UNIV \<Sigma> G (NLogical l) (book_conj_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have defined: "Encoded.book_closed_value (book_conj_logical_type l) (NLogical l)
      (book_conj_encoded_denote J g0 (NLogical l))"
      by (rule Encoded.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using defined by (simp only: at_symbol)
  qed
  show ?thesis
  proof (unfold book_conjunction_model_def,
      rule conjI[OF Encoded.book_full_environment_axioms], unfold_locales)
    fix l
    show "Encoded.book_closed_value (book_conj_logical_type l) (NLogical l) (?K l)" by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (?K (BCMinimal SImp)) p) q) = (V p \<longrightarrow> V q)"
      by (simp only: book_conj_lifted_values.simps; rule Target.implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> D (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (?K (BCMinimal (SBAll \<sigma>))) f) = (\<forall>a\<in>D \<sigma>. V (app \<sigma> Prop f a))"
      by (simp only: book_conj_lifted_values.simps; rule Target.forall_truth[OF fm])
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (?K BCAnd) p) q) = (V p \<and> V q)"
      by (simp only: book_conj_lifted_values.simps;
        rule book_conj_background_truth_at[OF model rich background typed pm qm])
  next
    show "\<exists>p\<in>D Prop. \<not> V p" by (rule Target.false_proposition)
  qed
qed

corollary book_conj_model_from_background:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> 'v"
  assumes model: "book_full_minimal_model D app (book_conj_target_signature \<Sigma>) G J V k"
    and rich: "sg_rich G"
    and background: "\<forall>A\<in>book_conj_axioms \<Sigma> G. book_formula_valid D G J V A"
  shows "\<exists>k'. book_conjunction_model D app \<Sigma> G (book_conj_encoded_denote J) V k'"
proof -
  interpret Target: book_full_minimal_model D app "book_conj_target_signature \<Sigma>" G J V k by (rule model)
  obtain g0 where typed: "book_env_typed D G g0" using Target.book_minimal_assignment_exists by blast
  show ?thesis by (rule exI, rule book_conj_model_from_background_at[OF model rich background typed])
qed

end
