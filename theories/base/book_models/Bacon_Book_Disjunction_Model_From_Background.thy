theory Bacon_Book_Disjunction_Model_From_Background
  imports Bacon_Book_Primitive_Disjunction_Model Bacon_Book_Disjunction_Encoding_Environment
    Bacon_Book_Disjunction_Background_Truth
begin

section \<open>Retain all inherited values and add the actual disjunction-tag value\<close>

fun book_disj_lifted_values ::
  "(book_conj_logical \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> book_disj_logical \<Rightarrow> 'v" where
  "book_disj_lifted_values k a (BDConjunction l) = k l"
| "book_disj_lifted_values k a BDOr = a"

text \<open>
  A conjunction model satisfying the fixed background Π∨ yields a
  native model with BOTH primitive ∧ and ∨. Keep its domains, App,
  and valuation; interpret native A by Jg(enc(A)). Preserve all old
  logical values and assign ∨ the actual value of its atomic tag.
  Source: §5.2, p.104, and Definition 15.1, p.314.

  Each logical denotation is witnessed by a typed assignment. The three
  inherited semantic clauses transfer unchanged, and the independently
  proved background truth calculation supplies the new disjunction clause.
  This transport assumes its input model; the later existence theorem
  must obtain that model from consistency, not assume the native model.
\<close>

theorem book_disj_model_from_background_at:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> 'v"
  assumes model: "book_conjunction_model D app (book_disj_target_signature \<Sigma>) G J V k"
    and rich: "sg_rich G"
    and background: "\<forall>A\<in>book_disj_axioms \<Sigma> G. book_formula_valid D G J V A"
    and typed: "book_env_typed D G g0"
  shows "book_disjunction_model D app \<Sigma> G (book_disj_encoded_denote J) V
    (book_disj_lifted_values k (J g0 (NConst (Inr ()) book_disj_type)))"
proof -
  let ?tag = "NConst (Inr ()) book_disj_type"
  let ?K = "book_disj_lifted_values k (J g0 ?tag)"
  interpret Target: book_conjunction_model D app "book_disj_target_signature \<Sigma>" G J V k
    by (rule model)
  interpret Encoded: book_full_environment D app book_disj_logical_type UNIV \<Sigma> G "book_disj_encoded_denote J"
    by (rule book_disj_encoded_full_environment[OF Target.book_full_environment_axioms rich])
  have at_symbol: "book_disj_encoded_denote J g0 (NLogical l) = ?K l" for l
    by (cases l) (simp_all add: book_disj_encoded_denote_symbols Target.book_conjunction_logical_value_at[OF typed])
  have logicals: "Encoded.book_closed_value (book_disj_logical_type l) (NLogical l) (?K l)" for l
  proof -
    have language: "book_in_language book_disj_logical_type UNIV \<Sigma> G (NLogical l) (book_disj_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have defined: "Encoded.book_closed_value (book_disj_logical_type l) (NLogical l)
      (book_disj_encoded_denote J g0 (NLogical l))"
      by (rule Encoded.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using defined by (simp only: at_symbol)
  qed
  have background_valid: "book_formula_valid D G J V A" if "A \<in> book_disj_axioms \<Sigma> G" for A
    by (rule bspec[OF background that])
  show ?thesis
  proof (unfold book_disjunction_model_def,
      rule conjI[OF Encoded.book_full_environment_axioms], unfold_locales)
    fix l
    show "Encoded.book_closed_value (book_disj_logical_type l) (NLogical l) (?K l)" by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (?K (BDConjunction (BCMinimal SImp))) p) q) = (V p \<longrightarrow> V q)"
      by (simp only: book_disj_lifted_values.simps; rule Target.implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> D (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (?K (BDConjunction (BCMinimal (SBAll \<sigma>)))) f) =
      (\<forall>a\<in>D \<sigma>. V (app \<sigma> Prop f a))"
      by (simp only: book_disj_lifted_values.simps; rule Target.forall_truth[OF fm])
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (?K (BDConjunction BCAnd)) p) q) = (V p \<and> V q)"
      by (simp only: book_disj_lifted_values.simps; rule Target.conjunction_truth[OF pm qm])
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (?K BDOr) p) q) = (V p \<or> V q)"
      by (simp only: book_disj_lifted_values.simps;
        rule book_disj_background_truth_at[OF model rich background_valid typed pm qm])
  next
    show "\<exists>p\<in>D Prop. \<not> V p" by (rule Target.false_proposition)
  qed
qed

corollary book_disj_model_from_background:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> 'v"
  assumes model: "book_conjunction_model D app (book_disj_target_signature \<Sigma>) G J V k"
    and rich: "sg_rich G"
    and background: "\<forall>A\<in>book_disj_axioms \<Sigma> G. book_formula_valid D G J V A"
  shows "\<exists>k'. book_disjunction_model D app \<Sigma> G (book_disj_encoded_denote J) V k'"
proof -
  interpret Target: book_conjunction_model D app "book_disj_target_signature \<Sigma>" G J V k by (rule model)
  obtain g0 where typed: "book_env_typed D G g0" using Target.book_conjunction_assignment_exists by blast
  show ?thesis by (rule exI, rule book_disj_model_from_background_at[OF model rich background typed])
qed

end
