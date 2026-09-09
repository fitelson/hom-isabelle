theory Bacon_Book_Disjunction_Decoded_Model
  imports Bacon_Book_Primitive_Disjunction_Model Bacon_Book_Disjunction_Decoding_Environment
    Bacon_Book_Primitive_Conjunction_Model
begin

section \<open>The conjunction reduct of a supplied disjunction model\<close>

text \<open>
  Given a native model with primitive ∧ and ∨, interpret target terms
  by Jᵈg(A)=Jg(dec(A)). Keep D, App, G and v unchanged, and put
  κ∧(l)=κ(BDConjunction(l)). The result is a conjunction model at the
  exact tagged signature. Source: Bacon §5.2, p.104, and Definition
  15.1, p.314, with witnessed closed values from Convention 14.3, p.298.

  Every old logical symbol has an ACTUAL closed-value witness at a
  typed assignment of the supplied model. Implication, universal,
  conjunction and false-point clauses are inherited. No Π premise,
  model existence or identity between primitive and defined operators
  is asserted. The rich stock is used for environment transport.
\<close>

theorem book_disj_decoded_conjunction_model:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_disj_term \<Rightarrow> 'v"
  assumes rich: "sg_rich G" and original: "book_disjunction_model D app \<Sigma> G J V \<kappa>"
  shows "book_conjunction_model D app (book_disj_target_signature \<Sigma>) G
    (book_disj_decoded_denote J) V (\<lambda>l. \<kappa> (BDConjunction l))"
proof -
  interpret Source: book_disjunction_model D app \<Sigma> G J V \<kappa> by (rule original)
  interpret Target: book_full_environment D app book_conj_logical_type UNIV
    "book_disj_target_signature \<Sigma>" G "book_disj_decoded_denote J"
    by (rule book_disj_decoded_full_environment[OF rich Source.book_full_environment_axioms])
  obtain g where typed: "book_env_typed D G g"
    using Source.book_disjunction_assignment_exists by blast
  have logicals: "Target.book_closed_value (book_conj_logical_type l) (NLogical l)
    (\<kappa> (BDConjunction l))" for l
  proof -
    have language: "book_in_language book_conj_logical_type UNIV
      (book_disj_target_signature \<Sigma>) G (NLogical l) (book_conj_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have equality: "book_disj_decoded_denote J g (NLogical l) = \<kappa> (BDConjunction l)"
      by (simp only: book_disj_decoded_denote_def book_disj_decode.simps;
        rule Source.book_disjunction_logical_value_at[OF typed])
    have witnessed: "Target.book_closed_value (book_conj_logical_type l) (NLogical l)
      (book_disj_decoded_denote J g (NLogical l))"
      by (rule Target.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using witnessed by (simp only: equality)
  qed
  show ?thesis
  proof (unfold book_conjunction_model_def,
      rule conjI[OF Target.book_full_environment_axioms], unfold_locales)
    fix l
    show "Target.book_closed_value (book_conj_logical_type l) (NLogical l) (\<kappa> (BDConjunction l))"
      by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BDConjunction (BCMinimal SImp))) p) q) = (V p \<longrightarrow> V q)"
      by (rule Source.implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> D (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (\<kappa> (BDConjunction (BCMinimal (SBAll \<sigma>)))) f) =
      (\<forall>a\<in>D \<sigma>. V (app \<sigma> Prop f a))"
      by (rule Source.forall_truth[OF fm])
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BDConjunction BCAnd)) p) q) =
      (V p \<and> V q)"
      by (rule Source.conjunction_truth[OF pm qm])
  next
    show "\<exists>p\<in>D Prop. \<not> V p" by (rule Source.false_proposition)
  qed
qed

section \<open>Native formula truth follows from actual primitive values\<close>

text \<open>
  At a typed assignment, primitive A∨B has truth v(Jg(A))∨v(Jg(B)),
  and the injected minimal implication has its material truth condition.
  These statements apply to open formulas. They use two actual application
  equations and the witnessed κ value, not replacement of ∨ by a λ-term.
\<close>

context book_disjunction_model
begin

theorem book_disj_apply_truth:
  assumes typed: "book_env_typed domain stock g"
    and first: "book_disj_formula signature stock A"
    and second: "book_disj_formula signature stock B"
  shows "V (denote g (book_disj_apply A B)) = (V (denote g A) \<or> V (denote g B))"
proof -
  have am: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I first typed])
  have bm: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I second typed])
  have partial_language: "book_in_language book_disj_logical_type UNIV signature stock
    (NApp (NLogical BDOr) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_disj_symbol_language first])
  have partial_value: "denote g (NApp (NLogical BDOr) A) =
    app Prop (Arr Prop Prop) (\<kappa> BDOr) (denote g A)"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_disj_symbol_language first typed]
    by (simp only: book_disjunction_logical_value_at[OF typed])
  have whole_value: "denote g (book_disj_apply A B) =
    app Prop Prop (denote g (NApp (NLogical BDOr) A)) (denote g B)"
    unfolding book_disj_apply_def
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial_language second typed])
  show ?thesis by (simp only: whole_value partial_value; rule disjunction_truth[OF am bm])
qed

theorem book_disj_imp_truth:
  assumes typed: "book_env_typed domain stock g"
    and first: "book_disj_formula signature stock A"
    and second: "book_disj_formula signature stock B"
  shows "V (denote g (book_disj_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
proof -
  have am: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I first typed])
  have bm: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I second typed])
  have partial_language: "book_in_language book_disj_logical_type UNIV signature stock
    (NApp (NLogical (BDConjunction (BCMinimal SImp))) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_disj_imp_operator_language first])
  have partial_value: "denote g (NApp (NLogical (BDConjunction (BCMinimal SImp))) A) =
    app Prop (Arr Prop Prop) (\<kappa> (BDConjunction (BCMinimal SImp))) (denote g A)"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_disj_imp_operator_language first typed]
    by (simp only: book_disjunction_logical_value_at[OF typed])
  have whole_value: "denote g (book_disj_imp A B) =
    app Prop Prop (denote g (NApp (NLogical (BDConjunction (BCMinimal SImp))) A)) (denote g B)"
    unfolding book_disj_imp_def
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial_language second typed])
  show ?thesis by (simp only: whole_value partial_value; rule implication_truth[OF am bm])
qed

end

end
