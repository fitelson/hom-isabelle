theory Bacon_Book_Conjunction_Decoded_Model
  imports Bacon_Book_Primitive_Conjunction_Model Bacon_Book_Conjunction_Decoding_Environment
    Bacon_Book_Full_Minimal_Model
begin

section \<open>The minimal reduct of a supplied conjunction model\<close>

text \<open>
  Given a native model with primitive ∧, decode minimal tagged terms
  before interpreting them. Keep D, App, G and v unchanged, and set
  κmin(l)=κ(BCMinimal(l)). This gives a full minimal model in the
  exact tagged signature. Source role: the primitive encoding of
  Bacon §5.2, p.104, with the semantic clauses of p.314.

  Each minimal logical value is an ACTUAL closed denotation witnessed
  at the source model's typed assignment. The implication, universal
  and false-point clauses are inherited directly. No truth of a fixed
  conjunction-axiom theory is assumed here, and no model-existence or
  operator-identity claim follows merely from this reduct theorem.
\<close>

theorem book_conj_decoded_minimal_model:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_conj_term \<Rightarrow> 'v"
  assumes rich: "sg_rich G" and original: "book_conjunction_model D app \<Sigma> G J V \<kappa>"
  shows "book_full_minimal_model D app (book_conj_target_signature \<Sigma>) G
    (book_conj_decoded_denote J) V (\<lambda>l. \<kappa> (BCMinimal l))"
proof -
  interpret Source: book_conjunction_model D app \<Sigma> G J V \<kappa> by (rule original)
  interpret Target: book_full_environment D app book_minimal_logical_type UNIV
    "book_conj_target_signature \<Sigma>" G "book_conj_decoded_denote J"
    by (rule book_conj_decoded_full_environment[OF rich Source.book_full_environment_axioms])
  obtain g where typed: "book_env_typed D G g"
    using Source.book_conjunction_assignment_exists by blast
  have logicals: "Target.book_closed_value (book_minimal_logical_type l) (NLogical l)
    (\<kappa> (BCMinimal l))" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV
      (book_conj_target_signature \<Sigma>) G (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have equality: "book_conj_decoded_denote J g (NLogical l) = \<kappa> (BCMinimal l)"
      by (simp only: book_conj_decoded_denote_def book_conj_decode.simps;
        rule Source.book_conjunction_logical_value_at[OF typed])
    have witnessed: "Target.book_closed_value (book_minimal_logical_type l) (NLogical l)
      (book_conj_decoded_denote J g (NLogical l))"
      by (rule Target.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using witnessed by (simp only: equality)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def,
      rule conjI[OF Target.book_full_environment_axioms], unfold_locales)
    fix l
    show "Target.book_closed_value (book_minimal_logical_type l) (NLogical l) (\<kappa> (BCMinimal l))"
      by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> D Prop" and qm: "q \<in> D Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BCMinimal SImp)) p) q) = (V p \<longrightarrow> V q)"
      by (rule Source.implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> D (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (\<kappa> (BCMinimal (SBAll \<sigma>))) f) =
      (\<forall>a\<in>D \<sigma>. V (app \<sigma> Prop f a))"
      by (rule Source.forall_truth[OF fm])
  next
    show "\<exists>p\<in>D Prop. \<not> V p" by (rule Source.false_proposition)
  qed
qed

section \<open>Native formula truth follows from actual primitive values\<close>

text \<open>
  At a typed assignment, primitive A∧B has truth v(Jg(A))∧v(Jg(B)),
  and the injected minimal implication has its material truth condition.
  These statements apply to open formulas. They use two actual application
  equations and the witnessed κ value, not replacement of ∧ by a λ-term.
\<close>

context book_conjunction_model
begin

theorem book_conj_apply_truth:
  assumes typed: "book_env_typed domain stock g"
    and first: "book_conj_formula signature stock A"
    and second: "book_conj_formula signature stock B"
  shows "V (denote g (book_conj_apply A B)) = (V (denote g A) \<and> V (denote g B))"
proof -
  have am: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I first typed])
  have bm: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I second typed])
  have partial_language: "book_in_language book_conj_logical_type UNIV signature stock
    (NApp (NLogical BCAnd) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_conj_symbol_language first])
  have partial_value: "denote g (NApp (NLogical BCAnd) A) =
    app Prop (Arr Prop Prop) (\<kappa> BCAnd) (denote g A)"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_conj_symbol_language first typed]
    by (simp only: book_conjunction_logical_value_at[OF typed])
  have whole_value: "denote g (book_conj_apply A B) =
    app Prop Prop (denote g (NApp (NLogical BCAnd) A)) (denote g B)"
    unfolding book_conj_apply_def
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial_language second typed])
  show ?thesis by (simp only: whole_value partial_value; rule conjunction_truth[OF am bm])
qed

theorem book_conj_imp_truth:
  assumes typed: "book_env_typed domain stock g"
    and first: "book_conj_formula signature stock A"
    and second: "book_conj_formula signature stock B"
  shows "V (denote g (book_conj_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
proof -
  have am: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I first typed])
  have bm: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I second typed])
  have partial_language: "book_in_language book_conj_logical_type UNIV signature stock
    (NApp (NLogical (BCMinimal SImp)) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_conj_imp_operator_language first])
  have partial_value: "denote g (NApp (NLogical (BCMinimal SImp)) A) =
    app Prop (Arr Prop Prop) (\<kappa> (BCMinimal SImp)) (denote g A)"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_conj_imp_operator_language first typed]
    by (simp only: book_conjunction_logical_value_at[OF typed])
  have whole_value: "denote g (book_conj_imp A B) =
    app Prop Prop (denote g (NApp (NLogical (BCMinimal SImp)) A)) (denote g B)"
    unfolding book_conj_imp_def
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial_language second typed])
  show ?thesis by (simp only: whole_value partial_value; rule implication_truth[OF am bm])
qed

end

end
