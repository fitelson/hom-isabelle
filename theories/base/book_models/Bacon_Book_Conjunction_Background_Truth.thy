theory Bacon_Book_Conjunction_Background_Truth
  imports Bacon_Book_Primitive_Conjunction_Axiom_Theory Bacon_Book_Conjunction_Axiom_Truth
begin

section \<open>The fixed background gives the tag its all-domain truth law\<close>

text \<open>
  Let K be the distinguished target constant k∧:t→t→t. In a full
  minimal model satisfying Π∧, an actual typed assignment g₀ gives a
  witnessed closed value k=Jg₀(K). The three Π∧ schemas at two
  distinct proposition variables imply v(kab) iff v(a) and v(b), for
  EVERY a,b∈Dₜ. Source: Bacon, §5.2, p.104, and Definition 15.1,
  p.314.

  Representation. The input model interprets the exact typed-tag target
  signature. Π∧ is a set of globally true premises, not a collection of
  minimal-H theorems. Arbitrary domain elements are supplied by typed
  variable updates, not by assuming closed terms denote them. The tag is
  neither substituted away nor equated with a λ-defined conjunction.
  This lemma constructs no model; it transfers a truth clause inside
  the explicitly supplied input model.
\<close>

context
  fixes \<Sigma> :: "'c ssignature"
    and domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and G :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> 'v"
    and V :: "'v \<Rightarrow> bool"
    and \<kappa> :: "book_minimal_logical \<Rightarrow> 'v"
  assumes target_model: "book_full_minimal_model domain app (book_conj_target_signature \<Sigma>) G denote V \<kappa>"
begin

interpretation Background: book_full_minimal_model domain app "book_conj_target_signature \<Sigma>" G denote V \<kappa>
  by (rule target_model)

lemma book_conj_background_tag_closed_value:
  assumes typed: "book_env_typed domain G g0"
  shows "Background.book_closed_value book_conj_type (NConst (Inr ()) book_conj_type)
    (denote g0 (NConst (Inr ()) book_conj_type))"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G
    (NConst (Inr ()) book_conj_type) book_conj_type"
    by (simp add: book_language_const_iff book_conj_target_tag_iff)
  have closed: "named_fv (NConst (Inr ()) book_conj_type) = {}" by simp
  show ?thesis by (rule Background.book_closed_value_intro[OF UNIV_I language closed typed])
qed

theorem book_conj_background_truth_at:
  assumes rich: "sg_rich G"
    and background: "\<forall>A\<in>book_conj_axioms \<Sigma> G. book_formula_valid domain G denote V A"
    and typed: "book_env_typed domain G g0"
    and am: "a \<in> domain Prop" and bm: "b \<in> domain Prop"
  shows "V (app Prop Prop
      (app Prop (Arr Prop Prop) (denote g0 (NConst (Inr ()) book_conj_type)) a) b)
    \<longleftrightarrow> (V a \<and> V b)"
proof -
  let ?K = "NConst (Inr ()) book_conj_type"
  let ?x = "book_prop_name G"
  have xtype: "G ?x = Prop" by (rule book_prop_name_type[OF rich])
  have finite_names: "finite {?x}" by simp
  obtain y where ytype: "G y = Prop" and fresh: "y \<notin> {?x}"
    using sg_rich_fresh[where \<sigma>=Prop and S="{?x}", OF rich finite_names] by (elim exE conjE)
  have distinct: "?x \<noteq> y" using fresh by simp
  have xl: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (NVar ?x)"
    by (simp only: book_language_var_iff xtype)
  have yl: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (NVar y)"
    by (simp only: book_language_var_iff ytype)
  have intro_member: "book_imp (NVar ?x)
      (book_imp (NVar y) (book_conj_target_apply (NVar ?x) (NVar y))) \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Intro[OF xl yl])
  have left_member: "book_imp (book_conj_target_apply (NVar ?x) (NVar y)) (NVar ?x) \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Left[OF xl yl])
  have right_member: "book_imp (book_conj_target_apply (NVar ?x) (NVar y)) (NVar y) \<in> book_conj_axioms \<Sigma> G"
    by (rule book_conj_axioms.Right[OF xl yl])
  have introduction: "book_formula_valid domain G denote V
    (book_imp (NVar ?x) (book_imp (NVar y) (NApp (NApp ?K (NVar ?x)) (NVar y))))"
    using bspec[OF background intro_member] by (simp only: book_conj_target_apply_def)
  have left_axiom: "book_formula_valid domain G denote V
    (book_imp (NApp (NApp ?K (NVar ?x)) (NVar y)) (NVar ?x))"
    using bspec[OF background left_member] by (simp only: book_conj_target_apply_def)
  have right_axiom: "book_formula_valid domain G denote V
    (book_imp (NApp (NApp ?K (NVar ?x)) (NVar y)) (NVar y))"
    using bspec[OF background right_member] by (simp only: book_conj_target_apply_def)
  have closed_value: "Background.book_closed_value book_conj_type ?K (denote g0 ?K)"
    by (rule book_conj_background_tag_closed_value[OF typed])
  show ?thesis by (rule Background.book_conjunction_axioms_truth[
    OF closed_value xtype ytype distinct introduction left_axiom right_axiom am bm])
qed

theorem book_conj_background_value_exists:
  assumes rich: "sg_rich G"
    and background: "\<forall>A\<in>book_conj_axioms \<Sigma> G. book_formula_valid domain G denote V A"
  shows "\<exists>g0. book_env_typed domain G g0 \<and>
    Background.book_closed_value book_conj_type (NConst (Inr ()) book_conj_type)
      (denote g0 (NConst (Inr ()) book_conj_type)) \<and>
    (\<forall>a\<in>domain Prop. \<forall>b\<in>domain Prop.
      V (app Prop Prop (app Prop (Arr Prop Prop) (denote g0 (NConst (Inr ()) book_conj_type)) a) b)
        \<longleftrightarrow> (V a \<and> V b))"
proof -
  obtain g0 where typed: "book_env_typed domain G g0"
    using Background.book_minimal_assignment_exists by (elim exE)
  have closed_value: "Background.book_closed_value book_conj_type (NConst (Inr ()) book_conj_type)
    (denote g0 (NConst (Inr ()) book_conj_type))"
    by (rule book_conj_background_tag_closed_value[OF typed])
  have truth: "\<forall>a\<in>domain Prop. \<forall>b\<in>domain Prop.
      V (app Prop Prop (app Prop (Arr Prop Prop) (denote g0 (NConst (Inr ()) book_conj_type)) a) b)
        \<longleftrightarrow> (V a \<and> V b)"
    by (intro ballI; rule book_conj_background_truth_at[OF rich background typed]; assumption)
  show ?thesis by (rule exI[where x=g0], rule conjI[OF typed conjI[OF closed_value truth]])
qed

end

end
