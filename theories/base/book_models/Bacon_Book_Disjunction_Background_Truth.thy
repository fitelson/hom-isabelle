theory Bacon_Book_Disjunction_Background_Truth
  imports Bacon_Book_Disjunction_Axiom_Truth Bacon_Book_Primitive_Disjunction_Axiom_Theory
begin

section \<open>Fixed-background models give the new primitive its exact truth clause\<close>

text \<open>
  Start with a conjunction model of Π∨ in the tagged signature.
  Its actual tag denotation k satisfies v(kab) ↔ v(a)∨v(b) on
  EVERY domain pair. Three distinct proposition variables exist by rich G;
  the three required schemas belong to Π∨ by its independent definition.
  The preceding axiom-truth theorem then supplies the all-domain clause.

  Source: §5.2, p.104, and Definition 15.1, p.314. The typed assignment
  g₀ explicitly witnesses k. We do not postulate a denotation for a closed
  constant in an empty environment. This theorem assumes a model of Π∨;
  native proof reflection and model existence must later supply that model.
\<close>

theorem book_disj_background_truth_at:
  fixes \<Sigma> :: "'c ssignature"
  assumes model: "book_conjunction_model D app (book_disj_target_signature \<Sigma>) G J V \<kappa>"
    and rich: "sg_rich G"
    and background: "\<And>A. A \<in> book_disj_axioms \<Sigma> G \<Longrightarrow> book_formula_valid D G J V A"
    and typed0: "book_env_typed D G g0"
    and am: "a \<in> D Prop" and bm: "b \<in> D Prop"
  shows "V (app Prop Prop
    (app Prop (Arr Prop Prop) (J g0 (NConst (Inr ()) book_disj_type)) a) b) \<longleftrightarrow> (V a \<or> V b)"
proof -
  interpret Source: book_conjunction_model D app "book_disj_target_signature \<Sigma>" G J V \<kappa>
    by (rule model)
  let ?K = "NConst (Inr ()) book_disj_type"
  have kl: "book_in_language book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G ?K book_disj_type"
    by (simp add: book_language_const_iff book_disj_target_tag_iff)
  have closed: "named_fv ?K = {}" by simp
  have witnessed: "Source.book_closed_value book_disj_type ?K (J g0 ?K)"
    by (rule Source.book_closed_value_intro[OF UNIV_I kl closed typed0])
  obtain x where xt: "G x = Prop"
    using sg_rich_fresh[where \<sigma>=Prop and S="{}", OF rich] by auto
  obtain y where yt: "G y = Prop" and yfresh: "y \<notin> {x}"
    using sg_rich_fresh[where \<sigma>=Prop and S="{x}", OF rich] by auto
  obtain z where zt: "G z = Prop" and zfresh: "z \<notin> {x,y}"
    using sg_rich_fresh[where \<sigma>=Prop and S="{x,y}", OF rich] by auto
  have xy: "x \<noteq> y" and xz: "x \<noteq> z" and yz: "y \<noteq> z"
    using yfresh zfresh by auto
  have xl: "book_conj_formula (book_disj_target_signature \<Sigma>) G (NVar x)"
    by (simp add: book_language_var_iff xt)
  have yl: "book_conj_formula (book_disj_target_signature \<Sigma>) G (NVar y)"
    by (simp add: book_language_var_iff yt)
  have zl: "book_conj_formula (book_disj_target_signature \<Sigma>) G (NVar z)"
    by (simp add: book_language_var_iff zt)
  have eliminate: "book_formula_valid D G J V
    (book_conj_imp (book_conj_imp (NVar x) (NVar z))
      (book_conj_imp (book_conj_imp (NVar y) (NVar z))
        (book_conj_imp (NApp (NApp ?K (NVar x)) (NVar y)) (NVar z))))"
    using background[OF book_disj_axioms.Elim[OF xl yl zl]]
    by (simp only: book_disj_target_apply_def)
  have left: "book_formula_valid D G J V
    (book_conj_imp (NVar x) (NApp (NApp ?K (NVar x)) (NVar y)))"
    using background[OF book_disj_axioms.Intro1[OF xl yl]]
    by (simp only: book_disj_target_apply_def)
  have right: "book_formula_valid D G J V
    (book_conj_imp (NVar y) (NApp (NApp ?K (NVar x)) (NVar y)))"
    using background[OF book_disj_axioms.Intro2[OF xl yl]]
    by (simp only: book_disj_target_apply_def)
  show ?thesis
    by (rule Source.book_disjunction_axioms_truth[
      OF witnessed xt yt zt xy xz yz eliminate left right am bm])
qed

end
