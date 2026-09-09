theory Bacon_Source_ZF_Action_Model_Nonempty
  imports Bacon_Source_ZF_Action_Model
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Application_Graph
begin

section \<open>Totality gives actual values at each object through a root arrow\<close>

text \<open>
  A generic action model supplies a root arrow to each W and a
  defined value in Wρ for every adequate, typed interpretation input.
  Source: Definitions 3.18–3.20, pp.55–56. This is the GIVEN
  independent action model, not the previously constructed BBK image.
  No BBK-model predicate or closed denotability assumption is used.
\<close>

lemma paper_ZF_action_model_value_at_object:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and language: "paper_R_in_language \<Sigma> G B \<rho>"
    and typed: "paper_ZF_action_env_typed D G W g" and adequate: "named_adequate g B"
  obtains h v where "h \<in> explode Ar" "source h = root" "target h = W"
    "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some v"
    "v \<in> explode (D \<rho> W)"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret Rooted: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  obtain h where arrow: "h \<in> explode Ar" and origin: "source h = root" and finish: "target h = W"
    using Rooted.root_reaches[OF object] by blast
  have target_typed: "paper_ZF_action_env_typed D G (target h) g" by (simp only: finish; rule typed)
  obtain v where evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some v"
    and member: "v \<in> explode (D \<rho> (target h))"
    using model language arrow origin target_typed adequate unfolding paper_ZF_action_model_def by blast
  have at_W: "v \<in> explode (D \<rho> W)" using member by (simp only: finish)
  show thesis by (rule that[OF arrow origin finish evaluated at_W])
qed

section \<open>A closed proposition needs no proposition-valued assignment entry\<close>

lemma paper_ZF_action_model_Prop_nonempty:
  fixes \<Sigma> :: "'c ssignature"
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj"
  shows "explode (D Prop W) \<noteq> {}"
proof -
  have rich: "paper_R_rich G" using model unfolding paper_ZF_action_model_def by (rule conjunct1)
  have pr: "paper_R_type Prop" by simp
  obtain p where pt: "G p = Prop" and pf: "p \<notin> {}" by (rule paper_R_rich_fresh[OF rich pr finite.emptyI])
  let ?B = "NApp (NLogical (SAll Prop)) (NLam p (NVar p)) :: 'c paper_named_term"
  have variable: "paper_R_in_language \<Sigma> G (NVar p) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=p, OF pt pr])
  have vt: "paper_R_has_type G (NVar p :: 'c paper_named_term) Prop"
    using variable unfolding paper_R_in_language_def by (rule conjunct1)
  have nr: "paper_R_type (G p)" by (simp only: pt; rule pr)
  have raw_predicate: "paper_R_has_type G (NLam p (NVar p) :: 'c paper_named_term) (Arr (G p) Prop)"
    by (rule paper_R_has_type.Lam[OF vt nr]; simp)
  have predicate: "paper_R_has_type G (NLam p (NVar p) :: 'c paper_named_term) (Arr Prop Prop)"
    using raw_predicate by (simp only: pt)
  have qr: "paper_R_type (paper_logical_type (SAll Prop))" by simp
  have quantifier: "paper_R_has_type G (NLogical (SAll Prop) :: 'c paper_named_term) (Arr (Arr Prop Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SAll Prop", OF qr] by simp
  have bt: "paper_R_has_type G ?B Prop" by (rule paper_R_has_type.App[OF quantifier predicate])
  have language: "paper_R_in_language \<Sigma> G ?B Prop"
    unfolding paper_R_in_language_def by (rule conjI[OF bt]; simp)
  have empty_typed: "paper_ZF_action_env_typed D G W Map.empty" by (rule paper_ZF_action_env_empty)
  have adequate: "named_adequate Map.empty ?B" by (simp add: named_adequate_def)
  obtain h v where member: "v \<in> explode (D Prop W)"
    by (rule paper_ZF_action_model_value_at_object[OF model object language empty_typed adequate]; rule that; assumption)
  show ?thesis using member by blast
qed

section \<open>Every R domain is nonempty, derived without total assignments\<close>

text \<open>
  At e use the premodel clause. At t use the closed term ∀p.p
  under the empty assignment. At σ→τ choose a τ-value a by
  induction and interpret λxσ.yτ under the partial assignment
  [y↦a], with x≠y. The R arrow guard supplies τ≠e.
  Source role: Proposition 3.21, p.57 and Appendix C, p.70.
  No value for x, nonlogical constant, or full assignment is needed.
\<close>

theorem paper_ZF_action_model_R_domain_nonempty:
  fixes \<Sigma> :: "'c ssignature"
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type \<rho>"
  shows "explode (D \<rho> W) \<noteq> {}"
  using rt
proof (induction \<rho>)
  case Ind
  show ?case using model object unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
next
  case Prop
  show ?case by (rule paper_ZF_action_model_Prop_nonempty[OF model object])
next
  case (Arr \<sigma> \<tau>)
  have sr: "paper_R_type \<sigma>" and tr: "paper_R_type \<tau>" and codomain: "\<tau> \<noteq> Ind"
    using Arr.prems by simp_all
  have inhabited: "explode (D \<tau> W) \<noteq> {}" by (rule Arr.IH(2)[OF tr])
  obtain a where member: "a \<in> explode (D \<tau> W)" using inhabited by blast
  have rich: "paper_R_rich G" using model unfolding paper_ZF_action_model_def by (rule conjunct1)
  obtain y where yt: "G y = \<tau>" and yf: "y \<notin> {}" by (rule paper_R_rich_fresh[OF rich tr finite.emptyI])
  have finite_y: "finite {y}" by simp
  obtain x where xt: "G x = \<sigma>" and xf: "x \<notin> {y}" by (rule paper_R_rich_fresh[OF rich sr finite_y])
  have distinct: "x \<noteq> y" using xf by simp
  have variable: "paper_R_in_language \<Sigma> G (NVar y) \<tau>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=y, OF yt tr])
  have vt: "paper_R_has_type G (NVar y :: 'c paper_named_term) \<tau>"
    using variable unfolding paper_R_in_language_def by (rule conjunct1)
  have xr: "paper_R_type (G x)" by (simp only: xt; rule sr)
  have abstraction: "paper_R_has_type G (NLam x (NVar y) :: 'c paper_named_term) (Arr (G x) \<tau>)"
    by (rule paper_R_has_type.Lam[OF vt xr codomain])
  have language: "paper_R_in_language \<Sigma> G (NLam x (NVar y)) (Arr \<sigma> \<tau>)"
    using abstraction by (simp add: paper_R_in_language_def xt)
  have empty_typed: "paper_ZF_action_env_typed D G W Map.empty" by (rule paper_ZF_action_env_empty)
  have typed: "paper_ZF_action_env_typed D G W (Map.empty(y := Some a))"
    by (rule paper_ZF_action_env_update[OF empty_typed yt tr member])
  have adequate: "named_adequate (Map.empty(y := Some a)) (NLam x (NVar y) :: 'c paper_named_term)"
    by (simp add: named_adequate_def dom_def distinct)
  obtain h v where represented: "v \<in> explode (D (Arr \<sigma> \<tau>) W)"
    by (rule paper_ZF_action_model_value_at_object[OF model object language typed adequate]; rule that; assumption)
  show ?case using represented by blast
qed

end
