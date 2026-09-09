theory Bacon_Source_Relational_Negation_Profile
  imports Bacon_Source_Relational_Application_Morphism Bacon_Source_Relational_Subcategory
    Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Logical constants under empty partial assignments\<close>

text \<open>
  A logical constant has no free variables. Its denotation at a typed
  assignment equals its denotation at the empty assignment, and every
  homomorphism carries that value to the corresponding target value.
  Source: Definition 3.1(ii.c), p.44, and §3.3, p.49.
  These helpers use only the independent R interface.
\<close>

lemma paper_R_logical_language:
  assumes rt: "paper_R_type (paper_logical_type l)"
  shows "paper_R_in_language \<Sigma> G (NLogical l) (paper_logical_type l)"
  unfolding paper_R_in_language_def by (rule conjI[OF paper_R_has_type.Logical[OF rt]]; simp)

lemma paper_R_empty_assignment_typed:
  "named_env_typed D G Map.empty"
  by (simp add: named_env_typed_def)

lemma paper_R_logical_adequate:
  "named_adequate g (NLogical l)"
  by (simp add: named_adequate_def)

context paper_R_bbk_model
begin

lemma paper_R_logical_denote_empty:
  assumes rt: "paper_R_type (paper_logical_type l)" and typed: "named_env_typed domain stock g"
  shows "denote g (NLogical l) = denote Map.empty (NLogical l)"
  by (rule denote_locality[OF paper_R_logical_language[OF rt] typed paper_R_empty_assignment_typed
    paper_R_logical_adequate paper_R_logical_adequate]; simp)

lemma paper_R_logical_denote_type:
  assumes rt: "paper_R_type (paper_logical_type l)"
  shows "denote Map.empty (NLogical l) \<in> domain (paper_logical_type l)"
  by (rule denote_type[OF paper_R_logical_language[OF rt] paper_R_empty_assignment_typed paper_R_logical_adequate])

lemma paper_R_negation_application_truth:
  assumes member: "a \<in> domain Prop"
  shows "valuation (paper_R_application signature stock domain denote Prop Prop
    (denote Map.empty (NLogical SNot)) a) = (\<not> valuation a)"
proof -
  have pr: "paper_R_type Prop" by simp
  have nr: "paper_R_type (paper_logical_type SNot)" by simp
  obtain n where nt: "stock n = Prop" and nf: "n \<notin> {}"
    by (rule paper_R_rich_fresh[OF stock_rich pr finite.emptyI])
  let ?g = "Map.empty(n := Some a)"
  have at: "a \<in> domain (stock n)" by (simp only: nt; rule member)
  have gt: "named_env_typed domain stock ?g"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF paper_R_empty_assignment_typed at])
  have vl: "paper_R_in_language signature stock (NVar n) Prop"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt pr])
  have nl: "paper_R_in_language signature stock (NLogical SNot) (Arr Prop Prop)"
    using paper_R_logical_language[where \<Sigma>=signature and G=stock, OF nr] by simp
  have va: "named_adequate ?g (NVar n :: 'c paper_named_term)"
    by (simp add: named_adequate_def dom_def)
  have whole: "named_adequate ?g (NApp (NLogical SNot) (NVar n) :: 'c paper_named_term)"
    by (simp add: named_adequate_def dom_def)
  have vv: "denote ?g (NVar n) = a" by (rule denote_var[OF gt]; simp)
  have nv: "denote ?g (NLogical SNot) = denote Map.empty (NLogical SNot)"
    by (rule paper_R_logical_denote_empty[OF nr gt])
  have application: "paper_R_application signature stock domain denote Prop Prop
      (denote Map.empty (NLogical SNot)) a = denote ?g (NApp (NLogical SNot) (NVar n))"
    using paper_R_application_denote[OF nl vl gt whole] by (simp only: nv vv)
  show ?thesis by (simp only: application valuation_neg[OF vl gt va] vv)
qed

end

lemma paper_R_logical_morphism_empty:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and rt: "paper_R_type (paper_logical_type l)"
  shows "h (paper_logical_type l) (J Map.empty (NLogical l)) = K Map.empty (NLogical l)"
proof -
  have hom: "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
    by (rule paper_R_bbk_model_morphism_raw[OF morphism])
  have empty: "paper_hom_assignment G h Map.empty = Map.empty"
    by (rule ext; simp add: paper_hom_assignment_def)
  show ?thesis using paper_R_bbk_homomorphism_denote[
    OF hom paper_R_logical_language[OF rt] paper_R_empty_assignment_typed paper_R_logical_adequate]
    by (simp only: empty)
qed

section \<open>Negating an old proposition complements its entire truth profile\<close>

lemma paper_R_negation_profile_value:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj" and member: "a \<in> paper_bbk_domain M Prop"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
  shows "paper_bbk_valuation (paper_arrow_target h)
      (paper_arrow_map h Prop (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
        Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a)) =
    (\<not> paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop a))"
proof -
  interpret Source: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF category object]])
  have hm: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source h) (paper_arrow_target h) (paper_arrow_map h)"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF category arrow]])
  have morphism: "paper_R_bbk_model_morphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
    (paper_bbk_valuation (paper_arrow_target h)) (paper_arrow_map h)"
    using hm by (simp only: paper_R_bbk_data_morphism_def source)
  interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain (paper_arrow_target h)"
    "paper_bbk_denote (paper_arrow_target h)" "paper_bbk_valuation (paper_arrow_target h)"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  have nr: "paper_R_type (paper_logical_type SNot)" and rt: "paper_R_type (Arr Prop Prop)" by simp_all
  have neg_type: "paper_bbk_denote M Map.empty (NLogical SNot) \<in> paper_bbk_domain M (Arr Prop Prop)"
    using Source.paper_R_logical_denote_type[OF nr] by simp
  have mapped: "paper_arrow_map h Prop a \<in> paper_bbk_domain (paper_arrow_target h) Prop"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] member])
  have logical: "paper_arrow_map h (Arr Prop Prop) (paper_bbk_denote M Map.empty (NLogical SNot)) =
    paper_bbk_denote (paper_arrow_target h) Map.empty (NLogical SNot)"
    using paper_R_logical_morphism_empty[OF morphism nr] by simp
  have application: "paper_arrow_map h Prop (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a) =
    paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
      Prop Prop (paper_bbk_denote (paper_arrow_target h) Map.empty (NLogical SNot)) (paper_arrow_map h Prop a)"
    using paper_R_application_morphism[OF morphism rt neg_type member] by (simp only: logical)
  show ?thesis by (simp only: application; rule Target.paper_R_negation_application_truth[OF mapped])
qed

theorem paper_R_negation_truth_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj" and member: "a \<in> paper_bbk_domain M Prop"
  shows "paper_bbk_truth_profile_on Arrows M
      (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
        Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a) =
    paper_outgoing Arrows paper_arrow_source M - paper_bbk_truth_profile_on Arrows M a"
proof (rule set_eqI)
  fix h
  show "(h \<in> paper_bbk_truth_profile_on Arrows M
      (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
        Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a)) =
    (h \<in> paper_outgoing Arrows paper_arrow_source M - paper_bbk_truth_profile_on Arrows M a)"
  proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M")
    case True
    have ha: "h \<in> Arrows" and hs: "paper_arrow_source h = M" using True by blast+
    show ?thesis
      by (simp only: paper_bbk_truth_profile_on_member paper_outgoing_member Diff_iff
        paper_R_negation_profile_value[OF category object member ha hs]; blast)
  next
    case False
    show ?thesis using False by (auto simp only: paper_bbk_truth_profile_on_member paper_outgoing_member)
  qed
qed

end
