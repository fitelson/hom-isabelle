theory Bacon_Source_Relational_Binary_Logical_Application
  imports Bacon_Source_Relational_Negation_Profile
begin

section \<open>Two independent variable witnesses for a binary logical value\<close>

text \<open>
  Interpret a logical l:σ→σ→t at two arbitrary values a,b∈Dσ
  by two DISTINCT σ-variable names and the assignment [x↦a,y↦b].
  Source: Definitions 3.1 and 3.3, pp.43–46. The saturated
  valuation clause then gives its all-domain truth condition.

  The generic lemma states that clause explicitly as a hypothesis,
  to be discharged by the actual ∧, ∨ or =σ model clause.
  It does not add a new field or logical operation. The same-variable
  name for both witnesses would wrongly identify their values and
  is not used. No total completion, F model or Functionality occurs.
\<close>

definition paper_R_binary_logical_application ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    otype \<Rightarrow> paper_logical \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
  "paper_R_binary_logical_application \<Sigma> G D J \<sigma> l a b =
    paper_R_application \<Sigma> G D J \<sigma> Prop
      (paper_R_application \<Sigma> G D J \<sigma> (Arr \<sigma> Prop) (J Map.empty (NLogical l)) a) b"

context paper_R_bbk_model
begin

theorem paper_R_binary_logical_application_truth:
  assumes sr: "paper_R_type \<sigma>" and symbol: "paper_logical_type l = Arr \<sigma> (Arr \<sigma> Prop)"
    and am: "a \<in> domain \<sigma>" and bm: "b \<in> domain \<sigma>"
    and clause: "\<And>P Q g. paper_R_in_language signature stock P \<sigma> \<Longrightarrow>
      paper_R_in_language signature stock Q \<sigma> \<Longrightarrow> named_env_typed domain stock g \<Longrightarrow>
      named_adequate g P \<Longrightarrow> named_adequate g Q \<Longrightarrow>
      valuation (denote g (NApp (NApp (NLogical l) P) Q)) = test (denote g P) (denote g Q)"
  shows "valuation (paper_R_binary_logical_application signature stock domain denote \<sigma> l a b) = test a b"
proof -
  obtain x where xt: "stock x = \<sigma>" and xf: "x \<notin> {}"
    by (rule paper_R_rich_fresh[OF stock_rich sr finite.emptyI])
  have finite_x: "finite {x}" by simp
  obtain y where yt: "stock y = \<sigma>" and yf: "y \<notin> {x}"
    by (rule paper_R_rich_fresh[OF stock_rich sr finite_x])
  have distinct: "x \<noteq> y" using yf by auto
  let ?g = "(Map.empty(x := Some a))(y := Some b)"
  have ax: "a \<in> domain (stock x)" by (simp only: xt; rule am)
  have b_type: "b \<in> domain (stock y)" by (simp only: yt; rule bm)
  have first_typed: "named_env_typed domain stock (Map.empty(x := Some a))"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF paper_R_empty_assignment_typed ax])
  have typed: "named_env_typed domain stock ?g"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF first_typed b_type])
  have gx: "?g x = Some a" by (simp add: distinct)
  have gy: "?g y = Some b" by simp
  have pl: "paper_R_in_language signature stock (NVar x) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=x, OF xt sr])
  have ql: "paper_R_in_language signature stock (NVar y) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=y, OF yt sr])
  have lr: "paper_R_type (paper_logical_type l)" by (simp add: symbol sr)
  have ll: "paper_R_in_language signature stock (NLogical l) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_R_logical_language[where \<Sigma>=signature and G=stock and l=l, OF lr] by (simp only: symbol)
  have partial_language: "paper_R_in_language signature stock (NApp (NLogical l) (NVar x)) (Arr \<sigma> Prop)"
    by (rule paper_R_language_App[OF ll pl])
  have pa: "named_adequate ?g (NVar x :: 'c paper_named_term)"
    and qa: "named_adequate ?g (NVar y :: 'c paper_named_term)"
    and partial_adequate: "named_adequate ?g (NApp (NLogical l) (NVar x) :: 'c paper_named_term)"
    and whole_adequate: "named_adequate ?g (NApp (NApp (NLogical l) (NVar x)) (NVar y) :: 'c paper_named_term)"
    by (simp_all add: named_adequate_def dom_def distinct)
  have pv: "denote ?g (NVar x) = a" by (rule denote_var[OF typed gx])
  have qv: "denote ?g (NVar y) = b" by (rule denote_var[OF typed gy])
  have lv: "denote ?g (NLogical l) = denote Map.empty (NLogical l)"
    by (rule paper_R_logical_denote_empty[OF lr typed])
  have first_application: "paper_R_application signature stock domain denote \<sigma> (Arr \<sigma> Prop)
      (denote Map.empty (NLogical l)) a = denote ?g (NApp (NLogical l) (NVar x))"
    using paper_R_application_denote[OF ll pl typed partial_adequate] by (simp only: lv pv)
  have second_application: "paper_R_binary_logical_application signature stock domain denote \<sigma> l a b =
    denote ?g (NApp (NApp (NLogical l) (NVar x)) (NVar y))"
    using paper_R_application_denote[OF partial_language ql typed whole_adequate]
    by (simp only: paper_R_binary_logical_application_def first_application qv)
  show ?thesis by (simp only: second_application clause[OF pl ql typed pa qa] pv qv)
qed

end

section \<open>Binary logical application commutes with every R homomorphism\<close>

theorem paper_R_binary_logical_application_morphism:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and sr: "paper_R_type \<sigma>" and symbol: "paper_logical_type l = Arr \<sigma> (Arr \<sigma> Prop)"
    and am: "a \<in> D \<sigma>" and bm: "b \<in> D \<sigma>"
  shows "h Prop (paper_R_binary_logical_application \<Sigma> G D J \<sigma> l a b) =
    paper_R_binary_logical_application \<Sigma> G E K \<sigma> l (h \<sigma> a) (h \<sigma> b)"
proof -
  interpret Source: paper_R_bbk_model \<Sigma> G D J V by (rule paper_R_bbk_model_morphism_source[OF morphism])
  have lr: "paper_R_type (paper_logical_type l)" and outer_rt: "paper_R_type (Arr \<sigma> (Arr \<sigma> Prop))"
    and inner_rt: "paper_R_type (Arr \<sigma> Prop)" by (simp_all add: symbol sr)
  have logical_type: "J Map.empty (NLogical l) \<in> D (Arr \<sigma> (Arr \<sigma> Prop))"
    using Source.paper_R_logical_denote_type[OF lr] by (simp only: symbol)
  have partial_type: "paper_R_application \<Sigma> G D J \<sigma> (Arr \<sigma> Prop) (J Map.empty (NLogical l)) a \<in> D (Arr \<sigma> Prop)"
    by (rule Source.paper_R_application_type[OF outer_rt logical_type am])
  have logical_map: "h (Arr \<sigma> (Arr \<sigma> Prop)) (J Map.empty (NLogical l)) = K Map.empty (NLogical l)"
    using paper_R_logical_morphism_empty[OF morphism lr] by (simp only: symbol)
  have first_map: "h (Arr \<sigma> Prop)
      (paper_R_application \<Sigma> G D J \<sigma> (Arr \<sigma> Prop) (J Map.empty (NLogical l)) a) =
    paper_R_application \<Sigma> G E K \<sigma> (Arr \<sigma> Prop) (K Map.empty (NLogical l)) (h \<sigma> a)"
    using paper_R_application_morphism[OF morphism outer_rt logical_type am] by (simp only: logical_map)
  show ?thesis
    unfolding paper_R_binary_logical_application_def
    using paper_R_application_morphism[OF morphism inner_rt partial_type bm]
    by (simp only: first_map)
qed

end
