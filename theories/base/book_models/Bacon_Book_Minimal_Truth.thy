theory Bacon_Book_Minimal_Truth
  imports Bacon_Book_Full_Minimal_Model Bacon_Book_Minimal_Formula_Syntax
begin

section \<open>Truth of the book's literal minimal-basis formulas\<close>

text \<open>
  A→B has material truth conditions and ∀n.A is true exactly when every
  typed update at n makes A true. The false-proposition clause makes
  ⊥ = ∀t(λp.p) false. Applying ¬ = λp.(p→⊥) therefore reverses truth.
  Source: Table 4.1, p.93; Chapter 5, pp.97–98; Definition 15.1,
  pp.314–315, in Bacon's book.

  Representation. The primitive clauses concern κ values, which the
  witnessed-definedness field identifies with their logical-term
  denotations. Abstraction uses the already proved full λ application
  equation. Negation is never redefined as an inline implication. These
  are conditional semantic consequences of book_full_minimal_model,
  not H rules, Functionality, actual-identity principles, or completeness.
\<close>

context book_full_minimal_model
begin

lemma book_imp_denote:
  assumes typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "denote g (book_imp A B) = app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g A)) (denote g B)"
proof -
  have partial_language: "book_in_language book_minimal_logical_type UNIV signature stock (NApp (NLogical SImp) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_imp_operator_language A])
  have partial: "denote g (NApp (NLogical SImp) A) = app Prop (Arr Prop Prop) (denote g (NLogical SImp)) (denote g A)"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I book_imp_operator_language A typed])
  have application: "denote g (book_imp A B) = app Prop Prop (denote g (NApp (NLogical SImp) A)) (denote g B)"
    unfolding book_imp_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial_language B typed])
  show ?thesis by (simp only: application partial book_minimal_logical_value_at[OF typed])
qed

theorem book_imp_truth:
  assumes typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "V (denote g (book_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
proof -
  have am: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I A typed])
  have bm: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I B typed])
  show ?thesis by (simp only: book_imp_denote[OF typed A B]; rule implication_truth[OF am bm])
qed

lemma book_forall_application_truth:
  assumes typed: "book_env_typed domain stock g"
    and F: "book_in_language book_minimal_logical_type UNIV signature stock F (Arr \<sigma> Prop)"
  shows "V (denote g (NApp (NLogical (SBAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop (denote g F) a))"
proof -
  have member: "denote g F \<in> domain (Arr \<sigma> Prop)" by (rule denote_type[OF UNIV_I F typed])
  have application: "denote g (NApp (NLogical (SBAll \<sigma>)) F) =
    app (Arr \<sigma> Prop) Prop (denote g (NLogical (SBAll \<sigma>))) (denote g F)"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I book_all_operator_language F typed])
  show ?thesis by (simp only: application book_minimal_logical_value_at[OF typed]; rule forall_truth[OF member])
qed

theorem book_all_truth:
  assumes typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
  shows "V (denote g (book_all stock n A)) = (\<forall>a \<in> domain (stock n). V (denote (g(n := a)) A))"
proof -
  have predicate_language: "book_in_language book_minimal_logical_type UNIV signature stock (NLam n A) (Arr (stock n) Prop)"
    by (rule book_language_Lam[OF A])
  have predicate_member: "denote g (NLam n A) \<in> domain (Arr (stock n) Prop)"
    by (rule denote_type[OF UNIV_I predicate_language typed])
  have application: "denote g (book_all stock n A) =
    app (Arr (stock n) Prop) Prop (denote g (NLogical (SBAll (stock n)))) (denote g (NLam n A))"
    unfolding book_all_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I book_all_operator_language predicate_language typed])
  have primitive: "V (denote g (book_all stock n A)) =
    (\<forall>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n A)) a))"
    by (simp only: application book_minimal_logical_value_at[OF typed]; rule forall_truth[OF predicate_member])
  have body: "(\<forall>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n A)) a)) =
    (\<forall>a \<in> domain (stock n). V (denote (g(n := a)) A))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> domain (stock n)"
    show "V (app (stock n) Prop (denote g (NLam n A)) a) = V (denote (g(n := a)) A)"
      by (simp only: book_full_lambda_application[OF A typed member])
  qed
  show ?thesis by (rule trans[OF primitive body])
qed

theorem book_bottom_false:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "\<not> V (denote g (book_bottom stock))"
proof
  assume truth: "V (denote g (book_bottom stock))"
  let ?p = "book_prop_name stock"
  have ptype: "stock ?p = Prop" by (rule book_prop_name_type[OF rich])
  have variable_language: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?p) Prop"
    by (simp only: book_language_var_iff ptype)
  have universal: "V (denote g (book_bottom stock)) =
    (\<forall>a \<in> domain Prop. V (denote (g(?p := a)) (NVar ?p)))"
    using book_all_truth[where n="?p", OF typed variable_language]
    by (simp only: book_bottom_as_all[OF rich] ptype)
  have every: "\<forall>a \<in> domain Prop. V (denote (g(?p := a)) (NVar ?p))" using truth by (simp only: universal)
  obtain f where fm: "f \<in> domain Prop" and false_f: "\<not> V f" using false_proposition by (elim bexE)
  have f_named: "f \<in> domain (stock ?p)" by (simp only: ptype; rule fm)
  have updated: "book_env_typed domain stock (g(?p := f))" by (rule book_env_update[OF typed f_named])
  have variable_value: "denote (g(?p := f)) (NVar ?p) = f"
    using denote_var[where n="?p", OF UNIV_I updated] by simp
  have impossible: "V (denote (g(?p := f)) (NVar ?p))" by (rule bspec[OF every fm])
  have Vf: "V f" using impossible by (simp only: variable_value)
  show False by (rule notE[OF false_f Vf])
qed

theorem book_not_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
  shows "V (denote g (book_not stock A)) = (\<not> V (denote g A))"
proof -
  let ?p = "book_prop_name stock"
  let ?body = "book_imp (NVar ?p) (book_bottom stock)"
  let ?a = "denote g A"
  let ?h = "g(?p := ?a)"
  have ptype: "stock ?p = Prop" by (rule book_prop_name_type[OF rich])
  have variable_language: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?p) Prop"
    by (simp only: book_language_var_iff ptype)
  have bottom_language: "book_in_language book_minimal_logical_type UNIV signature stock (book_bottom stock) Prop"
    by (rule book_bottom_language[OF rich])
  have body_language: "book_in_language book_minimal_logical_type UNIV signature stock ?body Prop"
    by (rule book_imp_language[OF variable_language bottom_language])
  have am: "?a \<in> domain Prop" by (rule denote_type[OF UNIV_I A typed])
  have a_named: "?a \<in> domain (stock ?p)" by (simp only: ptype; rule am)
  have updated: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed a_named])
  have application: "denote g (book_not stock A) = app Prop Prop (denote g (NLam ?p ?body)) ?a"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_not_const_language[OF rich] A typed]
    by (simp only: book_not_def book_not_const_def)
  have beta: "app Prop Prop (denote g (NLam ?p ?body)) ?a = denote ?h ?body"
    using book_full_lambda_application[OF body_language typed a_named] by (simp only: ptype)
  have value_eq: "denote g (book_not stock A) = denote ?h ?body" by (rule trans[OF application beta])
  have variable_value: "denote ?h (NVar ?p) = ?a" using denote_var[where n="?p", OF UNIV_I updated] by simp
  have false_bottom: "\<not> V (denote ?h (book_bottom stock))" by (rule book_bottom_false[OF rich updated])
  have body_truth: "V (denote ?h ?body) = (\<not> V ?a)"
    using book_imp_truth[OF updated variable_language bottom_language] false_bottom by (simp add: variable_value)
  show ?thesis by (simp only: value_eq; rule body_truth)
qed

end

end
