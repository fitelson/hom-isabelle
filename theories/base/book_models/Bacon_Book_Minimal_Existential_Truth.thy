theory Bacon_Book_Minimal_Existential_Truth
  imports Bacon_Book_Minimal_Existential_Syntax Bacon_Book_Minimal_Truth
begin

section \<open>Truth of the literal existential operator\<close>

text \<open>
  ∃σF is true exactly when some a∈Dσ makes F a true; consequently,
  ∃n.A is true exactly when some typed update at n makes A true.
  Source: Bacon, Table 4.1, p.93, together with Definition 15.1,
  pp.314–315.

  Representation. We evaluate the closed λX.¬(∀σ y.¬(X y)) operator
  by full λ application. The original value of F is stored before
  updating X and y. Their distinctness preserves that value; no
  freshness condition on F or capture-prone textual inlining is used.
  These results are conditional on book_full_minimal_model. No new
  semantic field, H rule, equality principle, or Functionality is added.
\<close>

context book_full_minimal_model
begin

lemma book_exists_updates_typed:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and fm: "f \<in> domain (Arr \<sigma> Prop)" and am: "a \<in> domain \<sigma>"
  shows "book_env_typed domain stock
    ((g(book_exists_function_name stock \<sigma> := f))(book_exists_argument_name stock \<sigma> := a))"
proof -
  have fn: "f \<in> domain (stock (book_exists_function_name stock \<sigma>))"
    by (simp only: book_exists_function_name_type[OF rich]; rule fm)
  have an: "a \<in> domain (stock (book_exists_argument_name stock \<sigma>))"
    by (simp only: book_exists_argument_name_type[OF rich]; rule am)
  show ?thesis by (rule book_env_update[OF book_env_update[OF typed fn] an])
qed

lemma book_exists_test_denote:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and fm: "f \<in> domain (Arr \<sigma> Prop)" and am: "a \<in> domain \<sigma>"
  shows "denote ((g(book_exists_function_name stock \<sigma> := f))(book_exists_argument_name stock \<sigma> := a))
    (NApp (NVar (book_exists_function_name stock \<sigma>)) (NVar (book_exists_argument_name stock \<sigma>))) = app \<sigma> Prop f a"
proof -
  let ?X = "book_exists_function_name stock \<sigma>"
  let ?y = "book_exists_argument_name stock \<sigma>"
  let ?h = "(g(?X := f))(?y := a)"
  have updated: "book_env_typed domain stock ?h" by (rule book_exists_updates_typed[OF rich typed fm am])
  have head_language: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?X) (Arr \<sigma> Prop)"
    by (simp only: book_language_var_iff book_exists_function_name_type[OF rich])
  have argument_language: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?y) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  have head_value: "denote ?h (NVar ?X) = f"
    using denote_var[where n="?X", OF UNIV_I updated] book_exists_names_distinct[OF rich, of \<sigma>] by simp
  have argument_value: "denote ?h (NVar ?y) = a"
    using denote_var[where n="?y", OF UNIV_I updated] by simp
  have application: "denote ?h (NApp (NVar ?X) (NVar ?y)) =
    app \<sigma> Prop (denote ?h (NVar ?X)) (denote ?h (NVar ?y))"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I head_language argument_language updated])
  show ?thesis by (simp only: application head_value argument_value)
qed

theorem book_exists_application_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and F: "book_in_language book_minimal_logical_type UNIV signature stock F (Arr \<sigma> Prop)"
  shows "V (denote g (NApp (book_exists_const stock \<sigma>) F)) =
    (\<exists>a \<in> domain \<sigma>. V (app \<sigma> Prop (denote g F) a))"
proof -
  let ?X = "book_exists_function_name stock \<sigma>"
  let ?y = "book_exists_argument_name stock \<sigma>"
  let ?test = "NApp (NVar ?X) (NVar ?y)"
  let ?inner = "book_not stock ?test"
  let ?quantified = "book_all stock ?y ?inner"
  let ?body = "book_not stock ?quantified"
  let ?f = "denote g F"
  let ?h = "g(?X := ?f)"
  have Xtype: "stock ?X = Arr \<sigma> Prop" by (rule book_exists_function_name_type[OF rich])
  have ytype: "stock ?y = \<sigma>" by (rule book_exists_argument_name_type[OF rich])
  have test_language: "book_in_language book_minimal_logical_type UNIV signature stock ?test Prop"
    by (rule book_exists_test_language[OF rich])
  have inner_language: "book_in_language book_minimal_logical_type UNIV signature stock ?inner Prop"
    by (rule book_not_language[OF rich test_language])
  have quantified_language: "book_in_language book_minimal_logical_type UNIV signature stock ?quantified Prop"
    by (rule book_all_language[OF inner_language])
  have body_language: "book_in_language book_minimal_logical_type UNIV signature stock ?body Prop"
    by (rule book_not_language[OF rich quantified_language])
  have fm: "?f \<in> domain (Arr \<sigma> Prop)" by (rule denote_type[OF UNIV_I F typed])
  have fn: "?f \<in> domain (stock ?X)" by (simp only: Xtype; rule fm)
  have updated: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed fn])
  have application: "denote g (NApp (book_exists_const stock \<sigma>) F) =
    app (Arr \<sigma> Prop) Prop (denote g (NLam ?X ?body)) ?f"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_exists_const_language[OF rich] F typed]
    by (simp only: book_exists_const_as_all[OF rich])
  have beta: "app (Arr \<sigma> Prop) Prop (denote g (NLam ?X ?body)) ?f = denote ?h ?body"
    using book_full_lambda_application[OF body_language typed fn] by (simp only: Xtype)
  have value_eq: "denote g (NApp (book_exists_const stock \<sigma>) F) = denote ?h ?body"
    by (rule trans[OF application beta])
  have inner_truth: "\<And>a. a \<in> domain \<sigma> \<Longrightarrow>
    V (denote (?h(?y := a)) ?inner) = (\<not> V (app \<sigma> Prop ?f a))"
  proof -
    fix a
    assume am: "a \<in> domain \<sigma>"
    have twice_typed: "book_env_typed domain stock (?h(?y := a))"
      by (rule book_exists_updates_typed[OF rich typed fm am])
    have test_value: "denote (?h(?y := a)) ?test = app \<sigma> Prop ?f a"
      by (rule book_exists_test_denote[OF rich typed fm am])
    show "V (denote (?h(?y := a)) ?inner) = (\<not> V (app \<sigma> Prop ?f a))"
      by (simp only: book_not_truth[OF rich twice_typed test_language] test_value)
  qed
  have all_truth: "V (denote ?h ?quantified) = (\<forall>a \<in> domain \<sigma>. \<not> V (app \<sigma> Prop ?f a))"
  proof -
    have primitive: "V (denote ?h ?quantified) = (\<forall>a \<in> domain \<sigma>. V (denote (?h(?y := a)) ?inner))"
      using book_all_truth[where n="?y", OF updated inner_language] by (simp only: ytype)
    have bodies: "(\<forall>a \<in> domain \<sigma>. V (denote (?h(?y := a)) ?inner)) =
      (\<forall>a \<in> domain \<sigma>. \<not> V (app \<sigma> Prop ?f a))"
      by (rule ball_cong[OF refl]; rule inner_truth; assumption)
    show ?thesis by (rule trans[OF primitive bodies])
  qed
  show ?thesis
    by (simp only: value_eq book_not_truth[OF rich updated quantified_language] all_truth; simp)
qed

theorem book_exists_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
  shows "V (denote g (book_exists stock n A)) =
    (\<exists>a \<in> domain (stock n). V (denote (g(n := a)) A))"
proof -
  have predicate_language: "book_in_language book_minimal_logical_type UNIV signature stock (NLam n A) (Arr (stock n) Prop)"
    by (rule book_language_Lam[OF A])
  have predicate_truth: "V (denote g (book_exists stock n A)) =
    (\<exists>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n A)) a))"
    unfolding book_exists_def by (rule book_exists_application_truth[OF rich typed predicate_language])
  have bodies: "(\<exists>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n A)) a)) =
    (\<exists>a \<in> domain (stock n). V (denote (g(n := a)) A))"
  proof (rule bex_cong[OF refl])
    fix a
    assume am: "a \<in> domain (stock n)"
    show "V (app (stock n) Prop (denote g (NLam n A)) a) = V (denote (g(n := a)) A)"
      by (simp only: book_full_lambda_application[OF A typed am])
  qed
  show ?thesis by (rule trans[OF predicate_truth bodies])
qed

end

end
