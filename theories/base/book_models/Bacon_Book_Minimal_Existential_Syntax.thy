theory Bacon_Book_Minimal_Existential_Syntax
  imports Bacon_Book_Minimal_Formula_Syntax
begin

section \<open>The book's literal existential operator\<close>

text \<open>
  ∃σ = λX.¬(∀σ y.¬(X y)), with X:σ→t and y:σ distinct.
  The formula ∃n.A applies this closed operator to λn.A.
  Source: Bacon, Table 4.1, p.93.

  Representation. The logical symbol inside the definition is literally
  SBAll σ. A rich typed stock supplies X and a distinct y. Arguments are
  outside the operator's binders; they are not inserted into its body.
  These are syntax and language facts for full F and the minimal logical
  basis, not additional quantifier axioms or substitution principles.
\<close>

definition book_exists_function_name :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat" where
  "book_exists_function_name G \<sigma> = named_chart_fresh G [] (Arr \<sigma> Prop)"

definition book_exists_argument_name :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat" where
  "book_exists_argument_name G \<sigma> = named_chart_fresh G [book_exists_function_name G \<sigma>] \<sigma>"

definition book_exists_const :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term" where
  "book_exists_const G \<sigma> = NLam (book_exists_function_name G \<sigma>)
    (book_not G (NApp (NLogical (SBAll \<sigma>))
      (NLam (book_exists_argument_name G \<sigma>)
        (book_not G (NApp (NVar (book_exists_function_name G \<sigma>))
          (NVar (book_exists_argument_name G \<sigma>)))))))"

definition book_exists :: "sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_exists G n A = NApp (book_exists_const G (G n)) (NLam n A)"

lemma book_exists_function_name_type:
  "sg_rich G \<Longrightarrow> G (book_exists_function_name G \<sigma>) = Arr \<sigma> Prop"
  unfolding book_exists_function_name_def by (rule named_chart_fresh_type; assumption)

lemma book_exists_argument_name_type:
  "sg_rich G \<Longrightarrow> G (book_exists_argument_name G \<sigma>) = \<sigma>"
  unfolding book_exists_argument_name_def by (rule named_chart_fresh_type; assumption)

lemma book_exists_names_distinct:
  assumes rich: "sg_rich G"
  shows "book_exists_function_name G \<sigma> \<noteq> book_exists_argument_name G \<sigma>"
  using named_chart_fresh_notin[where ns="[book_exists_function_name G \<sigma>]" and \<sigma>="\<sigma>", OF rich]
  by (simp add: book_exists_argument_name_def)

lemma book_exists_const_as_all:
  assumes rich: "sg_rich G"
  shows "book_exists_const G \<sigma> = NLam (book_exists_function_name G \<sigma>)
    (book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp (NVar (book_exists_function_name G \<sigma>))
        (NVar (book_exists_argument_name G \<sigma>))))))"
  by (simp only: book_exists_const_def book_all_def book_exists_argument_name_type[OF rich])

lemma book_exists_test_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NApp (NVar (book_exists_function_name G \<sigma>)) (NVar (book_exists_argument_name G \<sigma>))) Prop"
proof -
  have head_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NVar (book_exists_function_name G \<sigma>)) (Arr \<sigma> Prop)"
    by (simp only: book_language_var_iff book_exists_function_name_type[OF rich])
  have argument_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NVar (book_exists_argument_name G \<sigma>)) \<sigma>"
    by (simp only: book_language_var_iff book_exists_argument_name_type[OF rich])
  show ?thesis by (rule book_language_App[OF head_language argument_language])
qed

lemma book_exists_body_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_not G (book_all G (book_exists_argument_name G \<sigma>)
      (book_not G (NApp (NVar (book_exists_function_name G \<sigma>))
        (NVar (book_exists_argument_name G \<sigma>)))))) Prop"
  by (rule book_not_language[OF rich book_all_language[OF
        book_not_language[OF rich book_exists_test_language[OF rich]]]])

lemma book_exists_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_exists_const G \<sigma>) (Arr (Arr \<sigma> Prop) Prop)"
  using book_language_Lam[where n="book_exists_function_name G \<sigma>", OF book_exists_body_language[OF rich]]
  by (simp only: book_exists_const_as_all[OF rich] book_exists_function_name_type[OF rich])

lemma book_exists_application_language:
  assumes rich: "sg_rich G"
    and F: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp (book_exists_const G \<sigma>) F) Prop"
  by (rule book_language_App[OF book_exists_const_language[OF rich] F])

lemma book_exists_language:
  assumes rich: "sg_rich G"
    and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_exists G n A) Prop"
  unfolding book_exists_def by (rule book_exists_application_language[OF rich book_language_Lam[OF A]])

lemma book_exists_const_closed: "named_fv (book_exists_const G \<sigma>) = {}"
  by (auto simp: book_exists_const_def book_not_fv)

lemma book_exists_application_fv:
  "named_fv (NApp (book_exists_const G \<sigma>) F) = named_fv F"
  by (simp add: book_exists_const_closed)

lemma book_exists_fv: "named_fv (book_exists G n A) = named_fv A - {n}"
  by (simp add: book_exists_def book_exists_const_closed)

lemma book_exists_const_type:
  assumes rich: "sg_rich G"
  shows "has_ntype book_minimal_logical_type G (book_exists_const G \<sigma>) (Arr (Arr \<sigma> Prop) Prop)"
  by (rule book_language_type[OF book_exists_const_language[where \<Sigma>="\<lambda>_. {}", OF rich]])

end
