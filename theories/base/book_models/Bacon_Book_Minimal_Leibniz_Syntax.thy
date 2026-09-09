theory Bacon_Book_Minimal_Leibniz_Syntax
  imports Bacon_Book_Minimal_Boolean_Syntax
begin

section \<open>The literal two-argument Leibniz operator of Table 4.1\<close>

text \<open>
  Define =σ by λx:σ.λy:σ.∀Z:σ → t.(Zx ↔ Zy), retaining the
  literal λ-defined biconditional and the binder-form universal.
  Source: Table 4.1 and Definition 4.4, p.93. This defines a Leibniz
  operator in the minimal basis; it does not assert identity with any
  additional primitive identity symbol.

  Representation: x,y,Z are chosen distinct even when their types
  coincide. book_leibniz applies the closed operator twice to its actual
  arguments; no substitution or β simplification occurs in its definition.
  Status: syntax, language and FV facts only, with rich G for chosen types.
\<close>

definition book_leibniz_x :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat" where
  "book_leibniz_x G \<sigma> = named_chart_fresh G [] \<sigma>"
definition book_leibniz_y :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat" where
  "book_leibniz_y G \<sigma> = named_chart_fresh G [book_leibniz_x G \<sigma>] \<sigma>"
definition book_leibniz_z :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat" where
  "book_leibniz_z G \<sigma> = named_chart_fresh G [book_leibniz_x G \<sigma>, book_leibniz_y G \<sigma>] (Arr \<sigma> Prop)"

lemma book_leibniz_name_types:
  assumes rich: "sg_rich G"
  shows "G (book_leibniz_x G \<sigma>) = \<sigma>"
    and "G (book_leibniz_y G \<sigma>) = \<sigma>"
    and "G (book_leibniz_z G \<sigma>) = Arr \<sigma> Prop"
  unfolding book_leibniz_x_def book_leibniz_y_def book_leibniz_z_def
  by (rule named_chart_fresh_type[OF rich])+

lemma book_leibniz_names_distinct:
  assumes rich: "sg_rich G"
  shows "book_leibniz_x G \<sigma> \<noteq> book_leibniz_y G \<sigma>"
    and "book_leibniz_x G \<sigma> \<noteq> book_leibniz_z G \<sigma>"
    and "book_leibniz_y G \<sigma> \<noteq> book_leibniz_z G \<sigma>"
proof -
  have y_fresh: "book_leibniz_y G \<sigma> \<notin> set [book_leibniz_x G \<sigma>]"
    unfolding book_leibniz_y_def by (rule named_chart_fresh_notin[OF rich])
  have z_fresh: "book_leibniz_z G \<sigma> \<notin> set [book_leibniz_x G \<sigma>, book_leibniz_y G \<sigma>]"
    unfolding book_leibniz_z_def by (rule named_chart_fresh_notin[OF rich])
  show "book_leibniz_x G \<sigma> \<noteq> book_leibniz_y G \<sigma>"
    and "book_leibniz_x G \<sigma> \<noteq> book_leibniz_z G \<sigma>"
    and "book_leibniz_y G \<sigma> \<noteq> book_leibniz_z G \<sigma>" using y_fresh z_fresh by auto
qed

definition book_leibniz_matrix :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term" where
  "book_leibniz_matrix G \<sigma> = book_iff G
    (NApp (NVar (book_leibniz_z G \<sigma>)) (NVar (book_leibniz_x G \<sigma>)))
    (NApp (NVar (book_leibniz_z G \<sigma>)) (NVar (book_leibniz_y G \<sigma>)))"
definition book_leibniz_body :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term" where
  "book_leibniz_body G \<sigma> = book_all G (book_leibniz_z G \<sigma>) (book_leibniz_matrix G \<sigma>)"
definition book_leibniz_const :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term" where
  "book_leibniz_const G \<sigma> = NLam (book_leibniz_x G \<sigma>)
    (NLam (book_leibniz_y G \<sigma>) (book_leibniz_body G \<sigma>))"
definition book_leibniz :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_leibniz G \<sigma> A B = NApp (NApp (book_leibniz_const G \<sigma>) A) B"

lemma book_leibniz_variables_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_leibniz_x G \<sigma>)) \<sigma>"
    and "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_leibniz_y G \<sigma>)) \<sigma>"
    and "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_leibniz_z G \<sigma>)) (Arr \<sigma> Prop)"
  by (simp_all only: book_language_var_iff book_leibniz_name_types[OF rich])

lemma book_leibniz_matrix_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_leibniz_matrix G \<sigma>) Prop"
  unfolding book_leibniz_matrix_def
  by (rule book_iff_language[OF rich book_language_App[OF book_leibniz_variables_language(3)[OF rich]
    book_leibniz_variables_language(1)[OF rich]] book_language_App[OF book_leibniz_variables_language(3)[OF rich]
    book_leibniz_variables_language(2)[OF rich]]])

lemma book_leibniz_body_language:
  "sg_rich G \<Longrightarrow> book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_leibniz_body G \<sigma>) Prop"
  unfolding book_leibniz_body_def by (rule book_all_language, rule book_leibniz_matrix_language, assumption)

lemma book_leibniz_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_leibniz_const G \<sigma>) (Arr \<sigma> (Arr \<sigma> Prop))"
proof -
  have body: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_leibniz_body G \<sigma>) Prop"
    by (rule book_leibniz_body_language[OF rich])
  have abstraction: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam (book_leibniz_x G \<sigma>) (NLam (book_leibniz_y G \<sigma>) (book_leibniz_body G \<sigma>)))
    (Arr (G (book_leibniz_x G \<sigma>)) (Arr (G (book_leibniz_y G \<sigma>)) Prop))"
    by (rule book_language_Lam, rule book_language_Lam, rule body)
  show ?thesis using abstraction
    by (simp only: book_leibniz_const_def book_leibniz_name_types[OF rich])
qed

lemma book_leibniz_language:
  assumes rich: "sg_rich G"
    and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and B: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_leibniz G \<sigma> A B) Prop"
  unfolding book_leibniz_def
  by (rule book_language_App[OF book_language_App[OF book_leibniz_const_language[OF rich] A] B])

lemma book_leibniz_const_closed: "named_fv (book_leibniz_const G \<sigma>) = {}"
  by (auto simp: book_leibniz_const_def book_leibniz_body_def book_leibniz_matrix_def book_all_fv book_iff_fv)

lemma book_leibniz_fv: "named_fv (book_leibniz G \<sigma> A B) = named_fv A \<union> named_fv B"
  by (simp add: book_leibniz_def book_leibniz_const_closed)

end
