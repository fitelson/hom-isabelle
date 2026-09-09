theory Bacon_Book_Minimal_Boolean_Syntax
  imports Bacon_Book_Minimal_Formula_Syntax
begin

section \<open>The literal Boolean operators of Table 4.1\<close>

text \<open>
  Define ∨ = λpq.(¬p→q), ∧ = λpq.¬(p→¬q),
  ↔ = λpq.((p→q)∧(q→p)), and ⊤ = ¬⊥.
  Source: Bacon, Table 4.1, p.93.

  Representation. Each binary formula applies its closed operator to A
  and B. The arguments are not inserted into the operator's λ body.
  p is the chosen name already used by bottom and negation; q is a
  distinct propositional name. Repeated names inside closed subordinate
  operators retain their own scopes. No β equation, H rule, truth law,
  or identity of primitive and defined operators is claimed here.
\<close>

definition book_second_prop_name :: "sgcontext \<Rightarrow> nat" where
  "book_second_prop_name G = named_chart_fresh G [book_prop_name G] Prop"

lemma book_second_prop_name_type:
  "sg_rich G \<Longrightarrow> G (book_second_prop_name G) = Prop"
  unfolding book_second_prop_name_def by (rule named_chart_fresh_type; assumption)

lemma book_boolean_names_distinct:
  assumes rich: "sg_rich G"
  shows "book_prop_name G \<noteq> book_second_prop_name G"
  using named_chart_fresh_notin[where ns="[book_prop_name G]" and \<sigma>=Prop, OF rich]
  unfolding book_second_prop_name_def by auto

definition book_or_const :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_or_const G = NLam (book_prop_name G) (NLam (book_second_prop_name G)
    (book_imp (book_not G (NVar (book_prop_name G))) (NVar (book_second_prop_name G))))"
definition book_or :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_or G A B = NApp (NApp (book_or_const G) A) B"

definition book_and_const :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_and_const G = NLam (book_prop_name G) (NLam (book_second_prop_name G)
    (book_not G (book_imp (NVar (book_prop_name G)) (book_not G (NVar (book_second_prop_name G))))))"
definition book_and :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_and G A B = NApp (NApp (book_and_const G) A) B"

definition book_iff_const :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_iff_const G = NLam (book_prop_name G) (NLam (book_second_prop_name G)
    (book_and G (book_imp (NVar (book_prop_name G)) (NVar (book_second_prop_name G)))
      (book_imp (NVar (book_second_prop_name G)) (NVar (book_prop_name G)))))"
definition book_iff :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_iff G A B = NApp (NApp (book_iff_const G) A) B"
definition book_top :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_top G = book_not G (book_bottom G)"

lemma book_boolean_variables_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_prop_name G)) Prop"
    and "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_second_prop_name G)) Prop"
  by (simp_all only: book_language_var_iff book_prop_name_type[OF rich] book_second_prop_name_type[OF rich])

lemma book_boolean_abstraction_language:
  assumes rich: "sg_rich G" and body: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam (book_prop_name G) (NLam (book_second_prop_name G) M)) (Arr Prop (Arr Prop Prop))"
  using book_language_Lam[where n="book_prop_name G", OF book_language_Lam[where n="book_second_prop_name G", OF body]]
  by (simp only: book_prop_name_type[OF rich] book_second_prop_name_type[OF rich])

lemma book_or_body_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_imp (book_not G (NVar (book_prop_name G))) (NVar (book_second_prop_name G))) Prop"
  by (rule book_imp_language[OF book_not_language[OF rich book_boolean_variables_language(1)[OF rich]]
    book_boolean_variables_language(2)[OF rich]])

lemma book_or_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_or_const G) (Arr Prop (Arr Prop Prop))"
  unfolding book_or_const_def by (rule book_boolean_abstraction_language[OF rich book_or_body_language[OF rich]])

lemma book_or_language:
  assumes rich: "sg_rich G" and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_or G A B) Prop"
  unfolding book_or_def by (rule book_language_App[OF book_language_App[OF book_or_const_language[OF rich] A] B])

lemma book_and_body_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_not G (book_imp (NVar (book_prop_name G)) (book_not G (NVar (book_second_prop_name G))))) Prop"
  by (rule book_not_language[OF rich book_imp_language[OF book_boolean_variables_language(1)[OF rich]
    book_not_language[OF rich book_boolean_variables_language(2)[OF rich]]]])

lemma book_and_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_and_const G) (Arr Prop (Arr Prop Prop))"
  unfolding book_and_const_def by (rule book_boolean_abstraction_language[OF rich book_and_body_language[OF rich]])

lemma book_and_language:
  assumes rich: "sg_rich G" and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_and G A B) Prop"
  unfolding book_and_def by (rule book_language_App[OF book_language_App[OF book_and_const_language[OF rich] A] B])

lemma book_iff_body_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_and G (book_imp (NVar (book_prop_name G)) (NVar (book_second_prop_name G)))
      (book_imp (NVar (book_second_prop_name G)) (NVar (book_prop_name G)))) Prop"
  by (rule book_and_language[OF rich
    book_imp_language[OF book_boolean_variables_language(1)[OF rich] book_boolean_variables_language(2)[OF rich]]
    book_imp_language[OF book_boolean_variables_language(2)[OF rich] book_boolean_variables_language(1)[OF rich]]])

lemma book_iff_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_iff_const G) (Arr Prop (Arr Prop Prop))"
  unfolding book_iff_const_def by (rule book_boolean_abstraction_language[OF rich book_iff_body_language[OF rich]])

lemma book_iff_language:
  assumes rich: "sg_rich G" and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_iff G A B) Prop"
  unfolding book_iff_def by (rule book_language_App[OF book_language_App[OF book_iff_const_language[OF rich] A] B])

lemma book_top_language:
  "sg_rich G \<Longrightarrow> book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_top G) Prop"
  unfolding book_top_def by (rule book_not_language, assumption, rule book_bottom_language, assumption)

lemma book_or_const_closed: "named_fv (book_or_const G) = {}"
  by (auto simp: book_or_const_def book_imp_fv book_not_fv)
lemma book_or_fv: "named_fv (book_or G A B) = named_fv A \<union> named_fv B"
  by (simp add: book_or_def book_or_const_closed)
lemma book_and_const_closed: "named_fv (book_and_const G) = {}"
  by (auto simp: book_and_const_def book_not_fv book_imp_fv)
lemma book_and_fv: "named_fv (book_and G A B) = named_fv A \<union> named_fv B"
  by (simp add: book_and_def book_and_const_closed)
lemma book_iff_const_closed: "named_fv (book_iff_const G) = {}"
  by (auto simp: book_iff_const_def book_and_fv book_imp_fv)
lemma book_iff_fv: "named_fv (book_iff G A B) = named_fv A \<union> named_fv B"
  by (simp add: book_iff_def book_iff_const_closed)
lemma book_top_closed: "named_fv (book_top G) = {}"
  by (simp add: book_top_def book_not_fv book_bottom_closed)

end
