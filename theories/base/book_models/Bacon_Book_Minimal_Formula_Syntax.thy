theory Bacon_Book_Minimal_Formula_Syntax
  imports Bacon_Book_Language Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Charts
begin

section \<open>Literal formulas in the book's minimal logical basis\<close>

text \<open>
  A→B applies the primitive →; ∀n.A applies ∀G(n) to λn.A.
  Table 4.1, p.93, defines ⊥ as ∀t(λp.p) and ¬ as λp.(p→⊥).
  The same definitions are used in Chapter 5, pp.97–98.

  Representation. book_not G A is an application of the closed λ-defined
  negation operator, not the raw term A→⊥. Its chosen propositional name
  may also occur in A, which is outside that binder's scope. There is no
  β reduction or capture claim in these definitions. Types use full F;
  UNIV selects all symbols of the minimal SImp/SBAll datatype only.
\<close>

type_synonym 'c book_named_term = "('c, book_minimal_logical) named_term"

definition book_imp :: "'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_imp A B = NApp (NApp (NLogical SImp) A) B"
definition book_all :: "sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_all G n A = NApp (NLogical (SBAll (G n))) (NLam n A)"
definition book_prop_name :: "sgcontext \<Rightarrow> nat" where
  "book_prop_name G = named_chart_fresh G [] Prop"
definition book_bottom :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_bottom G = NApp (NLogical (SBAll Prop)) (NLam (book_prop_name G) (NVar (book_prop_name G)))"
definition book_not_const :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_not_const G = NLam (book_prop_name G) (book_imp (NVar (book_prop_name G)) (book_bottom G))"
definition book_not :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_not G A = NApp (book_not_const G) A"

lemma book_prop_name_type:
  "sg_rich G \<Longrightarrow> G (book_prop_name G) = Prop"
  unfolding book_prop_name_def by (rule named_chart_fresh_type; assumption)

lemma book_imp_operator_language:
  "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLogical SImp) (Arr Prop (Arr Prop Prop))"
  by (simp add: book_language_logical_iff)
lemma book_all_operator_language:
  "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLogical (SBAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
  by (simp add: book_language_logical_iff)

lemma book_imp_language:
  assumes A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_imp A B) Prop"
  unfolding book_imp_def by (rule book_language_App[OF book_language_App[OF book_imp_operator_language A] B])

lemma book_all_language:
  assumes A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_all G n A) Prop"
  unfolding book_all_def by (rule book_language_App[OF book_all_operator_language book_language_Lam[OF A]])

lemma book_bottom_as_all:
  assumes rich: "sg_rich G"
  shows "book_bottom G = book_all G (book_prop_name G) (NVar (book_prop_name G))"
  by (simp only: book_bottom_def book_all_def book_prop_name_type[OF rich])

lemma book_bottom_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_bottom G) Prop"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_prop_name G)) Prop"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  show ?thesis by (simp only: book_bottom_as_all[OF rich]; rule book_all_language[OF variable])
qed

lemma book_not_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_not_const G) (Arr Prop Prop)"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_prop_name G)) Prop"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have body: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (book_imp (NVar (book_prop_name G)) (book_bottom G)) Prop"
    by (rule book_imp_language[OF variable book_bottom_language[OF rich]])
  show ?thesis using book_language_Lam[where n="book_prop_name G", OF body]
    by (simp only: book_not_const_def book_prop_name_type[OF rich])
qed

lemma book_not_language:
  assumes rich: "sg_rich G" and A: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_not G A) Prop"
  unfolding book_not_def by (rule book_language_App[OF book_not_const_language[OF rich] A])

lemma book_imp_fv: "named_fv (book_imp A B) = named_fv A \<union> named_fv B"
  by (simp add: book_imp_def)
lemma book_all_fv: "named_fv (book_all G n A) = named_fv A - {n}"
  by (simp add: book_all_def)
lemma book_bottom_closed: "named_fv (book_bottom G) = {}"
  by (simp add: book_bottom_def)
lemma book_not_const_closed: "named_fv (book_not_const G) = {}"
  by (simp add: book_not_const_def book_imp_fv book_bottom_closed)
lemma book_not_fv: "named_fv (book_not G A) = named_fv A"
  by (simp add: book_not_def book_not_const_closed)

lemma book_bottom_type:
  assumes rich: "sg_rich G"
  shows "has_ntype book_minimal_logical_type G (book_bottom G) Prop"
  by (rule book_language_type[OF book_bottom_language[where \<Sigma>="\<lambda>_. {}", OF rich]])
lemma book_not_const_type:
  assumes rich: "sg_rich G"
  shows "has_ntype book_minimal_logical_type G (book_not_const G) (Arr Prop Prop)"
  by (rule book_language_type[OF book_not_const_language[where \<Sigma>="\<lambda>_. {}", OF rich]])

end
