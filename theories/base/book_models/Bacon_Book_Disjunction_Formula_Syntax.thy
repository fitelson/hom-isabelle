theory Bacon_Book_Disjunction_Formula_Syntax
  imports Bacon_Book_Primitive_Disjunction_Syntax
begin

section \<open>Inherited formula operations in the primitive-disjunction language\<close>

text \<open>
  Keep →, ∀ and primitive ∧ while adding primitive ∨. The inherited
  logical symbols are nested under BDConjunction; implication and
  universal quantification additionally use BCMinimal. The definitions
  of ⊥ and ¬ retain EXACTLY the previous book_prop_name(G) binder.
  Source: Bacon, Table 4.1, p.93, and §5.2, p.104.

  book_disj_conj is the application of the inherited primitive ∧,
  not a λ-definition. The new primitive ∨ is separately book_disj_apply
  from the vocabulary leaf. This file supplies language and free-variable
  facts only: no axiom, proof judgment, encoding equation, or model is
  assumed. Arbitrary nonlogical signatures and the fixed stock G remain
  explicit. Richness is needed only for typing the chosen ⊥/¬ binders.
\<close>

definition book_disj_imp :: "'c book_disj_term \<Rightarrow> 'c book_disj_term \<Rightarrow> 'c book_disj_term" where
  "book_disj_imp A B = NApp (NApp (NLogical (BDConjunction (BCMinimal SImp))) A) B"

definition book_disj_all :: "sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_disj_term \<Rightarrow> 'c book_disj_term" where
  "book_disj_all G n A = NApp (NLogical (BDConjunction (BCMinimal (SBAll (G n))))) (NLam n A)"

definition book_disj_bottom :: "sgcontext \<Rightarrow> 'c book_disj_term" where
  "book_disj_bottom G = NApp (NLogical (BDConjunction (BCMinimal (SBAll Prop))))
    (NLam (book_prop_name G) (NVar (book_prop_name G)))"

definition book_disj_not_const :: "sgcontext \<Rightarrow> 'c book_disj_term" where
  "book_disj_not_const G = NLam (book_prop_name G)
    (book_disj_imp (NVar (book_prop_name G)) (book_disj_bottom G))"

definition book_disj_not :: "sgcontext \<Rightarrow> 'c book_disj_term \<Rightarrow> 'c book_disj_term" where
  "book_disj_not G A = NApp (book_disj_not_const G) A"

definition book_disj_conj :: "'c book_disj_term \<Rightarrow> 'c book_disj_term \<Rightarrow> 'c book_disj_term" where
  "book_disj_conj A B = NApp (NApp (NLogical (BDConjunction BCAnd)) A) B"

lemma book_disj_imp_operator_language:
  "book_in_language book_disj_logical_type UNIV \<Sigma> G
    (NLogical (BDConjunction (BCMinimal SImp))) (Arr Prop (Arr Prop Prop))"
  by (simp add: book_language_logical_iff)

lemma book_disj_all_operator_language:
  "book_in_language book_disj_logical_type UNIV \<Sigma> G
    (NLogical (BDConjunction (BCMinimal (SBAll \<sigma>)))) (Arr (Arr \<sigma> Prop) Prop)"
  by (simp add: book_language_logical_iff)

lemma book_disj_conj_operator_language:
  "book_in_language book_disj_logical_type UNIV \<Sigma> G
    (NLogical (BDConjunction BCAnd)) (Arr Prop (Arr Prop Prop))"
  by (simp add: book_language_logical_iff)

lemma book_disj_imp_language:
  assumes first: "book_disj_formula \<Sigma> G A" and second: "book_disj_formula \<Sigma> G B"
  shows "book_disj_formula \<Sigma> G (book_disj_imp A B)"
  unfolding book_disj_imp_def
  by (rule book_language_App[OF book_language_App[OF book_disj_imp_operator_language first] second])

lemma book_disj_all_language:
  assumes body: "book_disj_formula \<Sigma> G A"
  shows "book_disj_formula \<Sigma> G (book_disj_all G n A)"
  unfolding book_disj_all_def
  by (rule book_language_App[OF book_disj_all_operator_language book_language_Lam[OF body]])

lemma book_disj_bottom_as_all:
  assumes rich: "sg_rich G"
  shows "book_disj_bottom G = book_disj_all G (book_prop_name G) (NVar (book_prop_name G))"
  by (simp only: book_disj_bottom_def book_disj_all_def book_prop_name_type[OF rich])

lemma book_disj_bottom_language:
  assumes rich: "sg_rich G"
  shows "book_disj_formula \<Sigma> G (book_disj_bottom G)"
proof -
  have variable: "book_disj_formula \<Sigma> G (NVar (book_prop_name G))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  show ?thesis by (simp only: book_disj_bottom_as_all[OF rich]; rule book_disj_all_language[OF variable])
qed

lemma book_disj_not_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_disj_logical_type UNIV \<Sigma> G (book_disj_not_const G) (Arr Prop Prop)"
proof -
  have variable: "book_disj_formula \<Sigma> G (NVar (book_prop_name G))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have body: "book_disj_formula \<Sigma> G (book_disj_imp (NVar (book_prop_name G)) (book_disj_bottom G))"
    by (rule book_disj_imp_language[OF variable book_disj_bottom_language[OF rich]])
  have abstraction: "book_in_language book_disj_logical_type UNIV \<Sigma> G
    (NLam (book_prop_name G) (book_disj_imp (NVar (book_prop_name G)) (book_disj_bottom G)))
    (Arr (G (book_prop_name G)) Prop)"
    by (rule book_language_Lam[OF body])
  show ?thesis using abstraction by (simp only: book_disj_not_const_def book_prop_name_type[OF rich])
qed

lemma book_disj_not_language:
  assumes rich: "sg_rich G" and body: "book_disj_formula \<Sigma> G A"
  shows "book_disj_formula \<Sigma> G (book_disj_not G A)"
  unfolding book_disj_not_def
  by (rule book_language_App[OF book_disj_not_const_language[OF rich] body])

lemma book_disj_conj_language:
  assumes first: "book_disj_formula \<Sigma> G A" and second: "book_disj_formula \<Sigma> G B"
  shows "book_disj_formula \<Sigma> G (book_disj_conj A B)"
  unfolding book_disj_conj_def
  by (rule book_language_App[OF book_language_App[OF book_disj_conj_operator_language first] second])

lemma book_disj_conj_type:
  assumes first: "has_ntype book_disj_logical_type G A Prop"
    and second: "has_ntype book_disj_logical_type G B Prop"
  shows "has_ntype book_disj_logical_type G (book_disj_conj A B) Prop"
proof -
  have operator: "has_ntype book_disj_logical_type G
    (NLogical (BDConjunction BCAnd)) (Arr Prop (Arr Prop Prop))"
    by (simp add: named_logical_type_iff)
  show ?thesis unfolding book_disj_conj_def
    by (rule has_ntype.App[OF has_ntype.App[OF operator first] second])
qed

lemma book_disj_imp_fv: "named_fv (book_disj_imp A B) = named_fv A \<union> named_fv B"
  by (simp add: book_disj_imp_def)
lemma book_disj_all_fv: "named_fv (book_disj_all G n A) = named_fv A - {n}"
  by (simp add: book_disj_all_def)
lemma book_disj_bottom_closed: "named_fv (book_disj_bottom G) = {}"
  by (simp add: book_disj_bottom_def)
lemma book_disj_not_const_closed: "named_fv (book_disj_not_const G) = {}"
  by (simp add: book_disj_not_const_def book_disj_imp_fv book_disj_bottom_closed)
lemma book_disj_not_fv: "named_fv (book_disj_not G A) = named_fv A"
  by (simp add: book_disj_not_def book_disj_not_const_closed)
lemma book_disj_conj_fv: "named_fv (book_disj_conj A B) = named_fv A \<union> named_fv B"
  by (simp add: book_disj_conj_def)

end
