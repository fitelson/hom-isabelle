theory Bacon_Book_Lambda_I_Universal_Closure
  imports Bacon_Book_Lambda_I_Theory_Variable_Substitution
begin

section \<open>Removing a universal binder with its own variable\<close>

text \<open>
  S ⊢ ∀n.A implies S ⊢ A. The literal quantifier formula is
  ∀G(n)(λn.A). UI at the term n gives (λn.A)n, and the exact-capture
  β axiom gives A because A[n/n]=A. This self-substitution is always
  exact-free-for n, even when A contains further binders (the separately
  transcribed printed test is not used here).
  Source: Bacon, Definition 5.1, pp.97–98. The λI rules used here are
  those of Definition 9.8, p.197, restricted to λI formulas, i.e. the
  same schemas as Definition 5.1 (see Bacon_Book_Lambda_I_Calculus).

  Representation: book_all is not a primitive binder constructor.
  Status: this elimination uses only UI, β and MP, with language guards;
  no richness, model, or H premise is needed for this direction.
\<close>

text \<open>
  λI variant. Literal quantification ∀n.A is a λI formula only when n
  occurs free in A, so every binder list below is required to be
  distinct and to consist of free variable names of A. The deterministic
  universal closure binds exactly the free variable names, so it meets
  this requirement automatically.
\<close>

theorem book_lambda_I_all_elim_variable:
  assumes quantified: "book_lambda_I_derivable \<Sigma> G S (book_all G n A)"
    and al: "book_lambda_I_formula \<Sigma> G A" and occurs: "n \<in> named_fv A"
  shows "book_lambda_I_derivable \<Sigma> G S A"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) (G n)"
    by (rule book_language_Var)
  have predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam n A) (Arr (G n) Prop)"
    by (rule book_language_Lam[OF conjunct1[OF al]])
  have predicate_lambda_I: "NLam n A \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (Arr (G n) Prop)"
    by (rule book_lambda_I_termsI[OF predicate]; simp add: conjunct2[OF al] occurs)
  have variable_lambda_I: "NVar n \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (G n)"
    by (rule book_lambda_I_termsI[OF variable]; simp)
  have redex_language: "book_lambda_I_formula \<Sigma> G (NApp (NLam n A) (NVar n))"
    by (rule conjI[OF book_language_App[OF predicate variable]]; simp add: conjunct2[OF al] occurs)
  have ui: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_all G n A) (NApp (NLam n A) (NVar n)))"
    by (simp only: book_all_def; rule book_lambda_I_derivable.UI[OF predicate_lambda_I variable_lambda_I])
  have redex: "book_lambda_I_derivable \<Sigma> G S (NApp (NLam n A) (NVar n))"
    by (rule book_lambda_I_derivable.MP[OF quantified ui redex_language])
  have raw: "named_beta_contract (NApp (NLam n A) (NVar n)) (named_subst n (NVar n) A)"
    by (rule named_beta_contract.beta, rule named_free_for_same_variable)
  have contraction: "named_beta_contract (NApp (NLam n A) (NVar n)) A"
    using raw by (simp only: named_subst_same_variable)
  have implication: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (NApp (NLam n A) (NVar n)) A)"
    by (rule book_lambda_I_derivable.Beta[OF redex_language al], rule disjI1,
      rule named_compatible_step.root, rule contraction)
  show ?thesis by (rule book_lambda_I_derivable.MP[OF redex implication al])
qed

section \<open>Finite iteration of literal universal quantification\<close>

text \<open>
  ∀[n₁,…,nₖ].A means ∀n₁.…∀nₖ.A, with the first list entry
  outermost. The raw recursive function permits repeated names, but the
  λI language and derivability claims below require the list to be
  distinct and drawn from FV(A). Its free variables are FV(A)∖{n₁,…,nₖ}.
  Under a rich stock and that guard, S ⊢ A iff S ⊢ ∀[n₁,…,nₖ].A; the
  forward direction uses the derived nonvacuous generalization rule.
  There is no restriction on the free variables of the premises S: these
  are theory-level, universally asserted assumptions, not
  fixed-assignment local premises.
\<close>

fun book_all_list :: "sgcontext \<Rightarrow> nat list \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_all_list G [] A = A"
| "book_all_list G (n # ns) A = book_all G n (book_all_list G ns A)"

lemma book_lambda_I_all_list_fv:
  "named_fv (book_all_list G ns A) = named_fv A - set ns"
  by (induction ns) (auto simp: book_all_fv)

lemma book_lambda_I_all_list_language:
  assumes al: "book_lambda_I_formula \<Sigma> G A"
    and distinct: "distinct ns" and subset: "set ns \<subseteq> named_fv A"
  shows "book_lambda_I_formula \<Sigma> G (book_all_list G ns A)"
  using distinct subset
proof (induction ns)
  case Nil
  show ?case using al by simp
next
  case (Cons n ns)
  have tail_distinct: "distinct ns" and tail_subset: "set ns \<subseteq> named_fv A"
    and head_free: "n \<in> named_fv A" and head_outside: "n \<notin> set ns"
    using Cons.prems by auto
  have inner: "book_lambda_I_formula \<Sigma> G (book_all_list G ns A)"
    by (rule Cons.IH[OF tail_distinct tail_subset])
  have occurs: "n \<in> named_fv (book_all_list G ns A)"
    using head_free head_outside by (simp add: book_lambda_I_all_list_fv)
  show ?case by (simp only: book_all_list.simps; rule book_lambda_I_all_language[OF inner occurs])
qed

lemma book_lambda_I_all_list_intro:
  assumes rich: "sg_rich G"
    and derivation: "book_lambda_I_derivable \<Sigma> G S A"
    and distinct: "distinct ns" and subset: "set ns \<subseteq> named_fv A"
  shows "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
  using distinct subset
proof (induction ns)
  case Nil
  show ?case using derivation by simp
next
  case (Cons n ns)
  have tail_distinct: "distinct ns" and tail_subset: "set ns \<subseteq> named_fv A"
    and head_free: "n \<in> named_fv A" and head_outside: "n \<notin> set ns"
    using Cons.prems by auto
  have inner: "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
    by (rule Cons.IH[OF tail_distinct tail_subset])
  have occurs: "n \<in> named_fv (book_all_list G ns A)"
    using head_free head_outside by (simp add: book_lambda_I_all_list_fv)
  show ?case by (simp only: book_all_list.simps; rule book_lambda_I_generalize[OF rich inner occurs])
qed

lemma book_lambda_I_all_list_elim:
  assumes al: "book_lambda_I_formula \<Sigma> G A"
    and derivation: "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
    and distinct: "distinct ns" and subset: "set ns \<subseteq> named_fv A"
  shows "book_lambda_I_derivable \<Sigma> G S A"
  using derivation distinct subset
proof (induction ns)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons n ns)
  have tail_distinct: "distinct ns" and tail_subset: "set ns \<subseteq> named_fv A"
    and head_free: "n \<in> named_fv A" and head_outside: "n \<notin> set ns"
    using Cons.prems by auto
  have inner_language: "book_lambda_I_formula \<Sigma> G (book_all_list G ns A)"
    by (rule book_lambda_I_all_list_language[OF al tail_distinct tail_subset])
  have occurs: "n \<in> named_fv (book_all_list G ns A)"
    using head_free head_outside by (simp add: book_lambda_I_all_list_fv)
  have outer: "book_lambda_I_derivable \<Sigma> G S (book_all G n (book_all_list G ns A))"
    using Cons.prems by (simp only: book_all_list.simps)
  have inner: "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
    by (rule book_lambda_I_all_elim_variable[OF outer inner_language occurs])
  show ?case by (rule Cons.IH[OF inner tail_distinct tail_subset])
qed

theorem book_lambda_I_all_list_iff:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and distinct: "distinct ns" and subset: "set ns \<subseteq> named_fv A"
  shows "book_lambda_I_derivable \<Sigma> G S A \<longleftrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
proof
  assume derivation: "book_lambda_I_derivable \<Sigma> G S A"
  show "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
    by (rule book_lambda_I_all_list_intro[OF rich derivation distinct subset])
next
  assume derivation: "book_lambda_I_derivable \<Sigma> G S (book_all_list G ns A)"
  show "book_lambda_I_derivable \<Sigma> G S A"
    by (rule book_lambda_I_all_list_elim[OF al derivation distinct subset])
qed

lemma book_lambda_I_closure_list_distinct:
  "distinct (sorted_list_of_set (named_fv A))"
  by (rule distinct_sorted_list_of_set)

lemma book_lambda_I_closure_list_subset:
  "set (sorted_list_of_set (named_fv A)) \<subseteq> named_fv A"
  by (simp add: named_fv_finite)

section \<open>A deterministic universal closure\<close>

text \<open>
  The universal closure of A binds exactly its finitely many free variable
  names, in increasing numerical order. It is a closed formula of the
  same language and has the same theory derivability as A under each S.
  This syntactic bridge does not discharge assumptions or introduce an
  additional proof rule. In particular, it makes no model-existence claim.
\<close>

definition book_lambda_I_universal_closure :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_lambda_I_universal_closure G A = book_all_list G (sorted_list_of_set (named_fv A)) A"

lemma book_lambda_I_universal_closure_language:
  assumes al: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_formula \<Sigma> G (book_lambda_I_universal_closure G A)"
  unfolding book_lambda_I_universal_closure_def
  by (rule book_lambda_I_all_list_language[OF al book_lambda_I_closure_list_distinct book_lambda_I_closure_list_subset])

lemma book_lambda_I_universal_closure_closed:
  "named_fv (book_lambda_I_universal_closure G A) = {}"
  by (simp add: book_lambda_I_universal_closure_def book_lambda_I_all_list_fv named_fv_finite)

lemma book_lambda_I_universal_closure_of_closed:
  assumes closed: "named_fv A = {}"
  shows "book_lambda_I_universal_closure G A = A"
  by (simp add: book_lambda_I_universal_closure_def closed)

theorem book_lambda_I_universal_closure_iff:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G S A \<longleftrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_lambda_I_universal_closure G A)"
  unfolding book_lambda_I_universal_closure_def
  by (rule book_lambda_I_all_list_iff[OF rich al book_lambda_I_closure_list_distinct book_lambda_I_closure_list_subset])

end
