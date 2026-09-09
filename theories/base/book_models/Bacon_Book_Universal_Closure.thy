theory Bacon_Book_Universal_Closure
  imports Bacon_Book_Theory_Variable_Substitution
begin

section \<open>Removing a universal binder with its own variable\<close>

text \<open>
  S ⊢ ∀n.A implies S ⊢ A. The literal quantifier formula is
  ∀G(n)(λn.A). UI at the term n gives (λn.A)n, and the printed
  β axiom gives A because A[n/n]=A. This substitution is always
  free for n, even when A contains further binders.
  Source: Bacon, Definition 5.1, pp.97–98.

  Representation: book_all is not a primitive binder constructor.
  Status: this elimination uses only UI, β and MP, with language guards;
  no richness, model, or H premise is needed for this direction.
\<close>

theorem book_theory_all_elim_variable:
  assumes quantified: "book_theory_derivable \<Sigma> G S (book_all G n A)"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S A"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) (G n)"
    by (rule book_language_Var)
  have predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam n A) (Arr (G n) Prop)"
    by (rule book_language_Lam[OF al])
  have redex_language: "book_theory_formula \<Sigma> G (NApp (NLam n A) (NVar n))"
    by (rule book_language_App[OF predicate variable])
  have ui: "book_theory_derivable \<Sigma> G S
    (book_imp (book_all G n A) (NApp (NLam n A) (NVar n)))"
    by (simp only: book_all_def; rule book_theory_derivable.UI[OF predicate variable])
  have redex: "book_theory_derivable \<Sigma> G S (NApp (NLam n A) (NVar n))"
    by (rule book_theory_derivable.MP[OF quantified ui redex_language])
  have raw: "named_beta_contract (NApp (NLam n A) (NVar n)) (named_subst n (NVar n) A)"
    by (rule named_beta_contract.beta, rule named_free_for_same_variable)
  have contraction: "named_beta_contract (NApp (NLam n A) (NVar n)) A"
    using raw by (simp only: named_subst_same_variable)
  have implication: "book_theory_derivable \<Sigma> G S
    (book_imp (NApp (NLam n A) (NVar n)) A)"
    by (rule book_theory_derivable.Beta[OF redex_language al], rule disjI1,
      rule named_compatible_step.root, rule contraction)
  show ?thesis by (rule book_theory_derivable.MP[OF redex implication al])
qed

section \<open>Finite iteration of literal universal quantification\<close>

text \<open>
  ∀[n₁,…,nₖ].A means ∀n₁.…∀nₖ.A, with the first list entry
  outermost. Repeated names are permitted. Its free variables are
  FV(A)∖{n₁,…,nₖ}. Under a rich stock, S ⊢ A iff S ⊢ ∀[n₁,…,nₖ].A.
  The forward direction uses the already derived theory generalization
  rule. There is no restriction on the free variables of S or A:
  these are theory-level, universally asserted assumptions, not
  fixed-assignment local premises.
\<close>

fun book_all_list :: "sgcontext \<Rightarrow> nat list \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_all_list G [] A = A"
| "book_all_list G (n # ns) A = book_all G n (book_all_list G ns A)"

lemma book_all_list_language:
  assumes al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_formula \<Sigma> G (book_all_list G ns A)"
proof (induction ns)
  case Nil
  show ?case using al by simp
next
  case (Cons n ns)
  show ?case by (simp only: book_all_list.simps; rule book_all_language[OF Cons.IH])
qed

lemma book_all_list_fv:
  "named_fv (book_all_list G ns A) = named_fv A - set ns"
  by (induction ns) (auto simp: book_all_fv)

lemma book_theory_all_list_intro:
  assumes rich: "sg_rich G"
    and derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
proof (induction ns)
  case Nil
  show ?case using derivation by simp
next
  case (Cons n ns)
  show ?case by (simp only: book_all_list.simps; rule book_theory_generalize[OF rich Cons.IH])
qed

lemma book_theory_all_list_elim:
  assumes al: "book_theory_formula \<Sigma> G A"
    and derivation: "book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
  shows "book_theory_derivable \<Sigma> G S A"
  using derivation
proof (induction ns)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons n ns)
  have inner_language: "book_theory_formula \<Sigma> G (book_all_list G ns A)"
    by (rule book_all_list_language[OF al])
  have outer: "book_theory_derivable \<Sigma> G S (book_all G n (book_all_list G ns A))"
    using Cons.prems by (simp only: book_all_list.simps)
  have inner: "book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
    by (rule book_theory_all_elim_variable[OF outer inner_language])
  show ?case by (rule Cons.IH[OF inner])
qed

theorem book_theory_all_list_iff:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
proof
  assume derivation: "book_theory_derivable \<Sigma> G S A"
  show "book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
    by (rule book_theory_all_list_intro[OF rich derivation])
next
  assume derivation: "book_theory_derivable \<Sigma> G S (book_all_list G ns A)"
  show "book_theory_derivable \<Sigma> G S A"
    by (rule book_theory_all_list_elim[OF al derivation])
qed

section \<open>A deterministic universal closure\<close>

text \<open>
  The universal closure of A binds exactly its finitely many free variable
  names, in increasing numerical order. It is a closed formula of the
  same language and has the same theory derivability as A under each S.
  This syntactic bridge does not discharge assumptions or introduce an
  additional proof rule. In particular, it makes no model-existence claim.
\<close>

definition book_universal_closure :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_universal_closure G A = book_all_list G (sorted_list_of_set (named_fv A)) A"

lemma book_universal_closure_language:
  assumes al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_formula \<Sigma> G (book_universal_closure G A)"
  unfolding book_universal_closure_def by (rule book_all_list_language[OF al])

lemma book_universal_closure_closed:
  "named_fv (book_universal_closure G A) = {}"
  by (simp add: book_universal_closure_def book_all_list_fv named_fv_finite)

lemma book_universal_closure_of_closed:
  assumes closed: "named_fv A = {}"
  shows "book_universal_closure G A = A"
  by (simp add: book_universal_closure_def closed)

theorem book_theory_universal_closure_iff:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable \<Sigma> G S (book_universal_closure G A)"
  unfolding book_universal_closure_def by (rule book_theory_all_list_iff[OF rich al])

end
