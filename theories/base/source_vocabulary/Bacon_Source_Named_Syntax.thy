theory Bacon_Source_Named_Syntax
  imports Bacon_Source_Global_Typing
begin

section \<open>Raw named terms with fixed variable types\<close>

text \<open>
  Each variable has a fixed type.  If x has type σ and A has type τ,
  λx.A has type σ → τ; application has the corresponding arrow rule.
  Source: Bacon–Dorr §1.1, p.5, including its explicit distinction between
  the relational grammar R and full simple types F.

  Isabelle representation.  NVar n denotes the variable named n, not a
  de Bruijn slot.  The stock G:nat → otype fixes its type everywhere.
  NLam n binds that same name in its body; a nested binder with the same
  name shadows the outer binder and keeps the same G n type.  The raw
  datatype retains binder names and has no α quotient.  Logical constants
  remain first-class; paper_named_term selects exactly paper_logical.
  The logical carrier parameter is structural sharing, not a merger of
  the paper and book primitive bases.

  Scope.  This is a raw AST representation of named typed expressions,
  with natural-number identifiers and the represented full F type grammar.
  No parser/printed-string correspondence, named substitution, α relation,
  proof system, or semantic interpretation is asserted here.  Source use
  can separately require sg_rich G; typing and finite-support results do
  not need that hypothesis.
\<close>

datatype ('c, 'l) named_term =
    NVar nat
  | NConst 'c otype
  | NLogical 'l
  | NApp "('c, 'l) named_term" "('c, 'l) named_term"
  | NLam nat "('c, 'l) named_term"

type_synonym 'c paper_named_term = "('c, paper_logical) named_term"

inductive has_ntype ::
  "('l \<Rightarrow> otype) \<Rightarrow> sgcontext \<Rightarrow> ('c, 'l) named_term \<Rightarrow> otype \<Rightarrow> bool"
  for L :: "'l \<Rightarrow> otype" and G :: sgcontext where
  Var: "has_ntype L G (NVar n) (G n)"
| Const: "has_ntype L G (NConst c \<sigma>) \<sigma>"
| Logical: "has_ntype L G (NLogical l) (L l)"
| App: "has_ntype L G F (Arr \<sigma> \<tau>) \<Longrightarrow> has_ntype L G A \<sigma> \<Longrightarrow>
    has_ntype L G (NApp F A) \<tau>"
| Lam: "has_ntype L G A \<tau> \<Longrightarrow> has_ntype L G (NLam n A) (Arr (G n) \<tau>)"

fun named_in_signature :: "'c ssignature \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool" where
  "named_in_signature \<Sigma> (NVar n) = True"
| "named_in_signature \<Sigma> (NConst c \<sigma>) = (c \<in> \<Sigma> \<sigma>)"
| "named_in_signature \<Sigma> (NLogical l) = True"
| "named_in_signature \<Sigma> (NApp F A) = (named_in_signature \<Sigma> F \<and> named_in_signature \<Sigma> A)"
| "named_in_signature \<Sigma> (NLam n A) = named_in_signature \<Sigma> A"

definition named_in_language ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    ('c, 'l) named_term \<Rightarrow> otype \<Rightarrow> bool" where
  "named_in_language L \<Sigma> G A \<tau> \<longleftrightarrow> has_ntype L G A \<tau> \<and> named_in_signature \<Sigma> A"

fun named_fv :: "('c, 'l) named_term \<Rightarrow> nat set" where
  "named_fv (NVar n) = {n}"
| "named_fv (NConst c \<sigma>) = {}"
| "named_fv (NLogical l) = {}"
| "named_fv (NApp F A) = named_fv F \<union> named_fv A"
| "named_fv (NLam n A) = named_fv A - {n}"

fun named_vars :: "('c, 'l) named_term \<Rightarrow> nat set" where
  "named_vars (NVar n) = {n}"
| "named_vars (NConst c \<sigma>) = {}"
| "named_vars (NLogical l) = {}"
| "named_vars (NApp F A) = named_vars F \<union> named_vars A"
| "named_vars (NLam n A) = insert n (named_vars A)"

lemma named_fv_finite: "finite (named_fv A)"
  by (induction A) simp_all

lemma named_vars_finite: "finite (named_vars A)"
  by (induction A) simp_all

lemma named_fv_subset_vars: "named_fv A \<subseteq> named_vars A"
  by (induction A) auto

subsection \<open>Typing inversion and uniqueness\<close>

lemma named_var_type_iff:
  "has_ntype L G (NVar n) \<tau> \<longleftrightarrow> \<tau> = G n"
  by (auto elim: has_ntype.cases intro: has_ntype.Var)

lemma named_const_type_iff:
  "has_ntype L G (NConst c \<sigma>) \<tau> \<longleftrightarrow> \<tau> = \<sigma>"
  by (auto elim: has_ntype.cases intro: has_ntype.Const)

lemma named_logical_type_iff:
  "has_ntype L G (NLogical l) \<tau> \<longleftrightarrow> \<tau> = L l"
  by (auto elim: has_ntype.cases intro: has_ntype.Logical)

lemma named_app_type_obtain:
  assumes typed: "has_ntype L G (NApp F A) \<tau>"
  obtains \<sigma> where "has_ntype L G F (Arr \<sigma> \<tau>)" and "has_ntype L G A \<sigma>"
  using typed by (cases rule: has_ntype.cases) auto

lemma named_lam_type_obtain:
  assumes typed: "has_ntype L G (NLam n A) \<tau>"
  obtains \<rho> where "\<tau> = Arr (G n) \<rho>" and "has_ntype L G A \<rho>"
  using typed by (cases rule: has_ntype.cases) auto

theorem named_type_unique:
  assumes first: "has_ntype L G A \<tau>" and second: "has_ntype L G A \<rho>"
  shows "\<tau> = \<rho>"
  using first second
proof (induction A arbitrary: \<tau> \<rho>)
  case (NVar n)
  show ?case using NVar.prems by (auto simp only: named_var_type_iff)
next
  case (NConst c \<sigma>)
  show ?case using NConst.prems by (auto simp only: named_const_type_iff)
next
  case (NLogical l)
  show ?case using NLogical.prems by (auto simp only: named_logical_type_iff)
next
  case (NApp F A)
  obtain \<sigma> where ft: "has_ntype L G F (Arr \<sigma> \<tau>)" and at: "has_ntype L G A \<sigma>"
    by (rule named_app_type_obtain[OF NApp.prems(1)]; rule that; assumption)
  obtain \<upsilon> where fr: "has_ntype L G F (Arr \<upsilon> \<rho>)" and ar: "has_ntype L G A \<upsilon>"
    by (rule named_app_type_obtain[OF NApp.prems(2)]; rule that; assumption)
  have arrows: "Arr \<sigma> \<tau> = Arr \<upsilon> \<rho>" by (rule NApp.IH(1)[OF ft fr])
  show ?case using arrows by simp
next
  case (NLam n A)
  obtain \<sigma> where t: "\<tau> = Arr (G n) \<sigma>" and at: "has_ntype L G A \<sigma>"
    by (rule named_lam_type_obtain[OF NLam.prems(1)]; rule that; assumption)
  obtain \<upsilon> where r: "\<rho> = Arr (G n) \<upsilon>" and ar: "has_ntype L G A \<upsilon>"
    by (rule named_lam_type_obtain[OF NLam.prems(2)]; rule that; assumption)
  have body: "\<sigma> = \<upsilon>" by (rule NLam.IH[OF at ar])
  show ?case by (simp only: t r body)
qed

end
