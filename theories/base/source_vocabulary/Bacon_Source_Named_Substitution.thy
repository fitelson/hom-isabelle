theory Bacon_Source_Named_Substitution
  imports Bacon_Source_Named_Syntax
begin

section \<open>Literal replacement and the source free-for condition\<close>

text \<open>
  A[B/x] replaces free occurrences of x by B, provided no free variable
  of B becomes bound (Bacon–Dorr Figure 2, p.8). We keep that proviso
  explicit rather than silently changing binder names.

  Isabelle representation: named_subst stops beneath NLam x. Beneath a
  different binder y it recursively replaces x without any α-renaming.
  named_free_for records exactly the capture restriction. If x is absent
  from that binder body, the binder cannot capture an inserted occurrence
  of B because none is inserted there.

  Status: raw named syntax only. The total replacement function may capture
  variables when named_free_for is false; it is not an automatically
  capture-avoiding substitution algorithm. No encoding, model, α relation,
  or generalized β rule is assumed.
\<close>

fun named_subst ::
  "nat \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term"
  where
  "named_subst x B (NVar y) = (if y = x then B else NVar y)"
| "named_subst x B (NConst c \<sigma>) = NConst c \<sigma>"
| "named_subst x B (NLogical l) = NLogical l"
| "named_subst x B (NApp F A) = NApp (named_subst x B F) (named_subst x B A)"
| "named_subst x B (NLam y A) =
    (if y = x then NLam y A else NLam y (named_subst x B A))"

fun named_free_for ::
  "('c, 'l) named_term \<Rightarrow> nat \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool" where
  "named_free_for B x (NVar y) = True"
| "named_free_for B x (NConst c \<sigma>) = True"
| "named_free_for B x (NLogical l) = True"
| "named_free_for B x (NApp F A) = (named_free_for B x F \<and> named_free_for B x A)"
| "named_free_for B x (NLam y A) =
    (y = x \<or> (named_free_for B x A \<and> (y \<notin> named_fv B \<or> x \<notin> named_fv A)))"

lemma named_subst_fresh:
  assumes fresh: "x \<notin> named_fv A"
  shows "named_subst x B A = A"
  using fresh by (induction A) (auto split: if_splits)

lemma named_free_for_fresh:
  assumes fresh: "x \<notin> named_fv A"
  shows "named_free_for B x A"
  using fresh by (induction A) auto

lemma named_subst_same_variable:
  "named_subst x (NVar x) A = A"
  by (induction A) (auto split: if_splits)

lemma named_free_for_same_variable:
  "named_free_for (NVar x) x A"
  by (induction A) auto

section \<open>Typing and nonlogical signature membership are preserved\<close>

text \<open>
  If A:τ and B has the fixed type G(x), replacing x by B preserves τ.
  Source: the fixed variable types of §1.1 and typed β in Figure 2.

  Isabelle representation: has_ntype uses the same G beneath every named
  binder. Therefore typing and signature preservation hold even for raw
  replacements that fail the free-for test. Those properties alone do not
  establish absence of capture or eligibility for the source β axiom.
\<close>

theorem named_subst_type:
  assumes body: "has_ntype L G A \<tau>"
    and replacement: "has_ntype L G B (G x)"
  shows "has_ntype L G (named_subst x B A) \<tau>"
  using body
proof (induction A arbitrary: \<tau>)
  case (NVar y)
  have ty: "\<tau> = G y" using NVar.prems by (simp only: named_var_type_iff)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis using replacement True ty by simp
  next
    case False
    show ?thesis using NVar.prems by (simp only: named_subst.simps False if_False)
  qed
next
  case NConst
  show ?case using NConst.prems by (simp only: named_subst.simps)
next
  case NLogical
  show ?case using NLogical.prems by (simp only: named_subst.simps)
next
  case (NApp F A)
  obtain \<sigma> where ft: "has_ntype L G F (Arr \<sigma> \<tau>)" and at: "has_ntype L G A \<sigma>"
    by (rule named_app_type_obtain[OF NApp.prems]; rule that; assumption)
  have fs: "has_ntype L G (named_subst x B F) (Arr \<sigma> \<tau>)" by (rule NApp.IH(1)[OF ft])
  have asub: "has_ntype L G (named_subst x B A) \<sigma>" by (rule NApp.IH(2)[OF at])
  show ?case unfolding named_subst.simps by (rule has_ntype.App[OF fs asub])
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis using NLam.prems True by simp
  next
    case False
    obtain \<rho> where ty: "\<tau> = Arr (G y) \<rho>" and at: "has_ntype L G A \<rho>"
      by (rule named_lam_type_obtain[OF NLam.prems]; rule that; assumption)
    have asub: "has_ntype L G (named_subst x B A) \<rho>" by (rule NLam.IH[OF at])
    have result: "has_ntype L G (NLam y (named_subst x B A)) (Arr (G y) \<rho>)"
      by (rule has_ntype.Lam[OF asub])
    show ?thesis using result by (simp only: named_subst.simps False if_False ty)
  qed
qed

theorem named_subst_signature_iff:
  "named_in_signature \<Sigma> (named_subst x B A) \<longleftrightarrow>
    (named_in_signature \<Sigma> A \<and> (x \<in> named_fv A \<longrightarrow> named_in_signature \<Sigma> B))"
  by (induction A) (auto split: if_splits)

corollary named_subst_signature:
  assumes "named_in_signature \<Sigma> A" and "named_in_signature \<Sigma> B"
  shows "named_in_signature \<Sigma> (named_subst x B A)"
  using assms by (simp only: named_subst_signature_iff) blast

corollary named_subst_language:
  assumes A: "named_in_language L \<Sigma> G A \<tau>"
    and B: "named_in_language L \<Sigma> G B (G x)"
  shows "named_in_language L \<Sigma> G (named_subst x B A) \<tau>"
proof -
  note ad = A[unfolded named_in_language_def]
  note bd = B[unfolded named_in_language_def]
  show ?thesis unfolding named_in_language_def
    by (rule conjI[OF named_subst_type[OF conjunct1[OF ad] conjunct1[OF bd]]
      named_subst_signature[OF conjunct2[OF ad] conjunct2[OF bd]]])
qed

section \<open>Free-variable bounds and the exact permitted-substitution equation\<close>

text \<open>
  FV(A[B/x]) ⊆ (FV(A) − {x}) ∪ FV(B).
  If B is free for x in A, the exact result is
  (FV(A) − {x}) ∪ FV(B) when x occurs free in A, and FV(A) otherwise.

  Isabelle representation: the first bound allows raw capture; the exact
  equation explicitly assumes named_free_for. In a different binder y,
  either y is absent from FV(B), or x is absent from the body and no
  replacement occurs there. No α-renaming result is used.
\<close>

lemma named_subst_fv_upper:
  "named_fv (named_subst x B A) \<subseteq> (named_fv A - {x}) \<union> named_fv B"
  by (induction A) (auto split: if_splits)

lemma named_subst_fv_bound:
  "named_fv (named_subst x B A) \<subseteq>
    (named_fv A - {x}) \<union> (if x \<in> named_fv A then named_fv B else {})"
proof (cases "x \<in> named_fv A")
  case True
  show ?thesis using named_subst_fv_upper[where x=x and B=B and A=A] by (simp only: True if_True)
next
  case False
  show ?thesis by (simp add: named_subst_fresh[OF False] False)
qed

theorem named_subst_fv_exact:
  assumes free_for: "named_free_for B x A"
  shows "named_fv (named_subst x B A) =
    (named_fv A - {x}) \<union> (if x \<in> named_fv A then named_fv B else {})"
  using free_for
proof (induction A)
  case (NVar y)
  show ?case by (cases "y = x") simp_all
next
  case NConst
  show ?case by simp
next
  case NLogical
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for B x F" and fa: "named_free_for B x A"
    using NApp.prems by simp_all
  note first = NApp.IH(1)[OF ff]
  note second = NApp.IH(2)[OF fa]
  show ?case by (simp only: named_subst.simps named_fv.simps first second)
    (auto split: if_splits)
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    note different = False
    have body_free: "named_free_for B x A" using NLam.prems different by simp
    note body = NLam.IH[OF body_free]
    show ?thesis
    proof (cases "x \<in> named_fv A")
      case False
      show ?thesis using False different
        by (simp add: named_subst_fresh[OF False])
    next
      case True
      have replacement_fresh: "y \<notin> named_fv B"
        using NLam.prems different True by simp
      show ?thesis using True different replacement_fresh
        by (auto simp: body)
    qed
  qed
qed

lemma named_capture_is_rejected:
  assumes different: "x \<noteq> y"
  shows "\<not> named_free_for (NVar y) x (NLam y (NVar x))"
  using different by simp

end
