theory Bacon_Source_Named_Signature_Retraction
  imports Bacon_Source_Named_Substitution
begin

section \<open>Replacing foreign constants by typed fresh variables\<close>

text \<open>
  For each type σ, choose a variable vσ of that type. Retain constants
  declared by Σ, and replace every other constant of type σ by vσ.
  The result belongs to ℒ(Σ); terms already in ℒ(Σ) are unchanged.
  Source role: the language qualification in Bacon–Dorr Definition 3.1(ii.d),
  p.44, and the fixed variable types and infinite stocks of §1.1, p.5.

  Isabelle representation. named_retract leaves original variable names,
  logical constants, and binder names unchanged. This leaf assumes the
  type and freshness properties of v; it does not construct v or require
  closed Σ-terms of every type. Literal substitution commutes with the
  retraction when no introduced name is the substituted variable. Its
  free-for condition is preserved when introduced names also avoid all
  names in the body. The latter guard prevents new binder capture.

  Status. Structural groundwork only: no conversion-chain conservativity,
  H theoremhood, or model assumption is used or asserted here.
\<close>

fun named_retract ::
  "'c ssignature \<Rightarrow> (otype \<Rightarrow> nat) \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term" where
  "named_retract \<Sigma> v (NVar n) = NVar n"
| "named_retract \<Sigma> v (NConst c \<sigma>) = (if c \<in> \<Sigma> \<sigma> then NConst c \<sigma> else NVar (v \<sigma>))"
| "named_retract \<Sigma> v (NLogical l) = NLogical l"
| "named_retract \<Sigma> v (NApp F A) = NApp (named_retract \<Sigma> v F) (named_retract \<Sigma> v A)"
| "named_retract \<Sigma> v (NLam n A) = NLam n (named_retract \<Sigma> v A)"

lemma named_retract_signature:
  "named_in_signature \<Sigma> (named_retract \<Sigma> v A)"
  by (induction A) (simp_all split: if_splits)

lemma named_retract_fixed:
  assumes signature: "named_in_signature \<Sigma> A"
  shows "named_retract \<Sigma> v A = A"
  using signature by (induction A) simp_all

theorem named_retract_type:
  assumes typed: "has_ntype L G A \<tau>"
    and stockmap: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>"
  shows "has_ntype L G (named_retract \<Sigma> v A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: named_retract.simps; rule has_ntype.Var)
next
  case (Const c \<sigma>)
  show ?case
  proof (cases "c \<in> \<Sigma> \<sigma>")
    case True
    show ?thesis by (simp only: named_retract.simps True if_True; rule has_ntype.Const)
  next
    case False
    have variable: "has_ntype L G (NVar (v \<sigma>)) (G (v \<sigma>))" by (rule has_ntype.Var)
    show ?thesis using variable by (simp only: named_retract.simps False if_False stockmap)
  qed
next
  case (Logical l)
  show ?case by (simp only: named_retract.simps; rule has_ntype.Logical)
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: named_retract.simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: named_retract.simps; rule has_ntype.Lam[OF Lam.IH])
qed

corollary named_retract_language:
  assumes typed: "has_ntype L G A \<tau>"
    and stockmap: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>"
  shows "named_in_language L \<Sigma> G (named_retract \<Sigma> v A) \<tau>"
  unfolding named_in_language_def
  by (rule conjI[OF named_retract_type[OF typed stockmap] named_retract_signature])

subsection \<open>Bounds on introduced free and bound names\<close>

lemma named_retract_fv_bound:
  "named_fv (named_retract \<Sigma> v A) \<subseteq> named_fv A \<union> range v"
  by (induction A) (auto split: if_splits)

lemma named_retract_vars_bound:
  "named_vars (named_retract \<Sigma> v A) \<subseteq> named_vars A \<union> range v"
  by (induction A) (auto split: if_splits)

lemma named_retract_fresh:
  assumes fresh: "n \<notin> named_fv A" and avoid: "\<And>\<sigma>. v \<sigma> \<noteq> n"
  shows "n \<notin> named_fv (named_retract \<Sigma> v A)"
proof -
  have not_range: "n \<notin> range v" using avoid by auto
  show ?thesis using named_retract_fv_bound[where \<Sigma>=\<Sigma> and v=v and A=A] fresh not_range by blast
qed

lemma named_retract_vars_fresh:
  assumes fresh: "n \<notin> named_vars A" and avoid: "\<And>\<sigma>. v \<sigma> \<noteq> n"
  shows "n \<notin> named_vars (named_retract \<Sigma> v A)"
proof -
  have not_range: "n \<notin> range v" using avoid by auto
  show ?thesis using named_retract_vars_bound[where \<Sigma>=\<Sigma> and v=v and A=A] fresh not_range by blast
qed

subsection \<open>Retraction and literal substitution\<close>

lemma named_retract_subst:
  assumes avoid: "\<And>\<sigma>. v \<sigma> \<noteq> x"
  shows "named_retract \<Sigma> v (named_subst x B A) =
    named_subst x (named_retract \<Sigma> v B) (named_retract \<Sigma> v A)"
proof (induction A)
  case (NVar n)
  show ?case by (cases "n = x") simp_all
next
  case (NConst c \<sigma>)
  show ?case by (cases "c \<in> \<Sigma> \<sigma>") (simp_all add: avoid)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case by (simp only: named_subst.simps named_retract.simps NApp.IH)
next
  case (NLam n A)
  show ?case by (cases "n = x") (simp_all add: NLam.IH)
qed

theorem named_retract_free_for:
  assumes free_for: "named_free_for B x A"
    and avoid_x: "\<And>\<sigma>. v \<sigma> \<noteq> x"
    and avoid_names: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A"
  shows "named_free_for (named_retract \<Sigma> v B) x (named_retract \<Sigma> v A)"
  using free_for avoid_names
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by (cases "c \<in> \<Sigma> \<sigma>") simp_all
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for B x F" and fa: "named_free_for B x A"
    using NApp.prems(1) by simp_all
  have avoid_f: "\<And>\<sigma>. v \<sigma> \<notin> named_vars F"
    and avoid_a: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A"
    using NApp.prems(2) by simp_all
  have left: "named_free_for (named_retract \<Sigma> v B) x (named_retract \<Sigma> v F)"
    by (rule NApp.IH(1)[OF ff avoid_f])
  have right: "named_free_for (named_retract \<Sigma> v B) x (named_retract \<Sigma> v A)"
    by (rule NApp.IH(2)[OF fa avoid_a])
  show ?case by (simp only: named_retract.simps named_free_for.simps; rule conjI[OF left right])
next
  case (NLam n A)
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have ff: "named_free_for B x A"
      and capture_guard: "n \<notin> named_fv B \<or> x \<notin> named_fv A"
      using NLam.prems(1) False by simp_all
    have avoid_body: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A"
      and avoid_n: "\<And>\<sigma>. v \<sigma> \<noteq> n"
      using NLam.prems(2) by simp_all
    have body: "named_free_for (named_retract \<Sigma> v B) x (named_retract \<Sigma> v A)"
      by (rule NLam.IH[OF ff avoid_body])
    have replacement_fresh: "n \<notin> named_fv B \<Longrightarrow>
      n \<notin> named_fv (named_retract \<Sigma> v B)"
      by (rule named_retract_fresh, assumption, rule avoid_n)
    have body_fresh: "x \<notin> named_fv A \<Longrightarrow>
      x \<notin> named_fv (named_retract \<Sigma> v A)"
      by (rule named_retract_fresh, assumption, rule avoid_x)
    have preserved_guard: "n \<notin> named_fv (named_retract \<Sigma> v B) \<or>
      x \<notin> named_fv (named_retract \<Sigma> v A)"
      using capture_guard replacement_fresh body_fresh by blast
    show ?thesis using body preserved_guard False by simp
  qed
qed

end
