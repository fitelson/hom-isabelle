theory Bacon_Book_Closed_Environment_Substitution
  imports Bacon_Book_Language
begin

section \<open>Replacing free variables by closed representatives\<close>

text \<open>
  A[r] replaces each free variable n by its chosen closed term r(n).
  Source role: the representative substitution in the interpretation
  displayed in Bacon's Theorem 15.3, p.321. This leaf supplies only
  its named-syntax infrastructure, not an interpretation or model.

  Representation. A bound-name set B protects names already beneath
  binders. At λn, recursion uses B∪{n}; repeated binders therefore keep
  n protected. Constants and logical symbols are unchanged. Replacement
  payloads are returned directly, without recursively substituting them.
  There is no automatic α-renaming. The raw operation can capture open
  payloads; requiring all payloads to be closed prevents that capture.
  Typing and language preservation alone do not require closedness.

  The logical-symbol carrier is generic, and Λ remains explicit. No
  β/η compatibility, representative equivalence, semantic J, default
  application, or domain construction is asserted.
\<close>

fun book_environment_subst ::
  "nat set \<Rightarrow> (nat \<Rightarrow> ('c,'l) named_term) \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_environment_subst B r (NVar n) = (if n \<in> B then NVar n else r n)"
| "book_environment_subst B r (NConst c \<sigma>) = NConst c \<sigma>"
| "book_environment_subst B r (NLogical l) = NLogical l"
| "book_environment_subst B r (NApp F A) =
    NApp (book_environment_subst B r F) (book_environment_subst B r A)"
| "book_environment_subst B r (NLam n A) = NLam n (book_environment_subst (insert n B) r A)"

theorem book_environment_subst_type:
  assumes typed: "has_ntype L G A \<tau>"
    and replacements: "\<And>n. has_ntype L G (r n) (G n)"
  shows "has_ntype L G (book_environment_subst B r A) \<tau>"
  using typed
proof (induction arbitrary: B rule: has_ntype.induct)
  case (Var n)
  show ?case by (cases "n \<in> B"; simp only: book_environment_subst.simps if_True if_False;
      (rule has_ntype.Var | rule replacements))
next
  case (Const c \<sigma>)
  show ?case by (simp only: book_environment_subst.simps; rule has_ntype.Const)
next
  case (Logical l)
  show ?case by (simp only: book_environment_subst.simps; rule has_ntype.Logical)
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: book_environment_subst.simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: book_environment_subst.simps; rule has_ntype.Lam[OF Lam.IH])
qed

theorem book_environment_subst_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and replacements: "\<And>n. book_in_language L \<Lambda> \<Sigma> G (r n) (G n)"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_environment_subst B r A) \<tau>"
  using language
proof (induction A arbitrary: B \<tau>)
  case (NVar n)
  have result_type: "\<tau> = G n" using NVar.prems by (simp only: book_language_var_iff)
  show ?case
  proof (cases "n \<in> B")
    case True
    show ?thesis by (simp only: book_environment_subst.simps True if_True; rule NVar.prems)
  next
    case False
    show ?thesis by (simp only: book_environment_subst.simps False if_False result_type; rule replacements)
  qed
next
  case (NConst c \<sigma>)
  show ?case by (simp only: book_environment_subst.simps; rule NConst.prems)
next
  case (NLogical l)
  show ?case by (simp only: book_environment_subst.simps; rule NLogical.prems)
next
  case (NApp F A)
  obtain \<sigma> where fl: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF NApp.prems]; rule that; assumption)
  have fs: "book_in_language L \<Lambda> \<Sigma> G (book_environment_subst B r F) (Arr \<sigma> \<tau>)"
    by (rule NApp.IH(1)[OF fl])
  have asub: "book_in_language L \<Lambda> \<Sigma> G (book_environment_subst B r A) \<sigma>"
    by (rule NApp.IH(2)[OF al])
  show ?case by (simp only: book_environment_subst.simps; rule book_language_App[OF fs asub])
next
  case (NLam n A)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and al: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_Lam_obtain[OF NLam.prems]; rule that; assumption)
  have asub: "book_in_language L \<Lambda> \<Sigma> G (book_environment_subst (insert n B) r A) \<rho>"
    by (rule NLam.IH[OF al])
  show ?case by (simp only: book_environment_subst.simps arrow; rule book_language_Lam[OF asub])
qed

section \<open>Closed payloads leave only protected free names\<close>

theorem book_environment_subst_fv:
  assumes closed: "\<And>n. named_fv (r n) = {}"
  shows "named_fv (book_environment_subst B r A) = named_fv A \<inter> B"
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case by (cases "n \<in> B"; simp add: closed)
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case by (simp only: book_environment_subst.simps named_fv.simps NApp.IH; blast)
next
  case (NLam n A)
  show ?case by (simp only: book_environment_subst.simps named_fv.simps NLam.IH; blast)
qed

corollary book_environment_subst_fv_bound:
  assumes closed: "\<And>n. named_fv (r n) = {}"
  shows "named_fv (book_environment_subst B r A) \<subseteq> B"
  by (simp only: book_environment_subst_fv[OF closed]; rule Int_lower2)

corollary book_environment_subst_closed:
  assumes closed: "\<And>n. named_fv (r n) = {}"
  shows "named_fv (book_environment_subst {} r A) = {}"
  by (simp only: book_environment_subst_fv[OF closed] Int_empty_right)

theorem book_environment_subst_fixed:
  assumes protected: "named_fv A \<subseteq> B"
  shows "book_environment_subst B r A = A"
  using protected
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case using NVar.prems by simp
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fp: "named_fv F \<subseteq> B" and ap: "named_fv A \<subseteq> B"
    using NApp.prems by auto
  show ?case by (simp only: book_environment_subst.simps NApp.IH(1)[OF fp] NApp.IH(2)[OF ap])
next
  case (NLam n A)
  have ap: "named_fv A \<subseteq> insert n B" using NLam.prems by auto
  show ?case by (simp only: book_environment_subst.simps NLam.IH[OF ap])
qed

corollary book_environment_subst_closed_fixed:
  assumes closed: "named_fv A = {}"
  shows "book_environment_subst {} r A = A"
  by (rule book_environment_subst_fixed; simp only: closed; rule subset_refl)

section \<open>Only active free occurrences inspect the replacement function\<close>

theorem book_environment_subst_locality:
  assumes agree: "\<And>n. n \<in> named_fv A - B \<Longrightarrow> r n = s n"
  shows "book_environment_subst B r A = book_environment_subst B s A"
  using agree
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case
  proof (cases "n \<in> B")
    case True
    show ?thesis by (simp only: book_environment_subst.simps True if_True)
  next
    case False
    have active: "n \<in> named_fv (NVar n) - B" using False by simp
    have same: "r n = s n" by (rule NVar.prems[OF active])
    show ?thesis by (simp only: book_environment_subst.simps False if_False same)
  qed
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fa: "r n = s n" if "n \<in> named_fv F - B" for n
    by (rule NApp.prems; use that in \<open>auto\<close>)
  have aa: "r n = s n" if "n \<in> named_fv A - B" for n
    by (rule NApp.prems; use that in \<open>auto\<close>)
  show ?case by (simp only: book_environment_subst.simps NApp.IH(1)[OF fa] NApp.IH(2)[OF aa])
next
  case (NLam n A)
  have body_agree: "r m = s m" if "m \<in> named_fv A - insert n B" for m
    by (rule NLam.prems; use that in \<open>auto\<close>)
  show ?case by (simp only: book_environment_subst.simps NLam.IH[OF body_agree])
qed

end
