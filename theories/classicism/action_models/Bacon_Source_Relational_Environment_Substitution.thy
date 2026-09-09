theory Bacon_Source_Relational_Environment_Substitution
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>Literal simultaneous substitution from a partial term assignment\<close>

text \<open>
  A defined variable n is replaced by r(n) as a whole, without recursively
  substituting into that payload. An undefined variable stays NVar n.
  Under λn, delete the n entry before processing the body. This protects
  bound occurrences and repeated/shadowed binders. Closed assigned payloads
  cannot be captured; for arbitrary open payloads no capture-avoidance claim
  is made. Source: the representative substitution of Theorem 3.2, p.45 n.64.

  The operation is generic in both name and logical-symbol carriers.
  Unlike a total closed-replacement convention it does not force unassigned
  names to close. The older book_environment_subst supplies a useful proof
  pattern, but a formal adapter using a totalizer with default NVar remains
  separate; no equivalence to that operation is asserted here. No F proof,
  semantic interpretation or alternative model construction is involved.
\<close>

fun paper_R_environment_subst ::
  "(('c,'l) named_term) named_assignment \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "paper_R_environment_subst r (NVar n) = (case r n of None \<Rightarrow> NVar n | Some A \<Rightarrow> A)"
| "paper_R_environment_subst r (NConst c \<sigma>) = NConst c \<sigma>"
| "paper_R_environment_subst r (NLogical l) = NLogical l"
| "paper_R_environment_subst r (NApp F A) = NApp (paper_R_environment_subst r F) (paper_R_environment_subst r A)"
| "paper_R_environment_subst r (NLam n A) = NLam n (paper_R_environment_subst (r(n := None)) A)"

lemma paper_R_environment_subst_empty:
  "paper_R_environment_subst Map.empty A = A"
  by (induction A) simp_all

lemma paper_R_environment_subst_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> r n = s n"
  shows "paper_R_environment_subst r A = paper_R_environment_subst s A"
  using agree
proof (induction A arbitrary: r s)
  case (NVar n)
  have equal: "r n = s n" by (rule NVar.prems; simp)
  show ?case by (simp only: paper_R_environment_subst.simps equal)
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fa: "r n = s n" if "n \<in> named_fv F" for n using NApp.prems that by auto
  have aa: "r n = s n" if "n \<in> named_fv A" for n using NApp.prems that by auto
  show ?case by (simp only: paper_R_environment_subst.simps NApp.IH(1)[OF fa] NApp.IH(2)[OF aa])
next
  case (NLam n A)
  have body: "(r(n := None)) m = (s(n := None)) m" if free: "m \<in> named_fv A" for m
  proof (cases "m = n")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have outer: "m \<in> named_fv (NLam n A)" using free False by simp
    have equal: "r m = s m" by (rule NLam.prems[OF outer])
    show ?thesis by (simp add: False equal)
  qed
  show ?case by (simp only: paper_R_environment_subst.simps NLam.IH[OF body])
qed

lemma paper_R_environment_subst_closed_fixed:
  assumes closed: "named_fv A = {}"
  shows "paper_R_environment_subst r A = A"
proof -
  have equal: "paper_R_environment_subst r A = paper_R_environment_subst Map.empty A"
    by (rule paper_R_environment_subst_locality; simp only: closed; simp)
  show ?thesis using equal by (simp only: paper_R_environment_subst_empty)
qed

section \<open>Closed assigned payloads remove exactly the assigned free names\<close>

theorem paper_R_environment_subst_fv:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
  shows "named_fv (paper_R_environment_subst r A) = named_fv A - dom r"
  using closed
proof (induction A arbitrary: r)
  case (NVar n)
  show ?case
  proof (cases "r n")
    case None
    show ?thesis using None by (auto simp: dom_def)
  next
    case (Some B)
    have empty: "named_fv B = {}" by (rule NVar.prems[OF Some])
    show ?thesis using Some empty by (auto simp: dom_def)
  qed
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case by (simp only: paper_R_environment_subst.simps named_fv.simps
    NApp.IH(1)[OF NApp.prems] NApp.IH(2)[OF NApp.prems]; blast)
next
  case (NLam n A)
  have body_closed: "named_fv B = {}" if assigned: "(r(n := None)) m = Some B" for m B
  proof -
    have old: "r m = Some B" using assigned by (auto split: if_splits)
    show ?thesis by (rule NLam.prems[OF old])
  qed
  show ?case by (simp only: paper_R_environment_subst.simps named_fv.simps NLam.IH[OF body_closed] dom_fun_upd; auto)
qed

corollary paper_R_environment_subst_adequate_closed:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}" and adequate: "named_adequate r A"
  shows "named_fv (paper_R_environment_subst r A) = {}"
  using adequate by (simp only: paper_R_environment_subst_fv[OF closed] named_adequate_def; blast)

end
