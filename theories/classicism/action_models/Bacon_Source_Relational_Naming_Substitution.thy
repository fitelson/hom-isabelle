theory Bacon_Source_Relational_Naming_Substitution
  imports Bacon_Source_Relational_Naming_Replacement
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Literal substitution through a finite naming replacement\<close>

lemma paper_R_naming_subst_support:
  "paper_R_naming_support (named_subst n B A) \<subseteq>
    paper_R_naming_support A \<union> paper_R_naming_support B"
  by (induction A) (auto split: sum.splits if_splits)

lemma paper_R_naming_replace_subst:
  assumes marker: "n \<notin> x ` paper_R_naming_support A"
  shows "paper_R_naming_replace x (named_subst n B A) =
    named_subst n (paper_R_naming_replace x B) (paper_R_naming_replace x A)"
  using marker by (induction A) (auto split: sum.splits if_splits)

lemma paper_R_naming_replace_preserves_fresh:
  assumes original: "n \<notin> named_fv A" and markers: "n \<notin> x ` paper_R_naming_support A"
  shows "n \<notin> named_fv (paper_R_naming_replace x A)"
  using paper_R_naming_replace_fv_bound[where x=x and A=A] original markers by blast

theorem paper_R_naming_replace_free_for:
  assumes free_for: "named_free_for B n A"
    and marker: "n \<notin> x ` paper_R_naming_support A"
    and capture: "x ` paper_R_naming_support B \<inter> named_vars A = {}"
  shows "named_free_for (paper_R_naming_replace x B) n (paper_R_naming_replace x A)"
  using free_for marker capture
proof (induction A)
  case (NVar m)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by (cases c) simp_all
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for B n F" and af: "named_free_for B n A"
    and fm: "n \<notin> x ` paper_R_naming_support F" and am: "n \<notin> x ` paper_R_naming_support A"
    and fc: "x ` paper_R_naming_support B \<inter> named_vars F = {}"
    and ac: "x ` paper_R_naming_support B \<inter> named_vars A = {}"
    using NApp.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps named_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF ff fm fc] NApp.IH(2)[OF af am ac]])
next
  case (NLam m A)
  show ?case
  proof (cases "m = n")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have body_ff: "named_free_for B n A"
      and old_guard: "m \<notin> named_fv B \<or> n \<notin> named_fv A"
      using NLam.prems(1) False by auto
    have body_marker: "n \<notin> x ` paper_R_naming_support A" using NLam.prems(2) by simp
    have body_capture: "x ` paper_R_naming_support B \<inter> named_vars A = {}"
      and binder_marker: "m \<notin> x ` paper_R_naming_support B" using NLam.prems(3) by auto
    have inner: "named_free_for (paper_R_naming_replace x B) n (paper_R_naming_replace x A)"
      by (rule NLam.IH[OF body_ff body_marker body_capture])
    have new_guard: "m \<notin> named_fv (paper_R_naming_replace x B) \<or>
      n \<notin> named_fv (paper_R_naming_replace x A)"
      using old_guard binder_marker body_marker
        paper_R_naming_replace_fv_bound[where x=x and A=B]
        paper_R_naming_replace_fv_bound[where x=x and A=A] by blast
    show ?thesis by (simp only: paper_R_naming_replace.simps named_free_for.simps False;
      use inner new_guard in blast)
  qed
qed

text \<open>
  The first guard prevents a new constant marker from becoming the
  substitution variable. The second prevents markers introduced into
  the payload from being captured by original binders. Both follow from
  one chart avoiding all variable names of the β redex. No closed-payload
  condition, α conversion, typing theorem or model assumption is used.
\<close>

end
