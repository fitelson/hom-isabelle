theory Bacon_Book_Simultaneous_Substitution_Peeling
  imports Bacon_Book_Simultaneous_Substitution_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>A fresh marker factors one simultaneous substitution entry\<close>

text \<open>
  Replace the selected key k by a fresh variable z, apply the remaining
  table, then insert the original payload B for z. Payloads inserted by
  the remaining table contain no free z, so this last step leaves them
  unchanged even if they mention k or other replaced keys.
  Source role: the simultaneous single-pass substitution discipline of
  Bacon's Definition 5.2, p.99.

  Representation: the marker operation is the singleton table
  [(k,NVar z)], not another syntax definition. A binder disables only
  its own variable key. The public equation removes every later copy
  of k, respecting the table's first-match lookup convention.
  Status: raw syntax equality only; no free-for, typing, theory or
  semantic premise. Freshness of z for B is unnecessary here because
  the final literal substitution does not recurse into its payload.
\<close>

lemma book_peeling_fresh:
  assumes fresh: "z \<notin> named_fv A"
    and payloads: "\<And>j C. map_of \<theta> j = Some C \<Longrightarrow> z \<notin> named_fv C"
  shows "z \<notin> named_fv (book_simult_subst G \<theta> A)"
  using fresh payloads
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case using NVar.prems
    by (cases "map_of \<theta> (BSVar n (G n))") auto
next
  case (NConst c \<sigma>)
  show ?case using NConst.prems
    by (cases "map_of \<theta> (BSConst c \<sigma>)") auto
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "z \<notin> named_fv F" and af: "z \<notin> named_fv A" using NApp.prems(1) by simp_all
  show ?case using NApp.IH(1)[OF ff NApp.prems(2)] NApp.IH(2)[OF af NApp.prems(2)] by simp
next
  case (NLam n A)
  show ?case
  proof (cases "n = z")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have body_fresh: "z \<notin> named_fv A" using NLam.prems(1) False by auto
    have remaining: "\<And>j C. map_of (book_subst_disable (BSVar n (G n)) \<theta>) j = Some C \<Longrightarrow>
      z \<notin> named_fv C"
      by (rule NLam.prems(2), rule book_subst_disabled_lookup, assumption)
    show ?thesis using NLam.IH[OF body_fresh remaining] by simp
  qed
qed

theorem book_simult_peeling_core:
  assumes fresh: "z \<notin> named_vars A"
    and deleted: "map_of \<theta> k = None"
    and marker: "map_of \<theta> (BSVar z (G z)) = None"
    and payloads: "\<And>j C. map_of \<theta> j = Some C \<Longrightarrow> z \<notin> named_fv C"
  shows "book_simult_subst G ((k,B) # \<theta>) A =
    named_subst z B (book_simult_subst G \<theta> (book_simult_subst G [(k,NVar z)] A))"
  using fresh deleted marker payloads
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case
  proof (cases "BSVar n (G n) = k")
    case True
    show ?thesis by (simp add: True eq_commute NVar.prems(3))
  next
    case False
    have distinct: "n \<noteq> z" using NVar.prems(1) by simp
    show ?thesis
    proof (cases "map_of \<theta> (BSVar n (G n))")
      case None
      show ?thesis by (simp add: False eq_commute None distinct NVar.prems(3))
    next
      case (Some C)
      have fresh_C: "z \<notin> named_fv C" by (rule NVar.prems(4)[OF Some])
      have unchanged: "named_subst z B C = C" by (rule named_subst_fresh[OF fresh_C])
      show ?thesis by (simp add: False eq_commute Some unchanged NVar.prems(2,3))
    qed
  qed
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases "BSConst c \<sigma> = k")
    case True
    show ?thesis by (simp add: True eq_commute NConst.prems(3))
  next
    case False
    show ?thesis
    proof (cases "map_of \<theta> (BSConst c \<sigma>)")
      case None
      show ?thesis by (simp add: False eq_commute None NConst.prems(3))
    next
      case (Some C)
      have fresh_C: "z \<notin> named_fv C" by (rule NConst.prems(4)[OF Some])
      have unchanged: "named_subst z B C = C" by (rule named_subst_fresh[OF fresh_C])
      show ?thesis by (simp add: False eq_commute Some unchanged NConst.prems(2,3))
    qed
  qed
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "z \<notin> named_vars F" and af: "z \<notin> named_vars A" using NApp.prems(1) by simp_all
  show ?case by (simp only: book_simult_subst.simps named_subst.simps
    NApp.IH(1)[OF ff NApp.prems(2,3,4)] NApp.IH(2)[OF af NApp.prems(2,3,4)])
next
  case (NLam n A)
  let ?b = "BSVar n (G n)"
  let ?rest = "book_subst_disable ?b \<theta>"
  have distinct: "n \<noteq> z" and body_fresh: "z \<notin> named_vars A" using NLam.prems(1) by auto
  have remaining: "\<And>j C. map_of ?rest j = Some C \<Longrightarrow> z \<notin> named_fv C"
    by (rule NLam.prems(4), rule book_subst_disabled_lookup, assumption)
  show ?case
  proof (cases "k = ?b")
    case True
    have head_disabled: "book_subst_disable ?b ((k,B) # \<theta>) = ?rest"
      by (simp add: book_subst_disable_def True)
    have marker_disabled: "book_subst_disable ?b [(k,NVar z)] = []"
      by (simp add: book_subst_disable_def True)
    have body_fv_fresh: "z \<notin> named_fv A" using body_fresh named_fv_subset_vars by blast
    have result_fresh: "z \<notin> named_fv (book_simult_subst G ?rest A)"
      by (rule book_peeling_fresh[OF body_fv_fresh remaining])
    have unchanged: "named_subst z B (book_simult_subst G ?rest A) = book_simult_subst G ?rest A"
      by (rule named_subst_fresh[OF result_fresh])
    show ?thesis by (simp only: book_simult_subst.simps named_subst.simps
      head_disabled marker_disabled book_simult_subst_empty distinct if_False unchanged)
  next
    case False
    have head_disabled: "book_subst_disable ?b ((k,B) # \<theta>) = (k,B) # ?rest"
      by (simp add: book_subst_disable_def False)
    have marker_disabled: "book_subst_disable ?b [(k,NVar z)] = [(k,NVar z)]"
      by (simp add: book_subst_disable_def False)
    have rest_deleted: "map_of ?rest k = None"
      by (simp add: book_subst_lookup_disable NLam.prems(2))
    have rest_marker: "map_of ?rest (BSVar z (G z)) = None"
      by (simp add: book_subst_lookup_disable NLam.prems(3))
    have body_eq: "book_simult_subst G ((k,B) # ?rest) A =
      named_subst z B (book_simult_subst G ?rest (book_simult_subst G [(k,NVar z)] A))"
      by (rule NLam.IH[OF body_fresh rest_deleted rest_marker remaining])
    show ?thesis by (simp only: book_simult_subst.simps named_subst.simps
      head_disabled marker_disabled distinct if_False body_eq)
  qed
qed

lemma book_peeling_head_lookup:
  "map_of ((k,B) # rest) = map_of ((k,B) # book_subst_disable k rest)"
  by (rule ext) (simp add: book_subst_lookup_disable)

theorem book_simult_subst_peeling:
  assumes fresh: "z \<notin> named_vars A"
    and marker: "map_of (book_subst_disable k rest) (BSVar z (G z)) = None"
    and payloads: "\<And>j C. map_of (book_subst_disable k rest) j = Some C \<Longrightarrow> z \<notin> named_fv C"
  shows "book_simult_subst G ((k,B) # rest) A =
    named_subst z B (book_simult_subst G (book_subst_disable k rest)
      (book_simult_subst G [(k,NVar z)] A))"
proof -
  have deleted: "map_of (book_subst_disable k rest) k = None"
    by (simp add: book_subst_lookup_disable)
  have head_eq: "book_simult_subst G ((k,B) # rest) A =
    book_simult_subst G ((k,B) # book_subst_disable k rest) A"
    by (rule book_simult_subst_map_eq[OF book_peeling_head_lookup])
  have factored: "book_simult_subst G ((k,B) # book_subst_disable k rest) A =
    named_subst z B (book_simult_subst G (book_subst_disable k rest)
      (book_simult_subst G [(k,NVar z)] A))"
    by (rule book_simult_peeling_core[where G=G and z=z and k=k and A=A
          and \<theta>="book_subst_disable k rest", OF fresh deleted marker payloads])
  show ?thesis by (rule trans[OF head_eq factored])
qed

end
