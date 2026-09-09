theory Bacon_Book_Simultaneous_Substitution_Peeling_Free_For
  imports Bacon_Book_Simultaneous_Substitution_Peeling
begin

section \<open>Capture conditions for one-marker peeling\<close>

text \<open>
  Write θ′ for θ with every occurrence of the first key k removed.
  For a fresh variable z, A[(k,B)#θ] factors through A[k:=z], then θ′,
  then [B/z]. This leaf checks that all three replacements are free for
  their arguments whenever the original simultaneous replacement is.
  Source: Bacon, Definition 5.2, p.99, the no-capture proviso.

  Representation. Freshness for A includes bound names. The remaining
  table neither replaces z nor inserts a payload containing free z.
  No freshness of z for B is needed: the final replacement is single-pass.
  These are syntax lemmas, with no typing, theory, or model premise.
\<close>

lemma book_marker_keys_bound:
  "book_term_keys G (book_simult_subst G [(k,NVar z)] A)
    \<subseteq> book_term_keys G A \<union> {BSVar z (G z)}"
proof (induction A)
  case (NVar n)
  show ?case by (simp; split if_splits; simp)
next
  case (NConst c \<sigma>)
  show ?case by (simp; split if_splits; simp)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case using NApp.IH by (simp only: book_simult_subst.simps book_term_keys.simps; blast)
next
  case (NLam n A)
  show ?case
  proof (cases "k = BSVar n (G n)")
    case True
    show ?thesis by (auto simp: book_subst_disable_def True book_simult_subst_empty)
  next
    case False
    show ?thesis using NLam.IH
      by (simp add: book_subst_disable_def False; blast)
  qed
qed

lemma book_marker_absent:
  assumes absent: "k \<notin> book_term_keys G A"
  shows "book_simult_subst G [(k,NVar z)] A = A"
  using absent
proof (induction A)
  case (NVar n)
  show ?case using NVar.prems by (simp add: eq_commute)
next
  case (NConst c \<sigma>)
  show ?case using NConst.prems by (simp add: eq_commute)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fk: "k \<notin> book_term_keys G F" and ak: "k \<notin> book_term_keys G A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_simult_subst.simps NApp.IH(1)[OF fk] NApp.IH(2)[OF ak])
next
  case (NLam n A)
  show ?case
  proof (cases "k = BSVar n (G n)")
    case True
    show ?thesis by (simp add: book_subst_disable_def True book_simult_subst_empty)
  next
    case False
    have ak: "k \<notin> book_term_keys G A" using NLam.prems False by simp
    show ?thesis by (simp add: book_subst_disable_def False NLam.IH[OF ak])
  qed
qed

lemma book_marker_free_for:
  assumes fresh: "z \<notin> named_vars A"
  shows "book_simult_free_for G [(k,NVar z)] A"
  using fresh
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "z \<notin> named_vars F" and af: "z \<notin> named_vars A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_simult_free_for.simps; rule conjI[OF NApp.IH(1)[OF ff] NApp.IH(2)[OF af]])
next
  case (NLam n A)
  have distinct: "n \<noteq> z" and af: "z \<notin> named_vars A"
    using NLam.prems by auto
  show ?case
  proof (cases "k = BSVar n (G n)")
    case True
    show ?thesis by (simp add: book_subst_disable_def True book_simult_free_for_empty)
  next
    case False
    show ?thesis using NLam.IH[OF af] distinct
      by (auto simp: book_subst_disable_def False split: if_splits)
  qed
qed

lemma book_peeling_remaining_free_for_core:
  assumes fresh: "z \<notin> named_vars A"
    and deleted: "map_of \<theta> k = None"
    and marker: "map_of \<theta> (BSVar z (G z)) = None"
    and permitted: "book_simult_free_for G ((k,B)#\<theta>) A"
  shows "book_simult_free_for G \<theta> (book_simult_subst G [(k,NVar z)] A)"
  using fresh deleted marker permitted
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case by (simp; split if_splits; simp)
next
  case (NConst c \<sigma>)
  show ?case by (simp; split if_splits; simp)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "z \<notin> named_vars F" and af: "z \<notin> named_vars A"
    using NApp.prems(1) by simp_all
  have fp: "book_simult_free_for G ((k,B)#\<theta>) F"
    and ap: "book_simult_free_for G ((k,B)#\<theta>) A"
    using NApp.prems(4) by simp_all
  show ?case unfolding book_simult_subst.simps book_simult_free_for.simps
    by (rule conjI[OF NApp.IH(1)[OF ff NApp.prems(2,3) fp]
        NApp.IH(2)[OF af NApp.prems(2,3) ap]])
next
  case (NLam n A)
  let ?b = "BSVar n (G n)"
  let ?rest = "book_subst_disable ?b \<theta>"
  let ?marked = "book_simult_subst G [(k,NVar z)] A"
  have af: "z \<notin> named_vars A" using NLam.prems(1) by simp
  show ?case
  proof (cases "k = ?b")
    case True
    show ?thesis using NLam.prems(4)
      by (simp add: book_subst_disable_def True book_simult_subst_empty)
  next
    case False
    have head_disabled: "book_subst_disable ?b ((k,B)#\<theta>) = (k,B)#?rest"
      by (simp add: book_subst_disable_def False)
    have singleton_disabled: "book_subst_disable ?b [(k,NVar z)] = [(k,NVar z)]"
      by (simp add: book_subst_disable_def False)
    have ap: "book_simult_free_for G ((k,B)#?rest) A"
      by (rule conjunct1[OF NLam.prems(4)[unfolded book_simult_free_for.simps head_disabled]])
    have old_guard: "\<forall>j\<in>book_term_keys G A. \<forall>C.
        map_of ((k,B)#?rest) j = Some C \<longrightarrow> n \<notin> named_fv C"
      by (rule conjunct2[OF NLam.prems(4)[unfolded book_simult_free_for.simps head_disabled]])
    have rd: "map_of ?rest k = None"
      by (simp add: book_subst_lookup_disable NLam.prems(2))
    have rm: "map_of ?rest (BSVar z (G z)) = None"
      by (simp add: book_subst_lookup_disable NLam.prems(3))
    have body_ok: "book_simult_free_for G ?rest ?marked"
      by (rule NLam.IH[OF af rd rm ap])
    have outer_ok: "\<forall>j\<in>book_term_keys G ?marked. \<forall>C.
      map_of ?rest j = Some C \<longrightarrow> n \<notin> named_fv C"
    proof (intro ballI allI impI)
      fix j C
      assume member: "j \<in> book_term_keys G ?marked" and found: "map_of ?rest j = Some C"
      have not_marker: "j \<noteq> BSVar z (G z)" using found rm by auto
      have not_head: "j \<noteq> k" using found rd by auto
      have old_member: "j \<in> book_term_keys G A"
        using book_marker_keys_bound[where G=G and k=k and z=z and A=A] member not_marker by blast
      have old_found: "map_of ((k,B)#?rest) j = Some C"
        by (simp add: not_head eq_commute found)
      show "n \<notin> named_fv C" using old_guard old_member old_found by blast
    qed
    show ?thesis by (simp only: book_simult_subst.simps singleton_disabled book_simult_free_for.simps;
        rule conjI[OF body_ok outer_ok])
  qed
qed

lemma book_peeling_payload_free_for_core:
  assumes fresh: "z \<notin> named_vars A"
    and payloads: "\<And>j C. map_of \<theta> j = Some C \<Longrightarrow> z \<notin> named_fv C"
    and permitted: "book_simult_free_for G ((k,B)#\<theta>) A"
  shows "named_free_for B z (book_simult_subst G \<theta>
    (book_simult_subst G [(k,NVar z)] A))"
  using fresh payloads permitted
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case
  proof (cases "k = BSVar n (G n)")
    case True
    show ?thesis using NVar.prems(2)
      by (cases "map_of \<theta> (BSVar z (G z))")
        (auto simp: True intro: named_free_for_fresh)
  next
    case False
    show ?thesis using NVar.prems(2)
      by (cases "map_of \<theta> (BSVar n (G n))")
        (auto simp: False intro: named_free_for_fresh)
  qed
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases "k = BSConst c \<sigma>")
    case True
    show ?thesis using NConst.prems(2)
      by (cases "map_of \<theta> (BSVar z (G z))")
        (auto simp: True intro: named_free_for_fresh)
  next
    case False
    show ?thesis using NConst.prems(2)
      by (cases "map_of \<theta> (BSConst c \<sigma>)")
        (auto simp: False intro: named_free_for_fresh)
  qed
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "z \<notin> named_vars F" and af: "z \<notin> named_vars A"
    using NApp.prems(1) by simp_all
  have fp: "book_simult_free_for G ((k,B)#\<theta>) F"
    and ap: "book_simult_free_for G ((k,B)#\<theta>) A"
    using NApp.prems(3) by simp_all
  show ?case unfolding book_simult_subst.simps named_free_for.simps
    by (rule conjI[OF NApp.IH(1)[OF ff NApp.prems(2) fp]
        NApp.IH(2)[OF af NApp.prems(2) ap]])
next
  case (NLam n A)
  let ?b = "BSVar n (G n)"
  let ?rest = "book_subst_disable ?b \<theta>"
  let ?marked = "book_simult_subst G [(k,NVar z)] A"
  have af: "z \<notin> named_vars A" using NLam.prems(1) by simp
  have fv_fresh: "z \<notin> named_fv A" using af named_fv_subset_vars by blast
  have remaining: "\<And>j C. map_of ?rest j = Some C \<Longrightarrow> z \<notin> named_fv C"
    by (rule NLam.prems(2), rule book_subst_disabled_lookup, assumption)
  show ?case
  proof (cases "k = ?b")
    case True
    have result_fresh: "z \<notin> named_fv (book_simult_subst G ?rest A)"
      by (rule book_peeling_fresh[OF fv_fresh remaining])
    have result_ok: "named_free_for B z (NLam n (book_simult_subst G ?rest A))"
      by (rule named_free_for_fresh; simp add: result_fresh)
    show ?thesis using result_ok
      by (simp add: book_subst_disable_def True book_simult_subst_empty)
  next
    case False
    have head_disabled: "book_subst_disable ?b ((k,B)#\<theta>) = (k,B)#?rest"
      by (simp add: book_subst_disable_def False)
    have singleton_disabled: "book_subst_disable ?b [(k,NVar z)] = [(k,NVar z)]"
      by (simp add: book_subst_disable_def False)
    have ap: "book_simult_free_for G ((k,B)#?rest) A"
      by (rule conjunct1[OF NLam.prems(3)[unfolded book_simult_free_for.simps head_disabled]])
    have old_guard: "\<forall>j\<in>book_term_keys G A. \<forall>C.
        map_of ((k,B)#?rest) j = Some C \<longrightarrow> n \<notin> named_fv C"
      by (rule conjunct2[OF NLam.prems(3)[unfolded book_simult_free_for.simps head_disabled]])
    have body_ok: "named_free_for B z (book_simult_subst G ?rest ?marked)"
      by (rule NLam.IH[OF af remaining ap])
    have guard: "n \<notin> named_fv B \<or> z \<notin> named_fv (book_simult_subst G ?rest ?marked)"
    proof (cases "k \<in> book_term_keys G A")
      case True
      have found: "map_of ((k,B)#?rest) k = Some B" by simp
      have nf: "n \<notin> named_fv B" using old_guard True found by blast
      show ?thesis by (rule disjI1[OF nf])
    next
      case False
      have marked_eq: "?marked = A" by (rule book_marker_absent[OF False])
      have result_fresh: "z \<notin> named_fv (book_simult_subst G ?rest ?marked)"
        unfolding marked_eq by (rule book_peeling_fresh[OF fv_fresh remaining])
      show ?thesis by (rule disjI2[OF result_fresh])
    qed
    show ?thesis unfolding book_simult_subst.simps singleton_disabled named_free_for.simps
      by (rule disjI2; rule conjI[OF body_ok guard])
  qed
qed

theorem book_simult_subst_peeling_free_for:
  assumes fresh: "z \<notin> named_vars A"
    and marker: "map_of (book_subst_disable k rest) (BSVar z (G z)) = None"
    and payloads: "\<And>j C. map_of (book_subst_disable k rest) j = Some C \<Longrightarrow> z \<notin> named_fv C"
    and permitted: "book_simult_free_for G ((k,B)#rest) A"
  shows "book_simult_free_for G [(k,NVar z)] A \<and>
    book_simult_free_for G (book_subst_disable k rest) (book_simult_subst G [(k,NVar z)] A) \<and>
    named_free_for B z (book_simult_subst G (book_subst_disable k rest)
      (book_simult_subst G [(k,NVar z)] A))"
proof -
  have deleted: "map_of (book_subst_disable k rest) k = None"
    by (simp add: book_subst_lookup_disable)
  have permitted_tail: "book_simult_free_for G ((k,B)#book_subst_disable k rest) A"
    using book_simult_free_for_map_eq[OF book_peeling_head_lookup, where G=G and A=A] permitted by simp
  have first: "book_simult_free_for G [(k,NVar z)] A"
    by (rule book_marker_free_for[OF fresh])
  have second: "book_simult_free_for G (book_subst_disable k rest) (book_simult_subst G [(k,NVar z)] A)"
    by (rule book_peeling_remaining_free_for_core[where G=G and z=z and k=k and A=A,
          OF fresh deleted marker permitted_tail])
  have third: "named_free_for B z (book_simult_subst G (book_subst_disable k rest)
      (book_simult_subst G [(k,NVar z)] A))"
    by (rule book_peeling_payload_free_for_core[where G=G and z=z and k=k and A=A,
          OF fresh payloads permitted_tail])
  show ?thesis by (rule conjI[OF first conjI[OF second third]])
qed

end
