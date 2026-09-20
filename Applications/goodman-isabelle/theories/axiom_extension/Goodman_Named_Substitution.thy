theory Goodman_Named_Substitution
  imports Goodman_Named_Renaming Goodman_Expansion_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Renaming_Conversion
begin

section \<open>Capture avoidance for translations under a slot chart\<close>

lemma gi_closed_free_for:
  "named_fv C = {} \<Longrightarrow> named_free_for B x C"
  by (rule named_free_for_fresh; simp)

lemma gi_translation_free_for:
  assumes rich: "sg_rich G" and support: "named_fv B \<subseteq> set ns"
  shows "named_free_for B x (gi_to_book G ns k A)"
  using support
proof (induction A arbitrary: ns)
  case Var
  show ?case by simp
next
  case Const
  show ?case by simp
next
  case App
  then show ?case by simp
next
  case (Lam \<sigma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have absent: "?n \<notin> named_fv B"
    using named_chart_fresh_notin[OF rich, where ns=ns and \<sigma>=\<sigma>] Lam.prems by blast
  have body: "named_free_for B x (gi_to_book G (?n # ns) k A)"
    by (rule Lam.IH; use Lam.prems in auto)
  show ?case by (simp add: Let_def body absent)
next
  case Eq
  then show ?case by (simp add: book_leibniz_def gi_closed_free_for[OF book_leibniz_const_closed])
next
  case Neg
  then show ?case by (simp add: book_not_def gi_closed_free_for[OF book_not_const_closed])
next
  case Conj
  then show ?case by (simp add: book_and_def gi_closed_free_for[OF book_and_const_closed])
next
  case Disj
  then show ?case by (simp add: book_or_def gi_closed_free_for[OF book_or_const_closed])
next
  case Imp
  then show ?case by (simp add: book_imp_def)
next
  case (Forall \<sigma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have absent: "?n \<notin> named_fv B"
    using named_chart_fresh_notin[OF rich, where ns=ns and \<sigma>=\<sigma>] Forall.prems by blast
  have body: "named_free_for B x (gi_to_book G (?n # ns) k A)"
    by (rule Forall.IH; use Forall.prems in auto)
  show ?case by (simp add: Let_def book_all_def body absent)
next
  case (Exists \<sigma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have absent: "?n \<notin> named_fv B"
    using named_chart_fresh_notin[OF rich, where ns=ns and \<sigma>=\<sigma>] Exists.prems by blast
  have body: "named_free_for B x (gi_to_book G (?n # ns) k A)"
    by (rule Exists.IH; use Exists.prems in auto)
  show ?case by (simp add: Let_def book_exists_def body absent
    gi_closed_free_for[OF book_exists_const_closed])
qed

lemma gi_source_beta_deterministic:
  "sbeta_contract A B \<Longrightarrow> sbeta_contract A C \<Longrightarrow> B = C"
  by (auto elim: sbeta_contract.cases)

section \<open>Substitution at a β redex commutes up to α\<close>

theorem gi_to_book_subst0_alpha:
  assumes rich: "sg_rich G" and body: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and argument: "\<Gamma> \<turnstile> N : \<sigma>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  defines "n \<equiv> named_chart_fresh G ns \<sigma>"
  shows "named_alpha G
    (named_subst n (gi_to_book G ns k N) (gi_to_book G (n # ns) k M))
    (gi_to_book G ns k (subst0 N M))"
proof -
  let ?X = "App (Lam \<sigma> M) N"
  let ?Y = "subst0 N M"
  let ?L = "gi_to_book G ns k ?X"
  let ?R = "named_subst n (gi_to_book G ns k N) (gi_to_book G (n # ns) k M)"
  have redex: "\<Gamma> \<turnstile> ?X : \<tau>"
    by (rule has_type.App[OF has_type.Lam[OF body] argument])
  have reduct: "\<Gamma> \<turnstile> ?Y : \<tau>"
    by (rule subst0_preserves_typing[OF body argument])
  have argument_support: "named_fv (gi_to_book G ns k N) \<subseteq> set (n # ns)"
    using gi_to_book_fv_subset[OF rich argument chart] by auto
  have free: "named_free_for (gi_to_book G ns k N) n (gi_to_book G (n # ns) k M)"
    by (rule gi_translation_free_for[OF rich argument_support])
  have named_step: "named_beta_contract ?L ?R"
    unfolding gi_to_book.simps Let_def n_def
    by (rule named_beta_contract.beta; use free in \<open>simp only: n_def\<close>)
  have encoded_step: "sbeta_contract (named_to_source G [] ?L) (named_to_source G [] ?R)"
    by (rule named_beta_contract_encoding[OF named_step])
  have expanded_step: "sbeta_contract (gi_expand G k ?X) (gi_expand G k ?Y)"
    by (rule gi_expand_beta, rule beta_contract.beta)
  have renamed_step: "sbeta_contract
    (srename (\<lambda>i. ns ! i) (gi_expand G k ?X))
    (srename (\<lambda>i. ns ! i) (gi_expand G k ?Y))"
    by (rule srename_beta[OF expanded_step])
  have canonical_step: "sbeta_contract (named_to_source G [] ?L)
    (named_to_source G [] (gi_to_book G ns k ?Y))"
    using renamed_step
    by (simp only: gi_to_book_empty_encoding[OF rich redex chart distinct]
      gi_to_book_empty_encoding[OF rich reduct chart distinct])
  have same: "named_to_source G [] ?R = named_to_source G [] (gi_to_book G ns k ?Y)"
    by (rule gi_source_beta_deterministic[OF encoded_step canonical_step])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich same])
qed

text \<open>
  This is the actual named-substitution bridge at a typed β redex. The
  source free-for condition is discharged, not assumed away. Literal
  named_subst can capture in general; the chart-support argument excludes
  capture here. The conclusion is α-equivalence, not raw syntactic equality
  or an object-language identity theorem.
\<close>

end
