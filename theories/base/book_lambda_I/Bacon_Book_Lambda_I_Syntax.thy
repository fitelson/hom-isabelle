theory Bacon_Book_Lambda_I_Syntax
  imports Bacon_Book_Environment_Development.Bacon_Book_Full_General_Language
begin

section \<open>Bacon's relevant terms: the λI fragment\<close>

text \<open>
  Definition 9.2, p.192: constants and variables are relevant; MN is
  relevant when M and N are; λx.M is relevant when M is relevant and x
  occurs free in M. This is the λI restriction (no vacuous abstraction),
  the relevant language of Definition 9.3. The predicate is on raw named
  terms; the λI language at a type is the full typed language cut down by
  it. Logical constants count as constants.

  Every clause of Definition 9.1 (as transcribed in
  Bacon_Book_General_Lambda_Language) is proved below for this cut: the
  language contains every constant and variable, is closed under
  application and its inverse, under α-inclusive directed βη-reduction,
  under substitution of λI terms for variables and constants, and under
  relettering of free variables. The decisive facts are that a λI β-step
  never erases its argument, so free variables are preserved exactly, and
  that swapping and variable-for-variable substitution preserve occurrence.
\<close>

fun book_lambda_I :: "('c,'l) named_term \<Rightarrow> bool" where
  "book_lambda_I (NVar n) = True"
| "book_lambda_I (NConst c \<sigma>) = True"
| "book_lambda_I (NLogical l) = True"
| "book_lambda_I (NApp F A) = (book_lambda_I F \<and> book_lambda_I A)"
| "book_lambda_I (NLam n A) = (book_lambda_I A \<and> n \<in> named_fv A)"

definition book_lambda_I_terms ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'l set \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> ('c,'l) named_term set" where
  "book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau> = {A. book_in_language L \<Lambda> \<Sigma> G A \<tau> \<and> book_lambda_I A}"

lemma book_lambda_I_termsI:
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> book_lambda_I A \<Longrightarrow> A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
  unfolding book_lambda_I_terms_def by simp

lemma book_lambda_I_terms_language:
  "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau> \<Longrightarrow> book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  unfolding book_lambda_I_terms_def by simp

lemma book_lambda_I_terms_relevant:
  "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau> \<Longrightarrow> book_lambda_I A"
  unfolding book_lambda_I_terms_def by simp

subsection \<open>Properness\<close>

lemma book_lambda_I_identity_implication:
  "book_lambda_I (NLam n (NApp (NApp (NLogical l) (NVar n)) (NVar n)))"
  by simp

lemma book_lambda_I_vacuous_abstraction:
  assumes distinct: "m \<noteq> n"
  shows "\<not> book_lambda_I (NLam n (NVar m))"
  using distinct by simp

subsection \<open>Substitution\<close>

lemma book_lambda_I_subst:
  assumes al: "book_lambda_I A" and bl: "book_lambda_I B" and free_for: "named_free_for B x A"
  shows "book_lambda_I (named_subst x B A)"
  using al free_for
proof (induction A)
  case (NVar y)
  show ?case by (cases "y = x") (simp_all add: bl)
next
  case NConst
  show ?case by simp
next
  case NLogical
  show ?case by simp
next
  case (NApp F A)
  show ?case using NApp by simp
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis using NLam.prems(1) True by simp
  next
    case False
    have inner_relevant: "book_lambda_I A" and occurs: "y \<in> named_fv A" using NLam.prems(1) by simp_all
    have inner_free_for: "named_free_for B x A" using NLam.prems(2) False by simp
    have inner: "book_lambda_I (named_subst x B A)" by (rule NLam.IH[OF inner_relevant inner_free_for])
    have fv: "named_fv (named_subst x B A) =
      (named_fv A - {x}) \<union> (if x \<in> named_fv A then named_fv B else {})"
      by (rule named_subst_fv_exact[OF inner_free_for])
    have still: "y \<in> named_fv (named_subst x B A)" using occurs False by (simp add: fv)
    show ?thesis using False inner still by simp
  qed
qed

lemma book_lambda_I_beta_fv:
  assumes occurs: "x \<in> named_fv A" and free_for: "named_free_for B x A"
  shows "named_fv (named_subst x B A) = named_fv (NApp (NLam x A) B)"
  by (simp add: named_subst_fv_exact[OF free_for] occurs)

subsection \<open>Directed βη-reduction with α preserves relevance and free variables\<close>

lemma book_lambda_I_printed_beta_root:
  assumes step: "book_printed_beta_contract A B" and al: "book_lambda_I A"
  shows "book_lambda_I B \<and> named_fv B = named_fv A"
  using step al
proof (induction rule: book_printed_beta_contract.induct)
  case (beta N x M)
  have ml: "book_lambda_I M" and occurs: "x \<in> named_fv M" and nl: "book_lambda_I N"
    using beta.prems by simp_all
  have free_for: "named_free_for N x M" by (rule book_printed_free_for_named[OF beta.hyps])
  show ?case
    by (rule conjI[OF book_lambda_I_subst[OF ml nl free_for] book_lambda_I_beta_fv[OF occurs free_for]])
qed

lemma book_lambda_I_eta_root:
  assumes step: "named_eta_contract A B" and al: "book_lambda_I A"
  shows "book_lambda_I B \<and> named_fv B = named_fv A"
  using step al
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  show ?case using eta by auto
qed

lemma book_lambda_I_compatible_step:
  assumes atomic: "\<And>M N. R M N \<Longrightarrow> book_lambda_I M \<Longrightarrow> book_lambda_I N \<and> named_fv N = named_fv M"
    and step: "named_compatible_step R A B" and al: "book_lambda_I A"
  shows "book_lambda_I B \<and> named_fv B = named_fv A"
  using step al
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule atomic[OF root.hyps root.prems])
next
  case (App_left M M' N)
  show ?case using App_left by simp
next
  case (App_right N N' M)
  show ?case using App_right by simp
next
  case (Lam_body M M' n)
  show ?case using Lam_body by simp
qed

lemma book_lambda_I_swap:
  assumes al: "book_lambda_I A"
  shows "book_lambda_I (named_swap x y A)"
  using al by (induction A) (simp_all add: named_swap_fv)

lemma book_lambda_I_swap_iff:
  "book_lambda_I (named_swap x y A) \<longleftrightarrow> book_lambda_I A"
proof
  assume swapped: "book_lambda_I (named_swap x y A)"
  have "book_lambda_I (named_swap x y (named_swap x y A))" by (rule book_lambda_I_swap[OF swapped])
  then show "book_lambda_I A" by (simp only: named_swap_involution)
next
  assume al: "book_lambda_I A"
  show "book_lambda_I (named_swap x y A)" by (rule book_lambda_I_swap[OF al])
qed

lemma named_swap_index_image_member:
  "y \<in> named_swap_index x y ` S \<longleftrightarrow> x \<in> S"
  by (auto simp: named_swap_index_def image_iff split: if_splits)

lemma book_lambda_I_alpha_iff:
  assumes alpha: "named_alpha G A B"
  shows "book_lambda_I A \<longleftrightarrow> book_lambda_I B"
  using alpha
proof (induction rule: named_alpha.induct)
  case (Refl A)
  show ?case by (rule refl)
next
  case (Fresh_Binder x y A)
  show ?case by (simp add: book_lambda_I_swap_iff named_swap_fv named_swap_index_image_member)
next
  case (App F H A B)
  show ?case using App.IH by simp
next
  case (Lam A B n)
  have fv: "named_fv A = named_fv B" by (rule named_alpha_fv[OF Lam.hyps])
  show ?case using Lam.IH by (simp add: fv)
next
  case (Sym A B)
  show ?case using Sym.IH by (rule sym)
next
  case (Trans A B C)
  show ?case using Trans.IH by (rule trans)
qed

lemma book_lambda_I_alpha:
  assumes alpha: "named_alpha G A B" and al: "book_lambda_I A"
  shows "book_lambda_I B"
  using al by (simp only: book_lambda_I_alpha_iff[OF alpha])

lemma book_lambda_I_source_step:
  assumes step: "book_source_reduction_step G A B" and al: "book_lambda_I A"
  shows "book_lambda_I B"
  using step unfolding book_source_reduction_step_def
  by (blast intro: al conjunct1[OF book_lambda_I_compatible_step[OF book_lambda_I_printed_beta_root _ al]]
    conjunct1[OF book_lambda_I_compatible_step[OF book_lambda_I_eta_root _ al]] book_lambda_I_alpha[OF _ al])

theorem book_lambda_I_source_reduces:
  assumes reduction: "book_source_reduces G A B" and al: "book_lambda_I A"
  shows "book_lambda_I B"
proof -
  have chain: "rtranclp (book_source_reduction_step G) A B"
    using reduction unfolding book_source_reduces_def .
  show ?thesis
    using chain
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (rule al)
  next
    case (step y z)
    show ?case by (rule book_lambda_I_source_step[OF step.hyps(2) step.IH])
  qed
qed

subsection \<open>Constant and logical substitution\<close>

lemma book_const_subst_fv_lower:
  "named_fv A \<subseteq> named_fv (book_const_subst c \<sigma> B A)"
  by (induction A) auto

lemma book_lambda_I_const_subst:
  assumes al: "book_lambda_I A" and bl: "book_lambda_I B"
  shows "book_lambda_I (book_const_subst c \<sigma> B A)"
  using al
proof (induction A)
  case (NLam n A)
  have inner: "book_lambda_I A" and occurs: "n \<in> named_fv A" using NLam.prems by simp_all
  have kept: "n \<in> named_fv (book_const_subst c \<sigma> B A)" by (rule subsetD[OF book_const_subst_fv_lower occurs])
  show ?case using NLam.IH[OF inner] kept by simp
qed (simp_all add: bl)

lemma book_logical_subst_fv_lower:
  "named_fv A \<subseteq> named_fv (book_logical_subst l B A)"
  by (induction A) auto

lemma book_lambda_I_logical_subst:
  assumes al: "book_lambda_I A" and bl: "book_lambda_I B"
  shows "book_lambda_I (book_logical_subst l B A)"
  using al
proof (induction A)
  case (NLam n A)
  have inner: "book_lambda_I A" and occurs: "n \<in> named_fv A" using NLam.prems by simp_all
  have kept: "n \<in> named_fv (book_logical_subst l B A)" by (rule subsetD[OF book_logical_subst_fv_lower occurs])
  show ?case using NLam.IH[OF inner] kept by simp
qed (simp_all add: bl)

subsection \<open>Relettering of free variables\<close>

lemma book_lambda_I_simult_fv_keep:
  assumes absent: "map_of \<theta> (BSVar n (G n)) = None" and occurs: "n \<in> named_fv A"
  shows "n \<in> named_fv (book_simult_subst G \<theta> A)"
  using absent occurs
proof (induction A arbitrary: \<theta>)
  case (NVar m)
  have same: "m = n" using NVar.prems(2) by simp
  show ?case using NVar.prems(1) by (simp add: same)
next
  case (NLam m A)
  have distinct: "n \<noteq> m" and inner: "n \<in> named_fv A" using NLam.prems(2) by auto
  have absent': "map_of (book_subst_disable (BSVar m (G m)) \<theta>) (BSVar n (G n)) = None"
    using NLam.prems(1) distinct by (simp add: book_subst_lookup_disable)
  show ?case using NLam.IH[OF absent' inner] distinct by simp
qed auto

lemma book_lambda_I_simult_variables:
  assumes variables: "\<And>p. p \<in> set \<theta> \<Longrightarrow> \<exists>y. snd p = NVar y"
    and al: "book_lambda_I A"
  shows "book_lambda_I (book_simult_subst G \<theta> A)"
  using variables al
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case
  proof (cases "map_of \<theta> (BSVar n (G n))")
    case None
    then show ?thesis by simp
  next
    case (Some B)
    have member: "(BSVar n (G n), B) \<in> set \<theta>" by (rule map_of_SomeD[OF Some])
    obtain y where shape: "B = NVar y" using NVar.prems(1)[OF member] by auto
    show ?thesis by (simp add: Some shape)
  qed
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases "map_of \<theta> (BSConst c \<sigma>)")
    case None
    then show ?thesis by simp
  next
    case (Some B)
    have member: "(BSConst c \<sigma>, B) \<in> set \<theta>" by (rule map_of_SomeD[OF Some])
    obtain y where shape: "B = NVar y" using NConst.prems(1)[OF member] by auto
    show ?thesis by (simp add: Some shape)
  qed
next
  case NLogical
  show ?case by simp
next
  case (NApp F A)
  show ?case using NApp by simp
next
  case (NLam n A)
  have inner: "book_lambda_I A" and occurs: "n \<in> named_fv A" using NLam.prems(2) by simp_all
  have smaller: "\<And>p. p \<in> set (book_subst_disable (BSVar n (G n)) \<theta>) \<Longrightarrow> \<exists>y. snd p = NVar y"
    using NLam.prems(1) unfolding book_subst_disable_def by simp
  have kept: "n \<in> named_fv (book_simult_subst G (book_subst_disable (BSVar n (G n)) \<theta>) A)"
    by (rule book_lambda_I_simult_fv_keep[OF book_subst_disable_variable occurs])
  show ?case using NLam.IH[OF smaller inner] kept by simp
qed

lemma book_lambda_I_reletter:
  assumes al: "book_lambda_I A"
  shows "book_lambda_I (book_variable_reletter G xs ys A)"
  unfolding book_variable_reletter_def
proof (rule book_lambda_I_simult_variables[OF _ al])
  fix p
  assume member: "p \<in> set (book_variable_relettering_table G xs ys)"
  obtain a b where shape: "p = (a, b)" by (cases p)
  have "b \<in> set (map NVar ys)"
    using member unfolding book_variable_relettering_table_def shape by (rule set_zip_rightD)
  then show "\<exists>y. snd p = NVar y" unfolding shape by auto
qed

subsection \<open>The λI language satisfies Definition 9.1\<close>

theorem book_lambda_I_general_lambda_language:
  fixes L :: "'l \<Rightarrow> otype" and \<Sigma> :: "'c ssignature"
  shows "book_general_lambda_language L \<Lambda> \<Sigma> G (book_lambda_I_terms L \<Lambda> \<Sigma> G)"
proof unfold_locales
  fix A \<tau>
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
  show "book_in_language L \<Lambda> \<Sigma> G A \<tau>" by (rule book_lambda_I_terms_language[OF member])
next
  fix c \<tau>
  assume declared: "c \<in> \<Sigma> \<tau>"
  show "NConst c \<tau> \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI; simp add: book_language_const_iff declared)
next
  fix l
  assume present: "l \<in> \<Lambda>"
  show "NLogical l \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G (L l)"
    by (rule book_lambda_I_termsI[OF book_language_Logical[OF present]]) simp
next
  fix F A \<sigma> \<tau>
  assume head: "F \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<sigma>"
  show "NApp F A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_language_App[OF book_lambda_I_terms_language[OF head]
      book_lambda_I_terms_language[OF argument]]])
      (simp add: book_lambda_I_terms_relevant[OF head] book_lambda_I_terms_relevant[OF argument])
next
  fix F A \<sigma> \<tau>
  assume member: "NApp F A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and typed: "has_ntype L G F (Arr \<sigma> \<tau>)"
  show "F \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule book_lambda_I_termsI[OF book_full_application_head_language[OF
      book_lambda_I_terms_language[OF member] typed]])
      (use book_lambda_I_terms_relevant[OF member] in simp)
next
  fix F A \<sigma> \<tau>
  assume member: "NApp F A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and typed: "has_ntype L G A \<sigma>" and nonvariable: "\<not> (\<exists>n. A = NVar n)"
  show "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<sigma>"
    by (rule book_lambda_I_termsI[OF book_full_application_argument_language[OF
      book_lambda_I_terms_language[OF member] typed]])
      (use book_lambda_I_terms_relevant[OF member] in simp)
next
  fix A B \<tau>
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and reduction: "book_source_reduces G A B"
  show "B \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_source_reduces_language[OF reduction
      book_lambda_I_terms_language[OF member]]
      book_lambda_I_source_reduces[OF reduction book_lambda_I_terms_relevant[OF member]]])
next
  fix A B \<tau> n
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and replacement: "B \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G (G n)"
    and free_for: "book_printed_free_for B n A"
  show "named_subst n B A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_variable_subst_language[OF
      book_lambda_I_terms_language[OF member] book_lambda_I_terms_language[OF replacement]]
      book_lambda_I_subst[OF book_lambda_I_terms_relevant[OF member]
      book_lambda_I_terms_relevant[OF replacement] book_printed_free_for_named[OF free_for]]])
next
  fix A B \<tau> c \<sigma>
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and declared: "c \<in> \<Sigma> \<sigma>"
    and replacement: "B \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<sigma>"
    and free_for: "book_printed_free_for B 0 A"
  show "book_const_subst c \<sigma> B A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_const_subst_language[OF
      book_lambda_I_terms_language[OF member] book_lambda_I_terms_language[OF replacement]]
      book_lambda_I_const_subst[OF book_lambda_I_terms_relevant[OF member]
      book_lambda_I_terms_relevant[OF replacement]]])
next
  fix A B \<tau> l
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and present: "l \<in> \<Lambda>"
    and replacement: "B \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G (L l)"
    and free_for: "book_printed_free_for B 0 A"
  show "book_logical_subst l B A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_logical_subst_language[OF
      book_lambda_I_terms_language[OF member] book_lambda_I_terms_language[OF replacement]]
      book_lambda_I_logical_subst[OF book_lambda_I_terms_relevant[OF member]
      book_lambda_I_terms_relevant[OF replacement]]])
next
  fix A \<tau> xs ys
  assume member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and sources_distinct: "distinct xs" and targets_distinct: "distinct ys"
    and source_names: "set xs \<subseteq> named_fv A"
    and aligned: "list_all2 (\<lambda>x y. G x = G y) xs ys"
    and free_for: "\<And>x y. (x,y) \<in> set (zip xs ys) \<Longrightarrow> book_printed_free_for (NVar y) x A"
  show "book_variable_reletter G xs ys A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    by (rule book_lambda_I_termsI[OF book_variable_reletter_language[OF
      book_lambda_I_terms_language[OF member] aligned]
      book_lambda_I_reletter[OF book_lambda_I_terms_relevant[OF member]]])
qed

text \<open>
  The λI language is a general λ-language in the sense of Definition 9.1
  and it is proper: it omits every vacuous abstraction. Its α-variants,
  β/η-reducts, substitution instances and reletterings all stay inside it,
  which is what allows the full-language proof techniques to be reused
  for the λI calculus. No calculus, model or completeness claim is made
  in this leaf.
\<close>

end
