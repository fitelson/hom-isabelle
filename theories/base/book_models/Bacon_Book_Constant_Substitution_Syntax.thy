theory Bacon_Book_Constant_Substitution_Syntax
  imports Bacon_Book_Language
begin

section \<open>Literal replacement of a typed nonlogical constant\<close>

text \<open>
  A[B/cσ] replaces each occurrence of the nonlogical constant c:σ by
  B:σ. The replacement is permitted when no free variable of an inserted
  B becomes bound. Source: Bacon, Definition 5.2, p.99.

  Representation. The key is the pair (c,σ), not the name c alone.
  Replacement is single-pass: it does not recurse into B. Binders keep
  their names, so the total operation can capture variables. Its explicit
  free-for predicate forbids precisely the relevant binder captures.
  Typing and signature preservation alone do not establish that predicate.
  All results below are syntactic, over generic logical symbols and a
  partial logical signature Λ; no theory or interpretation is assumed.
\<close>

fun book_const_occurs :: "'c \<Rightarrow> otype \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_const_occurs c \<sigma> (NVar n) = False"
| "book_const_occurs c \<sigma> (NConst d \<tau>) = (d = c \<and> \<tau> = \<sigma>)"
| "book_const_occurs c \<sigma> (NLogical l) = False"
| "book_const_occurs c \<sigma> (NApp F A) = (book_const_occurs c \<sigma> F \<or> book_const_occurs c \<sigma> A)"
| "book_const_occurs c \<sigma> (NLam n A) = book_const_occurs c \<sigma> A"

fun book_const_subst ::
  "'c \<Rightarrow> otype \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_const_subst c \<sigma> B (NVar n) = NVar n"
| "book_const_subst c \<sigma> B (NConst d \<tau>) = (if d = c \<and> \<tau> = \<sigma> then B else NConst d \<tau>)"
| "book_const_subst c \<sigma> B (NLogical l) = NLogical l"
| "book_const_subst c \<sigma> B (NApp F A) = NApp (book_const_subst c \<sigma> B F) (book_const_subst c \<sigma> B A)"
| "book_const_subst c \<sigma> B (NLam n A) = NLam n (book_const_subst c \<sigma> B A)"

fun book_const_free_for ::
  "('c,'l) named_term \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_const_free_for B c \<sigma> (NVar n) = True"
| "book_const_free_for B c \<sigma> (NConst d \<tau>) = True"
| "book_const_free_for B c \<sigma> (NLogical l) = True"
| "book_const_free_for B c \<sigma> (NApp F A) = (book_const_free_for B c \<sigma> F \<and> book_const_free_for B c \<sigma> A)"
| "book_const_free_for B c \<sigma> (NLam n A) =
    (book_const_free_for B c \<sigma> A \<and> (book_const_occurs c \<sigma> A \<longrightarrow> n \<notin> named_fv B))"

lemma book_const_subst_absent:
  "\<not> book_const_occurs c \<sigma> A \<Longrightarrow> book_const_subst c \<sigma> B A = A"
  by (induction A) auto

lemma book_const_free_for_absent:
  "\<not> book_const_occurs c \<sigma> A \<Longrightarrow> book_const_free_for B c \<sigma> A"
  by (induction A) auto

lemma book_const_subst_type:
  assumes body: "has_ntype L G A \<tau>" and replacement: "has_ntype L G B \<sigma>"
  shows "has_ntype L G (book_const_subst c \<sigma> B A) \<tau>"
  using body
proof (induction A arbitrary: \<tau>)
  case (NVar n)
  show ?case by (simp only: book_const_subst.simps; rule NVar.prems)
next
  case (NConst d \<rho>)
  have result_type: "\<tau> = \<rho>" using NConst.prems by (simp only: named_const_type_iff)
  show ?case
  proof (cases "d = c \<and> \<rho> = \<sigma>")
    case True
    show ?thesis using replacement True result_type by simp
  next
    case False
    show ?thesis by (simp only: book_const_subst.simps False if_False; rule NConst.prems)
  qed
next
  case (NLogical l)
  show ?case by (simp only: book_const_subst.simps; rule NLogical.prems)
next
  case (NApp F A)
  obtain \<rho> where ft: "has_ntype L G F (Arr \<rho> \<tau>)" and at: "has_ntype L G A \<rho>"
    by (rule named_app_type_obtain[OF NApp.prems]; rule that; assumption)
  have fs: "has_ntype L G (book_const_subst c \<sigma> B F) (Arr \<rho> \<tau>)" by (rule NApp.IH(1)[OF ft])
  have asub: "has_ntype L G (book_const_subst c \<sigma> B A) \<rho>" by (rule NApp.IH(2)[OF at])
  show ?case unfolding book_const_subst.simps by (rule has_ntype.App[OF fs asub])
next
  case (NLam n A)
  obtain \<rho> where result_type: "\<tau> = Arr (G n) \<rho>" and at: "has_ntype L G A \<rho>"
    by (rule named_lam_type_obtain[OF NLam.prems]; rule that; assumption)
  have asub: "has_ntype L G (book_const_subst c \<sigma> B A) \<rho>" by (rule NLam.IH[OF at])
  show ?case unfolding book_const_subst.simps result_type by (rule has_ntype.Lam[OF asub])
qed

lemma book_const_subst_signature:
  assumes "named_in_signature \<Sigma> A" and "named_in_signature \<Sigma> B"
  shows "named_in_signature \<Sigma> (book_const_subst c \<sigma> B A)"
  using assms by (induction A) (auto split: if_splits)

lemma book_const_subst_logical_occurrences:
  "named_logical_occurrences (book_const_subst c \<sigma> B A) \<subseteq>
    named_logical_occurrences A \<union> named_logical_occurrences B"
  by (induction A) (auto split: if_splits)

theorem book_const_subst_language:
  assumes A: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and B: "book_in_language L \<Lambda> \<Sigma> G B \<sigma>"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_const_subst c \<sigma> B A) \<tau>"
proof -
  have typed: "has_ntype L G (book_const_subst c \<sigma> B A) \<tau>"
    by (rule book_const_subst_type[OF book_language_type[OF A] book_language_type[OF B]])
  have names: "named_in_signature \<Sigma> (book_const_subst c \<sigma> B A)"
    by (rule book_const_subst_signature[OF book_language_signature[OF A] book_language_signature[OF B]])
  have allowed: "named_logical_occurrences A \<union> named_logical_occurrences B \<subseteq> \<Lambda>"
    by (rule Un_least[OF book_language_logical_occurrences[OF A] book_language_logical_occurrences[OF B]])
  have logicals: "named_logical_occurrences (book_const_subst c \<sigma> B A) \<subseteq> \<Lambda>"
    by (rule subset_trans[OF book_const_subst_logical_occurrences allowed])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

lemma book_const_subst_fv_upper:
  "named_fv (book_const_subst c \<sigma> B A) \<subseteq> named_fv A \<union> named_fv B"
  by (induction A) (auto split: if_splits)

end
