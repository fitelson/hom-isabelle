theory Bacon_Book_Logical_Substitution_Syntax
  imports Bacon_Book_Language
begin

section \<open>Literal replacement of a logical symbol\<close>

text \<open>
  A[B/l] replaces the logical symbol l by B:L(l), provided no free
  variable of an inserted B becomes bound. Source role: substitution
  for members of the WHOLE signature in Bacon, Definition 9.1, p.190.
  The logical/nonlogical split of this representation must not remove
  logical symbols from that syntactic closure requirement.

  Representation. Replacement is single-pass and leaves all binder names
  unchanged. It never recurses into B, even when B itself contains l.
  The total operation may capture variables; book_logical_free_for records
  the separate no-capture proviso. Type and language preservation do not
  require that proviso, since variable types are fixed by G.

  These are facts about full named syntax with explicit L, Λ and Σ.
  They prove neither substitution admissibility in H nor closure of an
  arbitrary admitted sublanguage. In particular they do not identify a
  primitive operator with a proposed definition.
\<close>

definition book_logical_occurs :: "'l \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_logical_occurs l A \<longleftrightarrow> l \<in> named_logical_occurrences A"

lemma book_logical_occurs_simps [simp]:
  "book_logical_occurs l (NVar n) = False"
  "book_logical_occurs l (NConst c \<sigma>) = False"
  "book_logical_occurs l (NLogical k) = (k = l)"
  "book_logical_occurs l (NApp F A) = (book_logical_occurs l F \<or> book_logical_occurs l A)"
  "book_logical_occurs l (NLam n A) = book_logical_occurs l A"
  by (auto simp: book_logical_occurs_def)

fun book_logical_subst ::
  "'l \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_logical_subst l B (NVar n) = NVar n"
| "book_logical_subst l B (NConst c \<sigma>) = NConst c \<sigma>"
| "book_logical_subst l B (NLogical k) = (if k = l then B else NLogical k)"
| "book_logical_subst l B (NApp F A) = NApp (book_logical_subst l B F) (book_logical_subst l B A)"
| "book_logical_subst l B (NLam n A) = NLam n (book_logical_subst l B A)"

fun book_logical_free_for ::
  "('c,'l) named_term \<Rightarrow> 'l \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_logical_free_for B l (NVar n) = True"
| "book_logical_free_for B l (NConst c \<sigma>) = True"
| "book_logical_free_for B l (NLogical k) = True"
| "book_logical_free_for B l (NApp F A) = (book_logical_free_for B l F \<and> book_logical_free_for B l A)"
| "book_logical_free_for B l (NLam n A) =
    (book_logical_free_for B l A \<and> (book_logical_occurs l A \<longrightarrow> n \<notin> named_fv B))"

lemma book_logical_subst_absent:
  "\<not> book_logical_occurs l A \<Longrightarrow> book_logical_subst l B A = A"
  by (induction A) auto

lemma book_logical_free_for_absent:
  "\<not> book_logical_occurs l A \<Longrightarrow> book_logical_free_for B l A"
  by (induction A) auto

lemma book_logical_free_for_closed:
  "named_fv B = {} \<Longrightarrow> book_logical_free_for B l A"
  by (induction A) auto

lemma book_logical_subst_type:
  assumes body: "has_ntype L G A \<tau>" and replacement: "has_ntype L G B (L l)"
  shows "has_ntype L G (book_logical_subst l B A) \<tau>"
  using body
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: book_logical_subst.simps; rule has_ntype.Var)
next
  case (Const c \<sigma>)
  show ?case by (simp only: book_logical_subst.simps; rule has_ntype.Const)
next
  case (Logical k)
  show ?case
  proof (cases "k = l")
    case True
    show ?thesis using replacement True by simp
  next
    case False
    show ?thesis by (simp only: book_logical_subst.simps False if_False; rule has_ntype.Logical)
  qed
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: book_logical_subst.simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: book_logical_subst.simps; rule has_ntype.Lam[OF Lam.IH])
qed

lemma book_logical_subst_signature:
  assumes "named_in_signature \<Sigma> A" and "named_in_signature \<Sigma> B"
  shows "named_in_signature \<Sigma> (book_logical_subst l B A)"
  using assms by (induction A) (auto split: if_splits)

lemma book_logical_subst_logical_occurrences:
  "named_logical_occurrences (book_logical_subst l B A) \<subseteq>
    (named_logical_occurrences A - {l}) \<union> named_logical_occurrences B"
  by (induction A) (auto split: if_splits)

theorem book_logical_subst_language:
  assumes A: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and B: "book_in_language L \<Lambda> \<Sigma> G B (L l)"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_logical_subst l B A) \<tau>"
proof -
  have typed: "has_ntype L G (book_logical_subst l B A) \<tau>"
    by (rule book_logical_subst_type[OF book_language_type[OF A] book_language_type[OF B]])
  have names: "named_in_signature \<Sigma> (book_logical_subst l B A)"
    by (rule book_logical_subst_signature[OF book_language_signature[OF A] book_language_signature[OF B]])
  have old_allowed: "named_logical_occurrences A - {l} \<subseteq> \<Lambda>"
    by (rule subset_trans[OF Diff_subset book_language_logical_occurrences[OF A]])
  have allowed: "(named_logical_occurrences A - {l}) \<union> named_logical_occurrences B \<subseteq> \<Lambda>"
    by (rule Un_least[OF old_allowed book_language_logical_occurrences[OF B]])
  have logicals: "named_logical_occurrences (book_logical_subst l B A) \<subseteq> \<Lambda>"
    by (rule subset_trans[OF book_logical_subst_logical_occurrences allowed])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

lemma book_logical_subst_fv_upper:
  "named_fv (book_logical_subst l B A) \<subseteq> named_fv A \<union> named_fv B"
  by (induction A) (auto split: if_splits)

end
