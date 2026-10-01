theory Typed_Paper_Translation
  imports Typed_Source_Model
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Syntax"
begin

section \<open>The six paper primitives as declared book constants\<close>

definition pt_signature :: "'c ssignature \<Rightarrow> ('c + paper_logical) ssignature" where
  "pt_signature S a = Inl ` S a \<union> {Inr l |l. paper_logical_type l = a}"

primrec pt_term :: "'c paper_named_term \<Rightarrow> ('c + paper_logical, book_minimal_logical) named_term" where
  "pt_term (NVar n) = NVar n"
| "pt_term (NConst c a) = NConst (Inl c) a"
| "pt_term (NLogical l) = NConst (Inr l) (paper_logical_type l)"
| "pt_term (NApp F A) = NApp (pt_term F) (pt_term A)"
| "pt_term (NLam n A) = NLam n (pt_term A)"

lemma pt_signature_old [simp]: "Inl c \<in> pt_signature S a \<longleftrightarrow> c \<in> S a"
  by (auto simp: pt_signature_def)

lemma pt_signature_logical [simp]:
  "Inr l \<in> pt_signature S a \<longleftrightarrow> paper_logical_type l = a"
  by (auto simp: pt_signature_def)

lemma pt_term_type:
  assumes "has_ntype paper_logical_type G A a"
  shows "has_ntype book_minimal_logical_type G (pt_term A) a"
  using assms
  by (induction rule: has_ntype.induct) (auto intro: has_ntype.intros)

lemma pt_term_signature:
  "named_in_signature (pt_signature S) (pt_term A) = named_in_signature S A"
  by (induction A) simp_all

lemma pt_term_logical_occurrences:
  "named_logical_occurrences (pt_term A) = {}"
  by (induction A) simp_all

lemma pt_term_fv [simp]: "named_fv (pt_term A) = named_fv A"
  by (induction A) simp_all

theorem pt_language:
  assumes "named_in_language paper_logical_type S G A a"
  shows "book_in_language book_minimal_logical_type UNIV (pt_signature S) G (pt_term A) a"
  using assms pt_term_type[where G=G and A=A and a=a]
  by (auto simp: book_in_language_def named_in_language_def pt_term_signature)

theorem pt_R_language:
  assumes "paper_R_in_language S G A a"
  shows "book_in_language book_minimal_logical_type UNIV (pt_signature S) G (pt_term A) a"
  by (rule pt_language, rule paper_R_language_embedding[OF assms])

text \<open>This translation does not identify the primitive bases.
  Each paper primitive becomes a declared nonlogical book constant at its
  original full type. Variables, applications, abstractions, and free
  variables are preserved literally. A semantic bridge must subsequently
  assign those constants their independently defined six primitive graphs
  and compare the two interpretations. No semantic conclusion is claimed
  by the language translation alone.\<close>

end
