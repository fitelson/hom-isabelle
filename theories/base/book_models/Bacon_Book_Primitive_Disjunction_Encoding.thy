theory Bacon_Book_Primitive_Disjunction_Encoding
  imports Bacon_Book_Primitive_Disjunction_Syntax
begin

section \<open>Encoding only the new primitive as a typed tag\<close>

text \<open>
  Encode ∨ by the distinguished constant k∨:t→t→t in the
  CONJUNCTION language. Old nonlogical names c become Inl(c);
  k∨ has the disjoint name Inr(⋆). Every prior logical symbol,
  including primitive ∧, remains a logical symbol in the target.
  Application and λ are preserved homomorphically.

  The target declares Inr(⋆) only at the designated type. These are
  syntax, typing and signature correspondences for the cumulative
  extension in Bacon §5.2, p.104. They assume neither countability,
  available unused old names, disjunction axioms, nor model truth.
  In particular, the tag is not a λ-defined disjunction.
\<close>

definition book_disj_target_signature :: "'c ssignature \<Rightarrow> ('c + unit) ssignature" where
  "book_disj_target_signature \<Sigma> \<tau> =
    image Inl (\<Sigma> \<tau>) \<union> (if \<tau> = book_disj_type then {Inr ()} else {})"

lemma book_disj_target_Inl_iff:
  "Inl c \<in> book_disj_target_signature \<Sigma> \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
  by (auto simp: book_disj_target_signature_def)

lemma book_disj_target_tag_iff:
  "Inr () \<in> book_disj_target_signature \<Sigma> \<tau> \<longleftrightarrow> \<tau> = book_disj_type"
  by (auto simp: book_disj_target_signature_def)

fun book_disj_encode :: "'c book_disj_term \<Rightarrow> ('c + unit) book_conj_term" where
  "book_disj_encode (NVar n) = NVar n"
| "book_disj_encode (NConst c \<tau>) = NConst (Inl c) \<tau>"
| "book_disj_encode (NLogical l) =
    (case l of BDConjunction q \<Rightarrow> NLogical q | BDOr \<Rightarrow> NConst (Inr ()) book_disj_type)"
| "book_disj_encode (NApp F A) = NApp (book_disj_encode F) (book_disj_encode A)"
| "book_disj_encode (NLam n A) = NLam n (book_disj_encode A)"

theorem book_disj_encode_type:
  assumes typed: "has_ntype book_disj_logical_type G A \<tau>"
  shows "has_ntype book_conj_logical_type G (book_disj_encode A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: book_disj_encode.simps; rule has_ntype.Var)
next
  case (Const c \<tau>)
  show ?case by (simp only: book_disj_encode.simps; rule has_ntype.Const)
next
  case (Logical l)
  show ?case
  proof (cases l)
    case (BDConjunction q)
    show ?thesis by (simp only: BDConjunction book_disj_encode.simps book_disj_logical_type.simps
      book_disj_logical.simps; rule has_ntype.Logical)
  next
    case BDOr
    show ?thesis by (simp only: BDOr book_disj_encode.simps book_disj_logical_type.simps
      book_disj_logical.simps; rule has_ntype.Const)
  qed
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: book_disj_encode.simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: book_disj_encode.simps; rule has_ntype.Lam[OF Lam.IH])
qed

lemma book_disj_encode_fv:
  "named_fv (book_disj_encode A) = named_fv A"
  by (induction A) (simp_all split: book_disj_logical.splits)

lemma book_disj_encode_vars:
  "named_vars (book_disj_encode A) = named_vars A"
  by (induction A) (simp_all split: book_disj_logical.splits)

lemma book_disj_encode_signature:
  "named_in_signature (book_disj_target_signature \<Sigma>) (book_disj_encode A)
    \<longleftrightarrow> named_in_signature \<Sigma> A"
  by (induction A)
    (simp_all add: book_disj_target_Inl_iff book_disj_target_tag_iff split: book_disj_logical.splits)

theorem book_disj_encode_language:
  assumes language: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<tau>"
  shows "book_in_language book_conj_logical_type UNIV
    (book_disj_target_signature \<Sigma>) G (book_disj_encode A) \<tau>"
proof -
  have typed: "has_ntype book_conj_logical_type G (book_disj_encode A) \<tau>"
    by (rule book_disj_encode_type[OF book_language_type[OF language]])
  have names: "named_in_signature (book_disj_target_signature \<Sigma>) (book_disj_encode A)"
    by (rule iffD2[OF book_disj_encode_signature book_language_signature[OF language]])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] subset_UNIV])
qed

lemma book_disj_apply_encode:
  "book_disj_encode (book_disj_apply A B) =
    NApp (NApp (NConst (Inr ()) book_disj_type) (book_disj_encode A)) (book_disj_encode B)"
  by (simp add: book_disj_apply_def)

end
