theory Bacon_Book_Primitive_Conjunction_Encoding
  imports Bacon_Book_Primitive_Conjunction_Syntax
begin

section \<open>Encoding the primitive as a distinguished constant\<close>

text \<open>
  Encode ∧ by a distinguished constant k∧:t→t→t in the minimal
  language. Old nonlogical names c become Inl(c), and k∧ has name
  Inr(⋆). Minimal logical symbols remain logical symbols. Application
  and λ are preserved homomorphically; no λ-expression replaces ∧.
  Source role: preserving the primitive distinction of Bacon §5.2,
  p.104, while preparing a fixed-background-theory encoding.

  The target declares the tag ONLY at its designated type. Source and
  target have arbitrary old-name carrier 'c, with no countability or
  unused-name assumption. These are typing and language facts, not a
  proof that the conjunction schemas or model clauses hold.
\<close>

definition book_conj_target_signature :: "'c ssignature \<Rightarrow> ('c + unit) ssignature" where
  "book_conj_target_signature \<Sigma> \<tau> =
    image Inl (\<Sigma> \<tau>) \<union> (if \<tau> = book_conj_type then {Inr ()} else {})"

lemma book_conj_target_Inl_iff:
  "Inl c \<in> book_conj_target_signature \<Sigma> \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
  by (auto simp: book_conj_target_signature_def)

lemma book_conj_target_tag_iff:
  "Inr () \<in> book_conj_target_signature \<Sigma> \<tau> \<longleftrightarrow> \<tau> = book_conj_type"
  by (auto simp: book_conj_target_signature_def)

fun book_conj_encode :: "'c book_conj_term \<Rightarrow> ('c + unit) book_named_term" where
  "book_conj_encode (NVar n) = NVar n"
| "book_conj_encode (NConst c \<tau>) = NConst (Inl c) \<tau>"
| "book_conj_encode (NLogical l) =
    (case l of BCMinimal q \<Rightarrow> NLogical q | BCAnd \<Rightarrow> NConst (Inr ()) book_conj_type)"
| "book_conj_encode (NApp F A) = NApp (book_conj_encode F) (book_conj_encode A)"
| "book_conj_encode (NLam n A) = NLam n (book_conj_encode A)"

theorem book_conj_encode_type:
  assumes typed: "has_ntype book_conj_logical_type G A \<tau>"
  shows "has_ntype book_minimal_logical_type G (book_conj_encode A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: book_conj_encode.simps; rule has_ntype.Var)
next
  case (Const c \<tau>)
  show ?case by (simp only: book_conj_encode.simps; rule has_ntype.Const)
next
  case (Logical l)
  show ?case
  proof (cases l)
    case (BCMinimal q)
    show ?thesis by (simp only: BCMinimal book_conj_encode.simps book_conj_logical_type.simps
      book_conj_logical.simps; rule has_ntype.Logical)
  next
    case BCAnd
    show ?thesis by (simp only: BCAnd book_conj_encode.simps book_conj_logical_type.simps
      book_conj_logical.simps; rule has_ntype.Const)
  qed
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: book_conj_encode.simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: book_conj_encode.simps; rule has_ntype.Lam[OF Lam.IH])
qed

lemma book_conj_encode_fv:
  "named_fv (book_conj_encode A) = named_fv A"
  by (induction A) (simp_all split: book_conj_logical.splits)

lemma book_conj_encode_vars:
  "named_vars (book_conj_encode A) = named_vars A"
  by (induction A) (simp_all split: book_conj_logical.splits)

lemma book_conj_encode_signature:
  "named_in_signature (book_conj_target_signature \<Sigma>) (book_conj_encode A)
    \<longleftrightarrow> named_in_signature \<Sigma> A"
  by (induction A)
    (simp_all add: book_conj_target_Inl_iff book_conj_target_tag_iff split: book_conj_logical.splits)

theorem book_conj_encode_language:
  assumes language: "book_in_language book_conj_logical_type UNIV \<Sigma> G A \<tau>"
  shows "book_in_language book_minimal_logical_type UNIV
    (book_conj_target_signature \<Sigma>) G (book_conj_encode A) \<tau>"
proof -
  have typed: "has_ntype book_minimal_logical_type G (book_conj_encode A) \<tau>"
    by (rule book_conj_encode_type[OF book_language_type[OF language]])
  have names: "named_in_signature (book_conj_target_signature \<Sigma>) (book_conj_encode A)"
    by (rule iffD2[OF book_conj_encode_signature book_language_signature[OF language]])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] subset_UNIV])
qed

lemma book_conj_apply_encode:
  "book_conj_encode (book_conj_apply A B) =
    NApp (NApp (NConst (Inr ()) book_conj_type) (book_conj_encode A)) (book_conj_encode B)"
  by (simp add: book_conj_apply_def)

end
