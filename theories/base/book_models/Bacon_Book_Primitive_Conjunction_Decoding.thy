theory Bacon_Book_Primitive_Conjunction_Decoding
  imports Bacon_Book_Primitive_Conjunction_Encoding
begin

section \<open>Decoding the distinguished conjunction name\<close>

text \<open>
  The left name summand decodes to ordinary constants, the right tag
  decodes to primitive ∧, and minimal logical symbols decode through
  BCMinimal. This reverses the encoding on every source term.

  The decoder is total: even an incorrectly typed right-tag occurrence
  decodes to ∧. It follows that encoding after decoding is asserted ONLY
  for target terms in the declared target signature, which admits the
  right tag exclusively at t→t→t. Decoding typing and language preserve
  that same guard. No proof or model correspondence follows from these
  syntactic roundtrips alone (source role: Bacon §5.2, p.104).
\<close>

fun book_conj_decode :: "('c + unit) book_named_term \<Rightarrow> 'c book_conj_term" where
  "book_conj_decode (NVar n) = NVar n"
| "book_conj_decode (NConst c \<tau>) =
    (case c of Inl d \<Rightarrow> NConst d \<tau> | Inr u \<Rightarrow> NLogical BCAnd)"
| "book_conj_decode (NLogical l) = NLogical (BCMinimal l)"
| "book_conj_decode (NApp F A) = NApp (book_conj_decode F) (book_conj_decode A)"
| "book_conj_decode (NLam n A) = NLam n (book_conj_decode A)"

theorem book_conj_decode_encode:
  "book_conj_decode (book_conj_encode A) = A"
  by (induction A) (simp_all split: book_conj_logical.splits)

theorem book_conj_encode_decode:
  assumes names: "named_in_signature (book_conj_target_signature \<Sigma>) A"
  shows "book_conj_encode (book_conj_decode A) = A"
  using names
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases c)
    case (Inl d)
    show ?thesis by (simp add: Inl)
  next
    case (Inr u)
    have unit_value: "u = ()" by simp
    have declared: "Inr () \<in> book_conj_target_signature \<Sigma> \<sigma>"
      using NConst.prems by (simp only: named_in_signature.simps Inr unit_value)
    have correct_type: "\<sigma> = book_conj_type" by (rule iffD1[OF book_conj_target_tag_iff declared])
    show ?thesis by (simp add: Inr unit_value correct_type)
  qed
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fn: "named_in_signature (book_conj_target_signature \<Sigma>) F"
    and an: "named_in_signature (book_conj_target_signature \<Sigma>) A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_conj_decode.simps book_conj_encode.simps NApp.IH(1)[OF fn] NApp.IH(2)[OF an])
next
  case (NLam n A)
  have an: "named_in_signature (book_conj_target_signature \<Sigma>) A" using NLam.prems by simp
  show ?case by (simp only: book_conj_decode.simps book_conj_encode.simps NLam.IH[OF an])
qed

lemma book_conj_decode_fv:
  "named_fv (book_conj_decode A) = named_fv A"
  by (induction A) (simp_all split: sum.splits)

lemma book_conj_decode_signature:
  assumes names: "named_in_signature (book_conj_target_signature \<Sigma>) A"
  shows "named_in_signature \<Sigma> (book_conj_decode A)"
  using names by (induction A)
    (auto simp: book_conj_target_signature_def split: sum.splits if_splits)

theorem book_conj_decode_type:
  assumes typed: "has_ntype book_minimal_logical_type G A \<tau>"
    and names: "named_in_signature (book_conj_target_signature \<Sigma>) A"
  shows "has_ntype book_conj_logical_type G (book_conj_decode A) \<tau>"
  using typed names
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: book_conj_decode.simps; rule has_ntype.Var)
next
  case (Const c \<sigma>)
  show ?case
  proof (cases c)
    case (Inl d)
    show ?thesis by (simp add: Inl; rule has_ntype.Const)
  next
    case (Inr u)
    have unit_value: "u = ()" by simp
    have declared: "Inr () \<in> book_conj_target_signature \<Sigma> \<sigma>"
      using Const.prems by (simp only: named_in_signature.simps Inr unit_value)
    have correct_type: "\<sigma> = book_conj_type" by (rule iffD1[OF book_conj_target_tag_iff declared])
    show ?thesis by (simp add: Inr unit_value correct_type named_logical_type_iff)
  qed
next
  case (Logical l)
  show ?case by (simp add: named_logical_type_iff)
next
  case (App F \<sigma> \<tau> A)
  have fn: "named_in_signature (book_conj_target_signature \<Sigma>) F"
    and an: "named_in_signature (book_conj_target_signature \<Sigma>) A"
    using App.prems by simp_all
  have ft: "has_ntype book_conj_logical_type G (book_conj_decode F) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[OF fn])
  have at: "has_ntype book_conj_logical_type G (book_conj_decode A) \<sigma>"
    by (rule App.IH(2)[OF an])
  show ?case by (simp only: book_conj_decode.simps; rule has_ntype.App[OF ft at])
next
  case (Lam A \<tau> n)
  have an: "named_in_signature (book_conj_target_signature \<Sigma>) A" using Lam.prems by simp
  show ?case by (simp only: book_conj_decode.simps; rule has_ntype.Lam[OF Lam.IH[OF an]])
qed

theorem book_conj_decode_language:
  assumes language: "book_in_language book_minimal_logical_type UNIV
    (book_conj_target_signature \<Sigma>) G A \<tau>"
  shows "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode A) \<tau>"
proof -
  have names: "named_in_signature (book_conj_target_signature \<Sigma>) A"
    by (rule book_language_signature[OF language])
  have typed: "has_ntype book_conj_logical_type G (book_conj_decode A) \<tau>"
    by (rule book_conj_decode_type[OF book_language_type[OF language] names])
  have decoded_names: "named_in_signature \<Sigma> (book_conj_decode A)"
    by (rule book_conj_decode_signature[OF names])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed decoded_names] subset_UNIV])
qed

theorem book_conj_encode_language_iff:
  "book_in_language book_conj_logical_type UNIV \<Sigma> G A \<tau> \<longleftrightarrow>
    book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G (book_conj_encode A) \<tau>"
proof
  assume language: "book_in_language book_conj_logical_type UNIV \<Sigma> G A \<tau>"
  show "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G (book_conj_encode A) \<tau>"
    by (rule book_conj_encode_language[OF language])
next
  assume language: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G (book_conj_encode A) \<tau>"
  have decoded: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode (book_conj_encode A)) \<tau>"
    by (rule book_conj_decode_language[OF language])
  show "book_in_language book_conj_logical_type UNIV \<Sigma> G A \<tau>"
    using decoded by (simp only: book_conj_decode_encode)
qed

end
