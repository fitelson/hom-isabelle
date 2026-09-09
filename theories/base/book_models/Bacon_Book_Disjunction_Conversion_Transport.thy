theory Bacon_Book_Disjunction_Conversion_Transport
  imports Bacon_Book_Disjunction_Step_Transport
begin

section \<open>Typed printed conversion across the primitive-disjunction encoding\<close>

text \<open>
  A ≡βη B is transported between the primitive-∨ language and its
  typed-tag encoding in the primitive-∧ language. Source: Bacon's
  conversion definitions, pp.66–73, and the extension in §5.2, p.104.

  Source conversion uses book_disj_logical_type and the old nonlogical
  signature Σ. Target conversion uses the conjunction logical basis and
  book_disj_target_signature Σ. Each target node is language guarded,
  so decoding never treats a wrongly typed disjunction tag as well typed.

  The proofs below preserve every Refl, printed β, η, Sym and Trans
  constructor of the independent conversion relation. No α rule, H
  derivation, model, or theorem about the disjunction axioms is assumed.
  Decoding is NOT asserted to preserve typing for an arbitrary raw
  conversion whose intermediate constants escape the target signature.
\<close>

theorem book_disj_encode_printed_conversion:
  assumes conversion: "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau> A B"
  shows "book_printed_conversion book_conj_logical_type UNIV
    (book_disj_target_signature \<Sigma>) G \<tau> (book_disj_encode A) (book_disj_encode B)"
  using conversion
proof (induction rule: book_printed_conversion.induct)
  case Refl
  show ?case by (rule book_printed_conversion.Refl[OF book_disj_encode_language[OF Refl.hyps]])
next
  case PrintedBeta
  show ?case by (rule book_printed_conversion.PrintedBeta[
    OF book_disj_encode_language[OF PrintedBeta.hyps(1)] book_disj_encode_language[OF PrintedBeta.hyps(2)]
      book_disj_encode_printed_beta_step[OF PrintedBeta.hyps(3)]])
next
  case Eta
  show ?case by (rule book_printed_conversion.Eta[
    OF book_disj_encode_language[OF Eta.hyps(1)] book_disj_encode_language[OF Eta.hyps(2)]
      book_disj_encode_eta_step[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule book_printed_conversion.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule book_printed_conversion.Trans[OF Trans.IH])
qed

theorem book_disj_decode_printed_conversion:
  assumes conversion: "book_printed_conversion book_conj_logical_type UNIV
    (book_disj_target_signature \<Sigma>) G \<tau> A B"
  shows "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau>
    (book_disj_decode A) (book_disj_decode B)"
  using conversion
proof (induction rule: book_printed_conversion.induct)
  case Refl
  show ?case by (rule book_printed_conversion.Refl[OF book_disj_decode_language[OF Refl.hyps]])
next
  case PrintedBeta
  show ?case by (rule book_printed_conversion.PrintedBeta[
    OF book_disj_decode_language[OF PrintedBeta.hyps(1)] book_disj_decode_language[OF PrintedBeta.hyps(2)]
      book_disj_decode_printed_beta_step[OF PrintedBeta.hyps(3)]])
next
  case Eta
  show ?case by (rule book_printed_conversion.Eta[
    OF book_disj_decode_language[OF Eta.hyps(1)] book_disj_decode_language[OF Eta.hyps(2)]
      book_disj_decode_eta_step[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule book_printed_conversion.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule book_printed_conversion.Trans[OF Trans.IH])
qed

corollary book_disj_printed_conversion_iff:
  "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau> A B \<longleftrightarrow>
    book_printed_conversion book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G \<tau>
      (book_disj_encode A) (book_disj_encode B)"
proof
  assume source: "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau> A B"
  show "book_printed_conversion book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G \<tau>
      (book_disj_encode A) (book_disj_encode B)"
    by (rule book_disj_encode_printed_conversion[OF source])
next
  assume target: "book_printed_conversion book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G \<tau>
      (book_disj_encode A) (book_disj_encode B)"
  have decoded: "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau>
      (book_disj_decode (book_disj_encode A)) (book_disj_decode (book_disj_encode B))"
    by (rule book_disj_decode_printed_conversion[OF target])
  show "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau> A B"
    using decoded by (simp only: book_disj_decode_encode)
qed

end
