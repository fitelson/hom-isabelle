theory Bacon_Book_Disjunction_Raw_Conversion_Transport
  imports Bacon_Book_Disjunction_Conversion_Transport Bacon_Book_Printed_Conversion_Correspondence
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Signature_Conservativity
begin

section \<open>Raw conversion is preserved by encoding\<close>

text \<open>
  A ≡βη B is transported from the primitive-∨ language to its
  primitive-∧ target language. Source: Bacon's β/η conversion conventions,
  pp.66–73, and the primitive extension in §5.2, p.104.

  A raw typed source conversion is first expressed as printed conversion
  over the universal source signature. Encoding sends it to the declared
  disjunction-tag signature over those source names. Forgetting that
  nonlogical-signature restriction gives a raw conjunction-language conversion.
  Richness is used by the checked printed/exact conversion adapter.
  The full logical alphabet of each side is retained; this does not
  identify primitive ∨ with a λ-defined operation.
  No theoremhood or model premise occurs.
\<close>

theorem book_disj_encode_raw_conversion:
  assumes rich: "sg_rich G"
    and conversion: "named_raw_beta_eta book_disj_logical_type G \<tau> A B"
  shows "named_raw_beta_eta book_conj_logical_type G \<tau> (book_disj_encode A) (book_disj_encode B)"
proof -
  have printed: "book_printed_conversion book_disj_logical_type UNIV (\<lambda>_. UNIV) G \<tau> A B"
    by (rule iffD1[OF book_raw_conversion_iff_printed[OF rich] conversion])
  have encoded: "book_printed_conversion book_conj_logical_type UNIV
    (book_disj_target_signature (\<lambda>_. UNIV)) G \<tau> (book_disj_encode A) (book_disj_encode B)"
    by (rule book_disj_encode_printed_conversion[OF printed])
  have named: "named_beta_eta_in_language book_conj_logical_type
    (book_disj_target_signature (\<lambda>_. UNIV)) G \<tau> (book_disj_encode A) (book_disj_encode B)"
    by (rule book_printed_conversion_named[OF encoded])
  show ?thesis by (rule named_conversion_to_raw[OF named])
qed

section \<open>Retraction into the exact target signature precedes decoding\<close>

text \<open>
  A raw conjunction-language conversion may pass through foreign
  constants, including a right-tag name at the wrong type. Such a chain must NOT be decoded
  directly. With typed endpoints in book_disj_target_signature Σ, first
  retract the entire conversion into that exact signature. Every node
  then admits the tag only at t→t→t.

  Convert this guarded chain to printed conversion, decode it using
  the checked per-node language transport, and only then pass to raw
  source conversion. The endpoint guards below are essential to this
  route. Fresh typed variables, not closed signature inhabitants,
  support the retraction. This is syntactic signature conservativity,
  not a proof about the fixed disjunction axioms, their consistency,
  or a model.
\<close>

theorem book_disj_decode_raw_conversion:
  assumes rich: "sg_rich G"
    and conversion: "named_raw_beta_eta book_conj_logical_type G \<tau> A B"
    and left: "book_in_language book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G A \<tau>"
    and right: "book_in_language book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G B \<tau>"
  shows "named_raw_beta_eta book_disj_logical_type G \<tau> (book_disj_decode A) (book_disj_decode B)"
proof -
  have guarded: "named_beta_eta_in_language book_conj_logical_type
    (book_disj_target_signature \<Sigma>) G \<tau> A B"
    by (rule named_raw_to_signature[OF rich conversion book_language_named[OF left] book_language_named[OF right]])
  have printed: "book_printed_conversion book_conj_logical_type UNIV
    (book_disj_target_signature \<Sigma>) G \<tau> A B"
    by (rule book_named_conversion_printed[OF rich guarded])
  have decoded: "book_printed_conversion book_disj_logical_type UNIV \<Sigma> G \<tau>
    (book_disj_decode A) (book_disj_decode B)"
    by (rule book_disj_decode_printed_conversion[OF printed])
  have named: "named_beta_eta_in_language book_disj_logical_type \<Sigma> G \<tau>
    (book_disj_decode A) (book_disj_decode B)"
    by (rule book_printed_conversion_named[OF decoded])
  show ?thesis by (rule named_conversion_to_raw[OF named])
qed

end
