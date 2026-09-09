theory Bacon_Source_Named_Closed_Roundtrip
  imports Bacon_Source_Named_Decoder_Roundtrip Bacon_Source_Named_Alpha_Characterization
begin

section \<open>Closed named terms use the empty source frame\<close>

text \<open>
  If A:τ belongs to ℒ(Σ) and FV(A) = ∅, its encoding has type τ
  in the empty source context. Decoding that encoding under the empty
  chart gives an α-variant of A in a rich named stock.
  Source role: closed terms and named λ binding in Bacon–Dorr §1.1, p.5.

  Isabelle representation. Exact FV preservation makes the global-to-finite
  typing obligation vacuous. The already checked decoder round trip then
  gives encoding equality; generated α follows from its independent
  characterization. No source free-variable bound computation is needed.
  This is a syntax theorem, not a denotation or H proof correspondence.
\<close>

lemma named_to_source_closed_type:
  assumes typed: "has_ntype L G A \<tau>" and closed: "named_fv A = {}"
  shows "has_stype L [] (named_to_source G [] A) \<tau>"
proof -
  have global: "has_sgtype L G (named_to_source G [] A) \<tau>"
    by (rule named_to_source_empty_type[OF typed])
  have source_closed: "sfv (named_to_source G [] A) = {}"
    by (rule named_to_source_closed[OF closed])
  show ?thesis
  proof (rule source_global_to_finite_typing[OF global])
    fix n
    assume member: "n \<in> sfv (named_to_source G [] A)"
    have False using member by (simp add: source_closed)
    then show "lookup [] n = Some (G n)" by (rule FalseE)
  qed
qed

theorem named_to_source_closed_language:
  assumes language: "named_in_language L \<Sigma> G A \<tau>" and closed: "named_fv A = {}"
  shows "sterm_in_language L \<Sigma> [] (named_to_source G [] A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" and sig: "named_in_signature \<Sigma> A"
    using language unfolding named_in_language_def by blast+
  have source_type: "has_stype L [] (named_to_source G [] A) \<tau>"
    by (rule named_to_source_closed_type[OF typed closed])
  have source_sig: "sterm_in_signature \<Sigma> (named_to_source G [] A)"
    by (simp only: named_to_source_signature; rule sig)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF source_type source_sig])
qed

theorem named_closed_roundtrip_alpha:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
  shows "named_alpha G (source_to_named G [] (named_to_source G [] A)) A"
proof -
  have named_type: "has_ntype L G A \<tau>"
    using language unfolding named_in_language_def by (rule conjunct1)
  have source_type: "has_stype L [] (named_to_source G [] A) \<tau>"
    by (rule named_to_source_closed_type[OF named_type closed])
  have equality: "named_to_source G [] (source_to_named G [] (named_to_source G [] A)) = named_to_source G [] A"
    by (rule source_to_named_closed_roundtrip[OF source_type rich])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich equality])
qed

end
