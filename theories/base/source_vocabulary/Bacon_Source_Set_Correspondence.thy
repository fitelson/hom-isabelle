theory Bacon_Source_Set_Correspondence
  imports Bacon_Source_Closed_Set_Preservation Bacon_Source_Local_Conversion_Transport
    Bacon_Source_Reverse_Set_Preservation
begin

section \<open>Replacing the round-trip image of each closed assumption\<close>

text \<open>
  Reverse translation first gives a proof from back(tr(S)). For each
  A ∈ S, the guarded source round trip identifies local derivability of
  back(tr(A)) and A. Local cut replaces those assumption leaves by their
  derivations from S. No injectivity of the syntax maps is assumed.

  Source role: preserving finite assumption/theorem/MP proofs over the
  arbitrary sentence sets of Bacon–Dorr Theorem 3.2. The set S itself
  need not be finite or countable.
\<close>

lemma paper_local_roundtrip_iff:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
  shows "paper_global_derivable \<Sigma> G S (pterm_to_paper (paper_to_pterm A))
    \<longleftrightarrow> paper_global_derivable \<Sigma> G S A"
proof -
  have conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> [] Prop
    (pterm_to_paper (paper_to_pterm A)) A" by (rule paper_roundtrip_conversion[OF language])
  have map: "G (id n) = \<rho>" if "lookup [] n = Some \<rho>" for n \<rho>
    using that by (simp add: lookup_def)
  show ?thesis using paper_global_derivable_conversion_iff[where G=G and r=id and S=S, OF conversion map]
    by (simp only: paper_reverse_srename_id)
qed

theorem paper_target_set_preimage:
  assumes sentences: "paper_sentence_set \<Sigma> S" and rich: "sg_rich G"
    and derivation: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) B"
  shows "paper_global_derivable \<Sigma> G S (pterm_to_paper B)"
proof -
  have restored: "paper_global_derivable \<Sigma> G
    (image pterm_to_paper (image paper_to_pterm S)) (pterm_to_paper B)"
    by (rule pH_closed_set_to_paper_global_derivable[OF derivation rich])
  show ?thesis
  proof (rule paper_global_derivable_cut[OF restored])
    fix C
    assume member: "C \<in> image pterm_to_paper (image paper_to_pterm S)"
    obtain A where source_member: "A \<in> S" and eq: "C = pterm_to_paper (paper_to_pterm A)"
      using member by auto
    have language: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
      by (rule paper_sentence_set_member[OF sentences source_member])
    have assumption: "paper_global_derivable \<Sigma> G S A"
      by (rule paper_global_derivable.Assumption[OF source_member paper_sentence_global_language[OF language]])
    have converted: "paper_global_derivable \<Sigma> G S (pterm_to_paper (paper_to_pterm A))"
      by (rule iffD2[OF paper_local_roundtrip_iff[OF language] assumption])
    show "paper_global_derivable \<Sigma> G S C" using converted by (simp only: eq)
  qed
qed

section \<open>Closed-set consequence agrees in source and target\<close>

text \<open>
  For a sentence set S and a sentence A of ℒ(Σ), source S ⊢H A
  iff target tr(S) ⊢H tr(A). The source stock G is rich; no bound on
  the cardinality of S or the declared nonlogical names is required.

  This is proof-theoretic consequence correspondence for the paper basis
  and full F types. It is not yet an equivalence of independently defined
  model classes, a named-variable/α identification, or a book-basis result.
\<close>

theorem paper_closed_set_derivable_iff:
  assumes sentences: "paper_sentence_set \<Sigma> S"
    and conclusion: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    and rich: "sg_rich G"
  shows "paper_global_derivable \<Sigma> G S A \<longleftrightarrow>
    pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
proof
  assume source: "paper_global_derivable \<Sigma> G S A"
  show "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
    by (rule paper_closed_set_preservation[OF sentences conclusion source])
next
  assume target: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
  have restored: "paper_global_derivable \<Sigma> G S (pterm_to_paper (paper_to_pterm A))"
    by (rule paper_target_set_preimage[OF sentences rich target])
  show "paper_global_derivable \<Sigma> G S A"
    by (rule iffD1[OF paper_local_roundtrip_iff[OF conclusion] restored])
qed

corollary paper_standard_closed_set_derivable_iff:
  assumes "paper_sentence_set \<Sigma> S"
    and "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
  shows "paper_global_derivable \<Sigma> sg_standard_stock S A \<longleftrightarrow>
    pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
  by (rule paper_closed_set_derivable_iff[OF assms sg_standard_stock_rich])

end
