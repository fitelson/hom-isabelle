theory Bacon_Source_Proof_Correspondence
  imports Bacon_Source_Closed_Proof_Preservation Bacon_Source_Reverse_Proof_Preservation
    Bacon_Source_Roundtrip Bacon_Source_Global_Conversion_Transport
begin

section \<open>Closed-sentence theoremhood agrees in source H and target H\<close>

text \<open>
  A closed paper-language sentence A is provable in the fixed rich source
  stock exactly when its translation is provable in target H with empty
  variable context. The nonlogical signature Σ is unchanged.
  Source: Bacon–Dorr §1.1 and Figure 2, pp.5–8.

  Forward preservation retains all variables needed by the source proof
  before eliminating the unused target context. Reverse preservation
  reconstructs the actual source axioms and rules, using derived source
  Existence for the target's explicit existence clause. The source round
  trip is then removed by the checked contextual-conversion theorem.

  Scope: closed-sentence theoremhood for the paper's first-class primitive
  basis and literal defined connectives, full F types, and arbitrary
  nonlogical signatures/name carriers. G must be rich; the following
  corollary supplies the independently constructed standard stock.
  This does not yet identify a separate named-variable/α syntax, the
  book's minimal primitive basis, or independently defined model classes.
\<close>

theorem paper_global_H_closed_iff:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    and rich: "sg_rich G"
  shows "paper_global_H \<Sigma> G A \<longleftrightarrow> pH_proves \<Sigma> [] (paper_to_pterm A)"
proof
  assume source: "paper_global_H \<Sigma> G A"
  have typed: "has_stype paper_logical_type [] A Prop"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have bounded: "sfv A \<subseteq> {..<length ([] :: ctx)}"
    by (rule source_typed_fv_bound[OF typed])
  have closed: "sfv A = {}" using bounded by auto
  show "pH_proves \<Sigma> [] (paper_to_pterm A)"
    by (rule paper_global_H_closed_preservation[OF source closed])
next
  assume target: "pH_proves \<Sigma> [] (paper_to_pterm A)"
  have restored_proof: "paper_global_H \<Sigma> G (pterm_to_paper (paper_to_pterm A))"
    by (rule pH_closed_to_paper_global_H[OF target rich])
  have conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> [] Prop
    (pterm_to_paper (paper_to_pterm A)) A"
    by (rule paper_roundtrip_conversion[OF language])
  have typed_map: "G (id n) = \<rho>" if "lookup [] n = Some \<rho>" for n \<rho>
    using that by (simp add: lookup_def)
  have correspondence: "paper_global_H \<Sigma> G (pterm_to_paper (paper_to_pterm A))
    \<longleftrightarrow> paper_global_H \<Sigma> G A"
    using paper_global_H_conversion_iff[where G=G and r=id, OF conversion typed_map]
    by (simp only: paper_reverse_srename_id)
  show "paper_global_H \<Sigma> G A" by (rule iffD1[OF correspondence restored_proof])
qed

corollary paper_standard_H_closed_iff:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
  shows "paper_global_H \<Sigma> sg_standard_stock A \<longleftrightarrow>
    pH_proves \<Sigma> [] (paper_to_pterm A)"
  by (rule paper_global_H_closed_iff[OF language sg_standard_stock_rich])

end
