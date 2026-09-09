theory Bacon_Source_Named_H_Correspondence
  imports Bacon_Source_Named_H_Reverse_PC Bacon_Source_Named_H_Reverse_Axioms
    Bacon_Source_Named_H_Reverse_Conversion Bacon_Source_Named_H_Reverse_Rules
begin

section \<open>Source-global proofs have named theorem representatives\<close>

text \<open>
  Induct over exactly the ten clauses of source-global H. Each axiom
  instance has a native named theorem preimage; the three inference rules
  reconstruct preimages from their induction hypotheses. The signature and
  rich variable stock stay unchanged. Source: Bacon–Dorr Figure 2, p.8.

  Equal encodings identify α-variants, not raw named strings. The derived
  native α theorem therefore transfers a constructed preimage to every
  named formula with that encoding. This closes syntactic theoremhood
  correspondence for open as well as closed formulas in the full F language.
  No soundness, completeness, or model assumption is used in this direction.
\<close>

theorem paper_named_H_preimage:
  assumes derivation: "paper_global_H \<Sigma> G M" and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = M"
  using derivation
proof (induction rule: paper_global_H.induct)
  case (PC A)
  show ?case by (rule paper_named_PC_preimage[OF PC.hyps rich])
next
  case (UI \<sigma> F A)
  show ?case by (rule paper_named_UI_preimage[OF UI.hyps rich])
next
  case (EG F A \<sigma>)
  show ?case by (rule paper_named_EG_preimage[OF EG.hyps rich])
next
  case (Ref \<sigma> A)
  show ?case by (rule paper_named_Ref_preimage[OF Ref.hyps rich])
next
  case (LL \<sigma> A B F)
  show ?case by (rule paper_named_LL_preimage[OF LL.hyps rich])
next
  case (Beta A B)
  show ?case by (rule paper_named_beta_preimage[OF Beta.hyps(1,2,3) rich])
next
  case (Eta A B)
  show ?case by (rule paper_named_eta_preimage[OF Eta.hyps(1,2,3) rich])
next
  case (MP A B)
  show ?case by (rule paper_named_MP_preimage[OF MP.IH rich])
next
  case (Gen P Q n \<sigma>)
  show ?case by (rule paper_named_Gen_preimage[OF Gen.IH Gen.hyps(2,3,4) rich])
next
  case (Inst P Q n \<sigma>)
  show ?case by (rule paper_named_Inst_preimage[OF Inst.IH Inst.hyps(2,3,4) rich])
qed

theorem paper_named_H_decoding:
  assumes derivation: "paper_global_H \<Sigma> G (named_to_source G [] A)" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G A"
proof -
  obtain N where theorem_N: "paper_named_H \<Sigma> G N"
    and same: "named_to_source G [] N = named_to_source G [] A"
    using paper_named_H_preimage[OF derivation rich] by (elim exE conjE)
  show ?thesis by (rule paper_named_H_same_encoding[OF theorem_N same rich])
qed

theorem paper_named_H_iff:
  assumes rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G A \<longleftrightarrow> paper_global_H \<Sigma> G (named_to_source G [] A)"
  by (rule iffI, rule paper_named_H_encoding[OF _ rich], assumption,
    rule paper_named_H_decoding[OF _ rich], assumption)

end
