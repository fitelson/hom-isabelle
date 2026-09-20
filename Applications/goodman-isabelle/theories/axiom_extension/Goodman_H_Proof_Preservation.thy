theory Goodman_H_Proof_Preservation
  imports Goodman_H_Identity_Rules Goodman_H_Propositional_Rule Goodman_H_Quantifier_Rules
begin

section \<open>Whole-proof preservation, first in the universal target signature\<close>

text \<open>
  Every constructor of H_proves is handled by induction. We first declare
  every target constant, so intermediate formulas may mention names absent
  from the final formula. The theorem below then removes these foreign
  constants using the core's PROVED signature-conservativity theorem.
\<close>

theorem gi_H_universal_preservation:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> \<turnstile>\<^sub>H A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "book_H (\<lambda>_. UNIV) G (gi_to_book G ns k A)"
  using derivation chart distinct
proof (induction arbitrary: ns rule: H_proves.induct)
  case PC
  show ?case by (rule gi_H_PC[OF rich PC.hyps PC.prems(1) gi_constants_universal])
next
  case IndividualExistence
  show ?case by (rule gi_H_IndividualExistence[OF rich])
next
  case UI
  show ?case by (rule gi_H_UI[OF rich UI.hyps UI.prems gi_constants_universal gi_constants_universal])
next
  case EG
  show ?case by (rule gi_H_EG[OF rich EG.hyps EG.prems gi_constants_universal gi_constants_universal])
next
  case Ref
  show ?case by (rule gi_H_Ref[OF rich Ref.hyps Ref.prems(1) gi_constants_universal])
next
  case LL
  show ?case by (rule gi_H_LL[OF rich LL.hyps LL.prems(1)
    gi_constants_universal gi_constants_universal gi_constants_universal])
next
  case Beta
  show ?case by (rule gi_H_beta_schema[OF rich Beta.hyps(3) Beta.hyps(1,2) Beta.prems
    gi_constants_universal gi_constants_universal])
next
  case Eta
  show ?case by (rule gi_H_eta_schema[OF rich Eta.hyps(3) Eta.hyps(1,2) Eta.prems
    gi_constants_universal gi_constants_universal])
next
  case (MP \<Gamma> A B)
  have bt: "\<Gamma> \<turnstile> B : Prop" by (rule H_proves_formula, rule H_proves.MP[OF MP.hyps])
  have first: "book_H (\<lambda>_. UNIV) G (gi_to_book G ns k A)" by (rule MP.IH(1)[OF MP.prems])
  have second: "book_H (\<lambda>_. UNIV) G (gi_to_book G ns k (Imp A B))" by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule gi_H_MP[OF rich bt MP.prems(1) gi_constants_universal first second])
next
  case (Gen \<Gamma> P \<sigma> Q)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Gen.prems(1)])
  have distinct: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Gen.prems(2)])
  have premise: "book_H (\<lambda>_. UNIV) G (gi_to_book G (?n # ns) k (Imp (shift P) Q))"
    by (rule Gen.IH[OF extended distinct])
  show ?case by (rule gi_H_Gen[OF rich Gen.hyps(1,2) Gen.prems
    gi_constants_universal gi_constants_universal premise])
next
  case (Inst \<sigma> \<Gamma> P Q)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Inst.prems(1)])
  have distinct: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Inst.prems(2)])
  have premise: "book_H (\<lambda>_. UNIV) G (gi_to_book G (?n # ns) k (Imp P (shift Q)))"
    by (rule Inst.IH[OF extended distinct])
  show ?case by (rule gi_H_Inst[OF rich Inst.hyps(1,2) Inst.prems
    gi_constants_universal gi_constants_universal premise])
qed

section \<open>Remove proof-only constants and recover the requested signature\<close>

theorem gi_H_preservation:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> \<turnstile>\<^sub>H A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants: "gi_constants_admitted k \<Sigma> A"
  shows "book_H \<Sigma> G (gi_to_book G ns k A)"
proof -
  have universal: "book_H (\<lambda>_. UNIV) G (gi_to_book G ns k A)"
    by (rule gi_H_universal_preservation[OF rich derivation chart distinct])
  have raw: "book_theory_derivable (\<lambda>_. UNIV) G {} (gi_to_book G ns k A)"
    using universal by (simp only: book_H_iff_theory[OF rich])
  have formula: "\<Gamma> \<turnstile> A : Prop" by (rule H_proves_formula[OF derivation])
  have language: "book_theory_formula \<Sigma> G (gi_to_book G ns k A)"
    by (rule gi_to_book_language[OF rich formula chart constants])
  have target_names: "named_in_signature \<Sigma> (gi_to_book G ns k A)"
    by (rule book_language_signature[OF language])
  have restricted: "book_theory_derivable \<Sigma> G {} (gi_to_book G ns k A)"
    by (rule book_theory_foreign_constants_eliminate[OF rich raw target_names]; simp)
  show ?thesis using restricted by (simp only: book_H_iff_theory[OF rich])
qed

corollary gi_H_closed_preservation:
  "sg_rich G \<Longrightarrow> [] \<turnstile>\<^sub>H A \<Longrightarrow> gi_constants_admitted k \<Sigma> A \<Longrightarrow>
    book_H \<Sigma> G (gi_to_book G [] k A)"
  by (rule gi_H_preservation; (assumption | simp))

text \<open>
  The final theorem requires only the CONCLUSION's constant-signature
  guard. Intermediate proof formulas are not assumed to stay in that
  signature. This is forward preservation of the represented constructor
  H into full-F/minimal book H, not reflection, an identification with
  the paper's R language, or preservation of CEV+ extensions.
\<close>

end
