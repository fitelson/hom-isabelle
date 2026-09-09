theory Bacon_Source_Relational_H_Typed_Constant_Map
  imports Bacon_Source_Relational_Typed_Constant_Map_Logical
begin

section \<open>Type-indexed constant transport through all ten H constructors\<close>

theorem paper_R_named_H_typed_constant_map:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "paper_R_named_H \<Omega> G (paper_R_typed_constant_map \<rho> A)"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case PC
  show ?case by (rule paper_R_named_H.PC[OF paper_R_typed_constant_map_PC[OF PC.hyps maps]])
next
  case UI
  show ?case
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
      rule paper_R_named_H.UI; use paper_R_typed_constant_map_language[OF UI.hyps maps]
        in \<open>simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps\<close>)
next
  case EG
  show ?case
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
      rule paper_R_named_H.EG; use paper_R_typed_constant_map_language[OF EG.hyps maps]
        in \<open>simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps\<close>)
next
  case Ref
  show ?case
    by (simp only: paper_R_typed_constant_map_primitive; rule paper_R_named_H.Ref;
      use paper_R_typed_constant_map_language[OF Ref.hyps maps] in \<open>simp only: paper_R_typed_constant_map_primitive\<close>)
next
  case LL
  show ?case
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
      rule paper_R_named_H.LL; use paper_R_typed_constant_map_language[OF LL.hyps maps]
        in \<open>simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps\<close>)
next
  case (Beta A B)
  have whole: "paper_R_in_language \<Omega> G
      (named_paper_iff G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)) Prop"
    using paper_R_typed_constant_map_language[OF Beta.hyps(4) maps] by (simp only: paper_R_typed_constant_map_iff)
  show ?case by (simp only: paper_R_typed_constant_map_iff; rule paper_R_named_H.Beta[OF
    paper_R_typed_constant_map_language[OF Beta.hyps(1) maps] paper_R_typed_constant_map_language[OF Beta.hyps(2) maps]
    paper_R_typed_constant_map_beta_step[OF Beta.hyps(3)] whole])
next
  case (Eta A B)
  have whole: "paper_R_in_language \<Omega> G
      (named_paper_iff G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)) Prop"
    using paper_R_typed_constant_map_language[OF Eta.hyps(4) maps] by (simp only: paper_R_typed_constant_map_iff)
  show ?case by (simp only: paper_R_typed_constant_map_iff; rule paper_R_named_H.Eta[OF
    paper_R_typed_constant_map_language[OF Eta.hyps(1) maps] paper_R_typed_constant_map_language[OF Eta.hyps(2) maps]
    paper_R_typed_constant_map_eta_step[OF Eta.hyps(3)] whole])
next
  case (MP A B)
  have implication: "paper_R_named_H \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B))"
    using MP.IH(2) by (simp only: paper_R_typed_constant_map_imp)
  show ?case by (rule paper_R_named_H.MP[OF MP.IH(1) implication paper_R_typed_constant_map_language[OF MP.hyps(3) maps]])
next
  case (Gen P Q n \<sigma>)
  have implication: "paper_R_named_H \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> P) (paper_R_typed_constant_map \<rho> Q))"
    using Gen.IH by (simp only: paper_R_typed_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_typed_constant_map \<rho> P)"
    by (simp only: paper_R_typed_constant_map_fv; rule Gen.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G (paper_R_typed_constant_map \<rho> P)
      (named_paper_all \<sigma> (NLam n (paper_R_typed_constant_map \<rho> Q)))) Prop"
    using paper_R_typed_constant_map_language[OF Gen.hyps(4) maps]
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps)
  show ?case by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
    rule paper_R_named_H.Gen[OF implication Gen.hyps(2) fresh whole])
next
  case (Inst P Q n \<sigma>)
  have implication: "paper_R_named_H \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> P) (paper_R_typed_constant_map \<rho> Q))"
    using Inst.IH by (simp only: paper_R_typed_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_typed_constant_map \<rho> Q)"
    by (simp only: paper_R_typed_constant_map_fv; rule Inst.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G
      (named_paper_ex \<sigma> (NLam n (paper_R_typed_constant_map \<rho> P))) (paper_R_typed_constant_map \<rho> Q)) Prop"
    using paper_R_typed_constant_map_language[OF Inst.hyps(4) maps]
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps)
  show ?case by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
    rule paper_R_named_H.Inst[OF implication Inst.hyps(2) fresh whole])
qed

text \<open>
  Every declared c:σ is sent to ρσ(c):σ in Ω. The proof is the
  native ten-constructor induction, with actual β/η step transport
  and unchanged eigenvariable conditions. No injectivity, inverse,
  richness, model, F calculus or consistency premise is needed.
  Source: Figure 2, p.8, and typed nonlogical signatures in §1.1.
\<close>

end
