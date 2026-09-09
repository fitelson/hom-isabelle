theory Bacon_Source_Relational_Classicism_Typed_Constant_Map
  imports Bacon_Source_Relational_H_Typed_Constant_Map
    Bacon_Source_Relational_Classicism_Presentation
begin

section \<open>Type-indexed constant transport through the five native C constructors\<close>

theorem paper_R_classicism_typed_constant_map:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "paper_R_classicism_proves \<Omega> G (paper_R_typed_constant_map \<rho> A)"
  using derivation
proof (induction rule: paper_R_classicism_proves.induct)
  case H
  show ?case by (rule paper_R_classicism_proves.H[OF paper_R_named_H_typed_constant_map[OF H.hyps maps]])
next
  case (Logical_Equivalence P Q ns)
  have certificate: "paper_R_named_H \<Omega> G
      (named_paper_iff G (paper_R_typed_constant_map \<rho> P) (paper_R_typed_constant_map \<rho> Q))"
    using paper_R_named_H_typed_constant_map[OF Logical_Equivalence.hyps(1) maps]
    by (simp only: paper_R_typed_constant_map_iff)
  show ?case by (simp only: paper_R_typed_constant_map_primitive paper_R_typed_constant_map_lam_vec;
    rule paper_R_classicism_proves.Logical_Equivalence[OF certificate
      paper_R_typed_constant_map_language[OF Logical_Equivalence.hyps(2) maps]
      paper_R_typed_constant_map_language[OF Logical_Equivalence.hyps(3) maps] Logical_Equivalence.hyps(4)])
next
  case (MP A B)
  have implication: "paper_R_classicism_proves \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B))"
    using MP.IH(2) by (simp only: paper_R_typed_constant_map_imp)
  show ?case by (rule paper_R_classicism_proves.MP[
    OF MP.IH(1) implication paper_R_typed_constant_map_language[OF MP.hyps(3) maps]])
next
  case (Gen P Q n \<sigma>)
  have implication: "paper_R_classicism_proves \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> P) (paper_R_typed_constant_map \<rho> Q))"
    using Gen.IH by (simp only: paper_R_typed_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_typed_constant_map \<rho> P)"
    by (simp only: paper_R_typed_constant_map_fv; rule Gen.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G (paper_R_typed_constant_map \<rho> P)
      (named_paper_all \<sigma> (NLam n (paper_R_typed_constant_map \<rho> Q)))) Prop"
    using paper_R_typed_constant_map_language[OF Gen.hyps(4) maps]
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps)
  show ?case by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
    rule paper_R_classicism_proves.Gen[OF implication Gen.hyps(2) fresh whole])
next
  case (Inst P Q n \<sigma>)
  have implication: "paper_R_classicism_proves \<Omega> G
      (named_paper_imp G (paper_R_typed_constant_map \<rho> P) (paper_R_typed_constant_map \<rho> Q))"
    using Inst.IH by (simp only: paper_R_typed_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_typed_constant_map \<rho> Q)"
    by (simp only: paper_R_typed_constant_map_fv; rule Inst.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G
      (named_paper_ex \<sigma> (NLam n (paper_R_typed_constant_map \<rho> P))) (paper_R_typed_constant_map \<rho> Q)) Prop"
    using paper_R_typed_constant_map_language[OF Inst.hyps(4) maps]
    by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps)
  show ?case by (simp only: paper_R_typed_constant_map_imp paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps;
    rule paper_R_classicism_proves.Inst[OF implication Inst.hyps(2) fresh whole])
qed

text \<open>
  Logical Equivalence is transported through its ORIGINAL H
  certificate, never through a recursively assumed C certificate.
  Its literal λ prefix and the stock G are unchanged. This is
  forward whole-proof preservation under a per-type declared-name
  map, not inverse reflection or compression of an infinite theory.
  Source: the p.12 definition of C and the Figure 2 H basis.
\<close>

end
