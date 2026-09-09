theory Bacon_Source_Relational_H_Constant_Map
  imports Bacon_Source_Relational_Constant_Map_Logical
begin

section \<open>Forward carrier transport through all ten native R-H constructors\<close>

text \<open>
  If f sends every declared Σ-name of type ρ into Ωρ, a native
  Hᴿ proof maps to an Hᴿ proof in Ω. Source role: the original-name
  embedding in the Henkin expansion of Theorem 3.2, p.45 n.64.
  All ten Figure 2 constructors are preserved independently.

  Gen/Inst freshness is unchanged because FV is unchanged; β/η use
  the literal transported steps; PC retains its original template.
  This is only forward proof transport. No injection, richness, F
  theorem, model, consistency reflection or Henkin witness is assumed.
\<close>

theorem paper_R_named_H_constant_map:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "paper_R_named_H \<Omega> G (paper_R_constant_map f A)"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case PC
  show ?case by (rule paper_R_named_H.PC[OF paper_R_constant_map_PC[OF PC.hyps maps]])
next
  case UI
  show ?case
    by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps;
      rule paper_R_named_H.UI; use paper_R_constant_map_language[OF UI.hyps maps]
        in \<open>simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps\<close>)
next
  case EG
  show ?case
    by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps;
      rule paper_R_named_H.EG; use paper_R_constant_map_language[OF EG.hyps maps]
        in \<open>simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps\<close>)
next
  case Ref
  show ?case
    by (simp only: paper_R_constant_map_primitive; rule paper_R_named_H.Ref;
      use paper_R_constant_map_language[OF Ref.hyps maps] in \<open>simp only: paper_R_constant_map_primitive\<close>)
next
  case LL
  show ?case
    by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps;
      rule paper_R_named_H.LL; use paper_R_constant_map_language[OF LL.hyps maps]
        in \<open>simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps\<close>)
next
  case (Beta A B)
  have whole: "paper_R_in_language \<Omega> G
    (named_paper_iff G (paper_R_constant_map f A) (paper_R_constant_map f B)) Prop"
    using paper_R_constant_map_language[OF Beta.hyps(4) maps] by (simp only: paper_R_constant_map_iff)
  show ?case by (simp only: paper_R_constant_map_iff; rule paper_R_named_H.Beta[OF
    paper_R_constant_map_language[OF Beta.hyps(1) maps] paper_R_constant_map_language[OF Beta.hyps(2) maps]
    paper_R_constant_map_beta_step[OF Beta.hyps(3)] whole])
next
  case (Eta A B)
  have whole: "paper_R_in_language \<Omega> G
    (named_paper_iff G (paper_R_constant_map f A) (paper_R_constant_map f B)) Prop"
    using paper_R_constant_map_language[OF Eta.hyps(4) maps] by (simp only: paper_R_constant_map_iff)
  show ?case by (simp only: paper_R_constant_map_iff; rule paper_R_named_H.Eta[OF
    paper_R_constant_map_language[OF Eta.hyps(1) maps] paper_R_constant_map_language[OF Eta.hyps(2) maps]
    paper_R_constant_map_eta_step[OF Eta.hyps(3)] whole])
next
  case (MP A B)
  have implication: "paper_R_named_H \<Omega> G
    (named_paper_imp G (paper_R_constant_map f A) (paper_R_constant_map f B))"
    using MP.IH(2) by (simp only: paper_R_constant_map_imp)
  show ?case by (rule paper_R_named_H.MP[OF MP.IH(1) implication paper_R_constant_map_language[OF MP.hyps(3) maps]])
next
  case (Gen P Q n \<sigma>)
  have implication: "paper_R_named_H \<Omega> G
    (named_paper_imp G (paper_R_constant_map f P) (paper_R_constant_map f Q))"
    using Gen.IH by (simp only: paper_R_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_constant_map f P)" by (simp only: paper_R_constant_map_fv; rule Gen.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G (paper_R_constant_map f P)
      (named_paper_all \<sigma> (NLam n (paper_R_constant_map f Q)))) Prop"
    using paper_R_constant_map_language[OF Gen.hyps(4) maps]
    by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps)
  show ?case by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps;
    rule paper_R_named_H.Gen[OF implication Gen.hyps(2) fresh whole])
next
  case (Inst P Q n \<sigma>)
  have implication: "paper_R_named_H \<Omega> G
    (named_paper_imp G (paper_R_constant_map f P) (paper_R_constant_map f Q))"
    using Inst.IH by (simp only: paper_R_constant_map_imp)
  have fresh: "n \<notin> named_fv (paper_R_constant_map f Q)" by (simp only: paper_R_constant_map_fv; rule Inst.hyps(3))
  have whole: "paper_R_in_language \<Omega> G (named_paper_imp G
      (named_paper_ex \<sigma> (NLam n (paper_R_constant_map f P))) (paper_R_constant_map f Q)) Prop"
    using paper_R_constant_map_language[OF Inst.hyps(4) maps]
    by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps)
  show ?case by (simp only: paper_R_constant_map_imp paper_R_constant_map_primitive paper_R_constant_map_simps;
    rule paper_R_named_H.Inst[OF implication Inst.hyps(2) fresh whole])
qed

corollary paper_R_named_H_constant_map_into:
  assumes derivation: "paper_R_named_H \<Sigma> G A" and maps: "\<And>\<rho>. image f (\<Sigma> \<rho>) \<subseteq> \<Omega> \<rho>"
  shows "paper_R_named_H \<Omega> G (paper_R_constant_map f A)"
  by (rule paper_R_named_H_constant_map[OF derivation]; rule subsetD[OF maps]; rule imageI; assumption)

corollary paper_R_named_H_constant_map_image:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
  shows "paper_R_named_H (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (paper_R_constant_map f A)"
  by (rule paper_R_named_H_constant_map[OF derivation]; rule imageI; assumption)

end
