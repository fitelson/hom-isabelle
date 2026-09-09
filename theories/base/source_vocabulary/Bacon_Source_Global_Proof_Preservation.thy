theory Bacon_Source_Global_Proof_Preservation
  imports Bacon_Source_Prefix_Quantifier_Rules Bacon_Source_Axiom_Guards
begin

section \<open>Whole source H proofs translate in sufficiently large finite prefixes\<close>

text \<open>
  A derivation of A in the fixed source variable stock G has a finite
  bound N such that, for every m ≥ N, target H proves the literal
  translation ⟦A⟧ in the frame [G(0),…,G(m−1)].  Source: Bacon–Dorr
  Figure 2, p.8, with the variable-stock convention of §1.1 and the
  available-variable qualification on pp.7–9.

  Isabelle representation.  The invariant paper_target_eventual retains
  every variable needed by the finite proof, not just variables occurring
  in its conclusion.  PC, MP, Gen, and Inst use their checked prefix
  wrappers.  UI, EG, Ref, and LL use the exact whole-formula language
  guards.  Each β/η case chooses a prefix covering both conversion
  endpoints before invoking the literal biconditional translation.

  Scope.  This is forward proof preservation for paper_global_H, with
  the paper's first-class logical basis and literal defined connectives.
  It applies to arbitrary nonlogical signatures and full F types.  Richness
  of the variable stock is not needed by the forward induction; intended
  source applications use the separately constructed rich stock.  No
  reverse proof translation, minimal-context theorem, named-variable/α
  correspondence, source consistency reflection, or source-model result
  is asserted here.
\<close>

lemma paper_target_eventual_Beta:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step sbeta_contract A B"
  shows "paper_target_eventual \<Sigma> G (paper_iff A B)"
  unfolding paper_target_eventual_def
proof (rule exI[where x="max (source_free_bound A) (source_free_bound B)"], intro allI impI)
  fix m
  assume bound: "max (source_free_bound A) (source_free_bound B) \<le> m"
  have boundA: "source_free_bound A \<le> m" and boundB: "source_free_bound B \<le> m"
    using bound by auto
  have finite_A: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G m) A Prop"
    by (rule source_language_in_prefix[OF A boundA])
  have finite_B: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G m) B Prop"
    by (rule source_language_in_prefix[OF B boundB])
  show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_iff A B))"
    by (rule paper_Beta_translation[OF finite_A finite_B step])
qed

lemma paper_target_eventual_Eta:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step seta_contract A B"
  shows "paper_target_eventual \<Sigma> G (paper_iff A B)"
  unfolding paper_target_eventual_def
proof (rule exI[where x="max (source_free_bound A) (source_free_bound B)"], intro allI impI)
  fix m
  assume bound: "max (source_free_bound A) (source_free_bound B) \<le> m"
  have boundA: "source_free_bound A \<le> m" and boundB: "source_free_bound B \<le> m"
    using bound by auto
  have finite_A: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G m) A Prop"
    by (rule source_language_in_prefix[OF A boundA])
  have finite_B: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G m) B Prop"
    by (rule source_language_in_prefix[OF B boundB])
  show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_iff A B))"
    by (rule paper_Eta_translation[OF finite_A finite_B step])
qed

theorem paper_global_H_target_eventual:
  assumes derivation: "paper_global_H \<Sigma> G A"
  shows "paper_target_eventual \<Sigma> G A"
  using derivation
proof (induction rule: paper_global_H.induct)
  case PC
  show ?case by (rule paper_target_eventual_PC[OF PC.hyps])
next
  case UI
  show ?case by (rule paper_target_eventual_from_axiom[OF UI.hyps])
    (rule paper_UI_guarded_translation, assumption)
next
  case EG
  show ?case by (rule paper_target_eventual_from_axiom[OF EG.hyps])
    (rule paper_EG_guarded_translation, assumption)
next
  case Ref
  show ?case by (rule paper_target_eventual_from_axiom[OF Ref.hyps])
    (rule paper_Ref_guarded_translation, assumption)
next
  case LL
  show ?case by (rule paper_target_eventual_from_axiom[OF LL.hyps])
    (rule paper_LL_guarded_translation, assumption)
next
  case Beta
  show ?case by (rule paper_target_eventual_Beta[OF Beta.hyps(1,2,3)])
next
  case Eta
  show ?case by (rule paper_target_eventual_Eta[OF Eta.hyps(1,2,3)])
next
  case MP
  show ?case by (rule paper_target_eventual_MP[OF MP.IH])
next
  case Gen
  show ?case by (rule paper_target_eventual_Gen[OF Gen.IH Gen.hyps(2,3)])
next
  case Inst
  show ?case by (rule paper_target_eventual_Inst[OF Inst.IH Inst.hyps(2,3)])
qed

corollary paper_global_H_target_finite_prefix:
  assumes derivation: "paper_global_H \<Sigma> G A"
  obtains m where "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
proof -
  have eventual: "paper_target_eventual \<Sigma> G A" by (rule paper_global_H_target_eventual[OF derivation])
  obtain N where bound: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    using eventual unfolding paper_target_eventual_def by (elim exE)
  have implication: "N \<le> N \<longrightarrow> pH_proves \<Sigma> (source_prefix G N) (paper_to_pterm A)"
    by (rule spec[where x=N, OF bound])
  have at_bound: "pH_proves \<Sigma> (source_prefix G N) (paper_to_pterm A)"
    by (rule mp[OF implication]) (rule order_refl)
  show thesis by (rule that[OF at_bound])
qed

end
