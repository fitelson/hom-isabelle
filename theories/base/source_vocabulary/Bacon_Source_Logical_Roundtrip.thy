theory Bacon_Source_Logical_Roundtrip
  imports Bacon_Source_Reverse_Syntax
begin

section \<open>Primitive logical constants survive the round trip up to η\<close>

text \<open>
  Translating a paper logical constant into its target wrapper and back
  yields an η expansion of that same constant.  Negation has one argument;
  conjunction, disjunction, and identity have two.  For ∀σ and ∃σ,
  first contract the inner predicate λx.Fx, then the outer λF abstraction.
  Source: Bacon--Dorr §1.1 and Figure 2's η axiom, pp.5–8.

  Isabelle representation.  Every step is in
  sbeta_eta_equiv_in_signature paper_logical_type Σ Γ and checks both
  endpoint types and signature membership.  The proofs use η only.
  Status.  All six primitive families are covered.  This does not identify
  target primitive implication with the paper's defined implication or
  assert any proof-reflection theorem.
\<close>

lemma paper_logical_unary_eta:
  fixes \<Sigma> :: "'c ssignature"
  assumes head: "paper_logical_type l = Arr \<sigma> \<tau>"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (Arr \<sigma> \<tau>)
    (SLam \<sigma> (SApp (SLogical l) (SVar 0))) (SLogical l)"
proof -
  let ?C = "SLogical l :: 'c paper_term"
  have target_type: "has_stype paper_logical_type \<Gamma> ?C (Arr \<sigma> \<tau>)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=l]
    by (simp only: head)
  have inner_head: "has_stype paper_logical_type (\<sigma> # \<Gamma>) ?C (Arr \<sigma> \<tau>)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>="\<sigma> # \<Gamma>" and l=l]
    by (simp only: head)
  have variable: "has_stype paper_logical_type (\<sigma> # \<Gamma>) (SVar 0 :: 'c paper_term) \<sigma>"
    by (rule has_stype.Var) simp
  have source_type: "has_stype paper_logical_type \<Gamma> (SLam \<sigma> (SApp ?C (SVar 0))) (Arr \<sigma> \<tau>)"
    by (rule has_stype.Lam[OF has_stype.App[OF inner_head variable]])
  have step: "scompatible_step seta_contract (SLam \<sigma> (SApp ?C (SVar 0))) ?C"
  proof -
    have "scompatible_step seta_contract (SLam \<sigma> (SApp (sshift ?C) (SVar 0))) ?C"
      by (rule scompatible_step.root[where R=seta_contract]) (rule seta_contract.eta)
    then show ?thesis by (simp add: sshift_def)
  qed
  show ?thesis by (rule sbeta_eta_equiv_in_signature.Eta[OF source_type target_type _ _ step]) simp_all
qed

lemma paper_logical_binary_eta:
  fixes \<Sigma> :: "'c ssignature"
  assumes head: "paper_logical_type l = Arr \<sigma> (Arr \<tau> \<rho>)"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (Arr \<sigma> (Arr \<tau> \<rho>))
    (SLam \<sigma> (SLam \<tau> (SApp (SApp (SLogical l) (SVar 1)) (SVar 0)))) (SLogical l)"
proof -
  let ?C = "SLogical l :: 'c paper_term"
  let ?S = "SLam \<sigma> (SLam \<tau> (SApp (SApp ?C (SVar 1)) (SVar 0)))"
  let ?M = "SLam \<sigma> (SApp ?C (SVar 0))"
  have inner_head: "has_stype paper_logical_type (\<tau> # \<sigma> # \<Gamma>) ?C (Arr \<sigma> (Arr \<tau> \<rho>))"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>="\<tau> # \<sigma> # \<Gamma>" and l=l]
    by (simp only: head)
  have first_var: "has_stype paper_logical_type (\<tau> # \<sigma> # \<Gamma>) (SVar 1 :: 'c paper_term) \<sigma>"
    by (rule has_stype.Var) simp
  have second_var: "has_stype paper_logical_type (\<tau> # \<sigma> # \<Gamma>) (SVar 0 :: 'c paper_term) \<tau>"
    by (rule has_stype.Var) simp
  have source_type: "has_stype paper_logical_type \<Gamma> ?S (Arr \<sigma> (Arr \<tau> \<rho>))"
    by (rule has_stype.Lam, rule has_stype.Lam,
      rule has_stype.App[OF has_stype.App[OF inner_head first_var] second_var])
  have outer_head: "has_stype paper_logical_type (\<sigma> # \<Gamma>) ?C (Arr \<sigma> (Arr \<tau> \<rho>))"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>="\<sigma> # \<Gamma>" and l=l]
    by (simp only: head)
  have variable: "has_stype paper_logical_type (\<sigma> # \<Gamma>) (SVar 0 :: 'c paper_term) \<sigma>"
    by (rule has_stype.Var) simp
  have middle_type: "has_stype paper_logical_type \<Gamma> ?M (Arr \<sigma> (Arr \<tau> \<rho>))"
    by (rule has_stype.Lam[OF has_stype.App[OF outer_head variable]])
  have inner_step: "scompatible_step seta_contract
    (SLam \<tau> (SApp (SApp ?C (SVar 1)) (SVar 0))) (SApp ?C (SVar 0))"
  proof -
    have "scompatible_step seta_contract
      (SLam \<tau> (SApp (sshift (SApp ?C (SVar 0))) (SVar 0))) (SApp ?C (SVar 0))"
      by (rule scompatible_step.root[where R=seta_contract]) (rule seta_contract.eta)
    then show ?thesis by (simp add: sshift_def)
  qed
  have step: "scompatible_step seta_contract ?S ?M"
    by (rule scompatible_step.Lam_body[OF inner_step])
  have first: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma>
    (Arr \<sigma> (Arr \<tau> \<rho>)) ?S ?M"
    by (rule sbeta_eta_equiv_in_signature.Eta[OF source_type middle_type _ _ step]) simp_all
  show ?thesis by (rule sbeta_eta_equiv_in_signature.Trans[OF first paper_logical_unary_eta[OF head]])
qed

lemma paper_logical_quantifier_eta:
  fixes \<Sigma> :: "'c ssignature"
  assumes head: "paper_logical_type l = Arr (Arr \<sigma> Prop) Prop"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (Arr (Arr \<sigma> Prop) Prop)
    (SLam (Arr \<sigma> Prop) (SApp (SLogical l) (SLam \<sigma> (SApp (SVar 1) (SVar 0)))))
    (SLogical l)"
proof -
  let ?R = "Arr \<sigma> Prop"
  let ?C = "SLogical l :: 'c paper_term"
  let ?S = "SLam ?R (SApp ?C (SLam \<sigma> (SApp (SVar 1) (SVar 0))))"
  let ?M = "SLam ?R (SApp ?C (SVar 0))"
  have logical_type: "has_stype paper_logical_type (?R # \<Gamma>) ?C (Arr ?R Prop)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>="?R # \<Gamma>" and l=l]
    by (simp only: head)
  have predicate: "has_stype paper_logical_type (\<sigma> # ?R # \<Gamma>) (SVar 1 :: 'c paper_term) ?R"
    by (rule has_stype.Var) simp
  have argument: "has_stype paper_logical_type (\<sigma> # ?R # \<Gamma>) (SVar 0 :: 'c paper_term) \<sigma>"
    by (rule has_stype.Var) simp
  have abstraction: "has_stype paper_logical_type (?R # \<Gamma>) (SLam \<sigma> (SApp (SVar 1) (SVar 0)) :: 'c paper_term) ?R"
    by (rule has_stype.Lam[OF has_stype.App[OF predicate argument]])
  have source_type: "has_stype paper_logical_type \<Gamma> ?S (Arr ?R Prop)"
    by (rule has_stype.Lam[OF has_stype.App[OF logical_type abstraction]])
  have variable: "has_stype paper_logical_type (?R # \<Gamma>) (SVar 0 :: 'c paper_term) ?R"
    by (rule has_stype.Var) simp
  have middle_type: "has_stype paper_logical_type \<Gamma> ?M (Arr ?R Prop)"
    by (rule has_stype.Lam[OF has_stype.App[OF logical_type variable]])
  have inner_step: "scompatible_step seta_contract
    (SLam \<sigma> (SApp (SVar 1) (SVar 0)) :: 'c paper_term) (SVar 0)"
  proof -
    have "scompatible_step seta_contract
      (SLam \<sigma> (SApp (sshift (SVar 0)) (SVar 0)) :: 'c paper_term) (SVar 0)"
      by (rule scompatible_step.root[where R=seta_contract]) (rule seta_contract.eta)
    then show ?thesis by (simp add: sshift_def)
  qed
  have step: "scompatible_step seta_contract ?S ?M"
    by (rule scompatible_step.Lam_body[OF scompatible_step.App_right[OF inner_step]])
  have first: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (Arr ?R Prop) ?S ?M"
    by (rule sbeta_eta_equiv_in_signature.Eta[OF source_type middle_type _ _ step]) simp_all
  show ?thesis by (rule sbeta_eta_equiv_in_signature.Trans[OF first paper_logical_unary_eta[OF head]])
qed

theorem paper_logical_roundtrip:
  "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> (paper_logical_type l)
    (pterm_to_paper (paper_logical_translation l)) (SLogical l)"
proof (cases l)
  case SNot
  have head: "paper_logical_type SNot = Arr Prop Prop" by simp
  show ?thesis using paper_logical_unary_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SNot paper_not_def)
next
  case SAnd
  have head: "paper_logical_type SAnd = Arr Prop (Arr Prop Prop)" by simp
  show ?thesis using paper_logical_binary_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SAnd paper_and_def)
next
  case SOr
  have head: "paper_logical_type SOr = Arr Prop (Arr Prop Prop)" by simp
  show ?thesis using paper_logical_binary_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SOr paper_or_def)
next
  case (SAll \<sigma>)
  have head: "paper_logical_type (SAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  show ?thesis using paper_logical_quantifier_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SAll)
next
  case (SEx \<sigma>)
  have head: "paper_logical_type (SEx \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  show ?thesis using paper_logical_quantifier_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SEx)
next
  case (SEq \<sigma>)
  have head: "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)" by simp
  show ?thesis using paper_logical_binary_eta[OF head, where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
    by (simp add: SEq)
qed

end
