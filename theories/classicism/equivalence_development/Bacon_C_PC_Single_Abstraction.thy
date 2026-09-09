theory Bacon_C_PC_Single_Abstraction
  imports Bacon_C_PC_Cofactors
begin

section \<open>The unconditional PC case beneath one abstraction\<close>

text \<open>
  If A is a propositional tautology and A:t in the context of v:σ,
  then ⊢C (λv.A) = (λv.⊤₀).
  Source: the single-variable instance of Bacon--Dorr Appendix A.2(i),
  p.65; the general abstraction vector remains a further step.

  Isabelle representation.  We prove the stronger restricted-validity
  statement: A is true for every propositional valuation assigning True
  to ObjTrue.  Induction measures |At(A) − {ObjTrue}|.  Shannon cofactors
  strictly decrease this measure, and both cofactors retain restricted
  validity.  The base case uses only the reflexive identity for ObjTrue.
  Status.  The proof derives C identities without atomic-constancy
  hypotheses, CE/CEV, necessitation, or a semantic completeness assumption.
\<close>

lemma C_PC_replace_measure_less:
  assumes selected: "p \<in> C_PC_atoms A - {ObjTrue}"
  shows "card (C_PC_atoms (C_PC_replace p b A) - {ObjTrue}) <
    card (C_PC_atoms A - {ObjTrue})"
proof -
  let ?S = "C_PC_atoms A - {ObjTrue}"
  let ?R = "C_PC_atoms (C_PC_replace p b A) - {ObjTrue}"
  have finite_S: "finite ?S" using C_PC_atoms_finite[of A] by simp
  have finite_delete: "finite (?S - {p})" using finite_S by simp
  have subset: "?R \<subseteq> ?S - {p}"
    using C_PC_replace_atoms[where p=p and b=b and A=A] by blast
  have bound: "card ?R \<le> card (?S - {p})" by (rule card_mono[OF finite_delete subset])
  have proper: "?S - {p} \<subset> ?S" using selected by blast
  have decrease: "card (?S - {p}) < card ?S"
    by (rule psubset_card_mono[OF finite_S proper])
  show ?thesis by (rule le_less_trans[OF bound decrease])
qed

theorem C_PC_restricted_valid_under_lambda:
  assumes typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and valid: "\<And>w. w ObjTrue \<Longrightarrow> prop_eval w A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> ObjTrue)"
  using typed valid
proof (induction A rule: measure_induct_rule[where f="\<lambda>A. card (C_PC_atoms A - {ObjTrue})"])
  case (less A)
  show ?case
  proof (cases "C_PC_atoms A - {ObjTrue} = {}")
    case True
    have atomic_identity: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
      \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant ((\<lambda>_. True) a)))"
    proof -
      fix a
      assume member: "a \<in> C_PC_atoms A"
      have atom_truth: "a = ObjTrue" using True member by blast
      show "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant ((\<lambda>_. True) a)))"
        using C_boolean_lambda_reflexive[OF typed_ObjTrue, where \<sigma>=\<sigma> and \<Gamma>=\<Gamma>]
        by (simp add: atom_truth C_boolean_constant_def)
    qed
    have evaluation: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> A) (Lam \<sigma> (C_boolean_constant (prop_eval (\<lambda>_. True) A)))"
      by (rule C_PC_evaluate_under_lambda[where w="\<lambda>_. True", OF less.prems(1) atomic_identity])
    have truth: "prop_eval (\<lambda>_. True) A"
      by (rule less.prems(2)[where w="\<lambda>_. True"]) simp
    show ?thesis using evaluation by (simp add: truth C_boolean_constant_def)
  next
    case False
    obtain p where selected: "p \<in> C_PC_atoms A - {ObjTrue}" using False by blast
    have member: "p \<in> C_PC_atoms A" using selected by simp
    have distinct: "p \<noteq> ObjTrue" using selected by simp
    have P: "\<sigma> # \<Gamma> \<turnstile> p : Prop"
      by (rule C_PC_atoms_typed[OF less.prems(1) member])
    have NP: "\<sigma> # \<Gamma> \<turnstile> Neg p : Prop" by (rule has_type.Neg[OF P])
    have cofactor: "\<And>b. \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (C_PC_replace p b A)) (Lam \<sigma> ObjTrue)"
    proof -
      fix b
      have smaller: "card (C_PC_atoms (C_PC_replace p b A) - {ObjTrue}) <
        card (C_PC_atoms A - {ObjTrue})"
        by (rule C_PC_replace_measure_less[OF selected])
      have cofactor_type: "\<sigma> # \<Gamma> \<turnstile> C_PC_replace p b A : Prop"
        by (rule C_PC_replace_type[OF less.prems(1)])
      have cofactor_valid: "\<And>w. w ObjTrue \<Longrightarrow> prop_eval w (C_PC_replace p b A)"
      proof -
        fix w
        assume truth: "w ObjTrue"
        have updated: "(w(p := b)) ObjTrue"
          by (rule C_PC_update_preserves_truth[where w=w and p=p and b=b, OF truth distinct])
        have evaluation: "prop_eval (w(p := b)) A"
          by (rule less.prems(2)[where w="w(p := b)", OF updated])
        show "prop_eval w (C_PC_replace p b A)"
          using C_PC_replace_eval[where w=w and p=p and b=b and A=A, OF truth] evaluation by simp
      qed
      show "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> (C_PC_replace p b A)) (Lam \<sigma> ObjTrue)"
        by (rule less.IH[OF smaller cofactor_type cofactor_valid])
    qed
    have positive: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj p (C_PC_replace p True A))) (Lam \<sigma> p)"
      by (rule C_A1_trans[OF C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF P]
        cofactor[of True]] C_boolean_lambda_conj_true_right[OF P]])
    have negative: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj (Neg p) (C_PC_replace p False A))) (Lam \<sigma> (Neg p))"
      by (rule C_A1_trans[OF C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF NP]
        cofactor[of False]] C_boolean_lambda_conj_true_right[OF NP]])
    have normalized: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Disj (Conj p (C_PC_replace p True A)) (Conj (Neg p) (C_PC_replace p False A))))
      (Lam \<sigma> (Disj p (Neg p)))"
      by (rule C_BA_disj_congruence[OF positive negative])
    show ?thesis by (rule C_A1_trans[OF C_PC_Shannon_expansion[OF P less.prems(1)]
      C_A1_trans[OF normalized C_boolean_lambda_excluded_middle_ObjTrue[OF P]]])
  qed
qed

corollary C_PC_single_abstraction:
  assumes tautology: "prop_tautology (\<sigma> # \<Gamma>) A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> ObjTrue)"
proof -
  have typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using tautology by (simp add: prop_tautology_def)
  have valid: "\<And>w. w ObjTrue \<Longrightarrow> prop_eval w A"
    using tautology unfolding prop_tautology_def by blast
  show ?thesis by (rule C_PC_restricted_valid_under_lambda[OF typed valid])
qed

text \<open>
  This completes the PC-to-truth identity for one abstraction.  It does
  not abstract an arbitrary open identity or an arbitrary C derivation.
  Extending the argument to an arbitrary abstraction vector, and proving
  the remaining axiom and rule cases of Appendix A.2, are still distinct
  tasks; C = CE = CEV is not claimed by this theorem alone.
\<close>

end
