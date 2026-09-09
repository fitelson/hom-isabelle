theory Bacon_Source_Axiom_Guards
  imports Bacon_Source_Conversion_Axioms
begin

section \<open>Recovering axiom operands from the literal whole-formula guard\<close>

text \<open>
  Figure 2's UI, EG, Ref, and LL instances are formulas in ℒ(Σ).
  Their fixed logical-symbol types determine the types of the schematic
  operands: F:σ → t and A:σ for UI/EG; A:σ for Ref; and
  A,B:σ and F:σ → t for LL.  Signature membership is inherited by
  every displayed operand.

  Isabelle representation.  We invert has_stype applications and use
  source_typing_unique, retaining the literal paper_imp definitions.
  The final translation theorems assume only sterm_in_language for
  the entire axiom, matching the finite-frame form of paper_global_H's
  guards.  Status.  No source guard is strengthened, and no logical
  inference rule, C theorem, or semantic assumption is added.
\<close>

lemma paper_imp_language_iff:
  "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop \<longleftrightarrow>
    (sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<and>
     sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop)"
  by (auto simp only: sterm_in_language_def paper_imp_type_iff paper_imp_signature)

lemma source_app_argument_guard:
  fixes F A :: "('c,'l) sterm"
  assumes whole: "sterm_in_language L \<Sigma> \<Gamma> (SApp F A) \<tau>"
    and head: "has_stype L \<Gamma> F (Arr \<sigma> \<tau>)"
  shows "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
proof -
  have typed: "has_stype L \<Gamma> (SApp F A) \<tau>"
    using whole unfolding sterm_in_language_def by (rule conjunct1)
  obtain \<nu> where ft: "has_stype L \<Gamma> F (Arr \<nu> \<tau>)" and at: "has_stype L \<Gamma> A \<nu>"
    by (rule source_app_type_obtain[OF typed]; rule that; assumption)
  have types: "Arr \<nu> \<tau> = Arr \<sigma> \<tau>" by (rule source_typing_unique[OF ft head])
  have domain: "\<nu> = \<sigma>" using types by simp
  have arg_type: "has_stype L \<Gamma> A \<sigma>" using at by (simp only: domain)
  have names: "sterm_in_signature \<Sigma> A" using whole unfolding sterm_in_language_def by simp
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF arg_type names])
qed

lemma source_app_function_guard:
  fixes F A :: "('c,'l) sterm"
  assumes whole: "sterm_in_language L \<Sigma> \<Gamma> (SApp F A) \<tau>"
    and argument: "has_stype L \<Gamma> A \<sigma>"
  shows "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
proof -
  have typed: "has_stype L \<Gamma> (SApp F A) \<tau>"
    using whole unfolding sterm_in_language_def by (rule conjunct1)
  obtain \<nu> where ft: "has_stype L \<Gamma> F (Arr \<nu> \<tau>)" and at: "has_stype L \<Gamma> A \<nu>"
    by (rule source_app_type_obtain[OF typed]; rule that; assumption)
  have domain: "\<nu> = \<sigma>" by (rule source_typing_unique[OF at argument])
  have fun_type: "has_stype L \<Gamma> F (Arr \<sigma> \<tau>)" using ft by (simp only: domain)
  have names: "sterm_in_signature \<Sigma> F" using whole unfolding sterm_in_language_def by simp
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF fun_type names])
qed

lemma source_binary_operands_guard:
  fixes F A B :: "('c,'l) sterm"
  assumes whole: "sterm_in_language L \<Sigma> \<Gamma> (SApp (SApp F A) B) \<rho>"
    and head: "has_stype L \<Gamma> F (Arr \<sigma> (Arr \<tau> \<rho>))"
  shows "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
    and "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
proof -
  have typed: "has_stype L \<Gamma> (SApp (SApp F A) B) \<rho>"
    using whole unfolding sterm_in_language_def by (rule conjunct1)
  obtain \<beta> where fa: "has_stype L \<Gamma> (SApp F A) (Arr \<beta> \<rho>)"
    and bt: "has_stype L \<Gamma> B \<beta>"
    by (rule source_app_type_obtain[OF typed]; rule that; assumption)
  obtain \<alpha> where ft: "has_stype L \<Gamma> F (Arr \<alpha> (Arr \<beta> \<rho>))"
    and at: "has_stype L \<Gamma> A \<alpha>"
    by (rule source_app_type_obtain[OF fa]; rule that; assumption)
  have types: "Arr \<alpha> (Arr \<beta> \<rho>) = Arr \<sigma> (Arr \<tau> \<rho>)"
    by (rule source_typing_unique[OF ft head])
  have first_type: "\<alpha> = \<sigma>" and second_type: "\<beta> = \<tau>" using types by simp_all
  have A_type: "has_stype L \<Gamma> A \<sigma>" using at by (simp only: first_type)
  have B_type: "has_stype L \<Gamma> B \<tau>" using bt by (simp only: second_type)
  have A_names: "sterm_in_signature \<Sigma> A" and B_names: "sterm_in_signature \<Sigma> B"
    using whole unfolding sterm_in_language_def by simp_all
  show "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
    unfolding sterm_in_language_def by (rule conjI[OF A_type A_names])
  show "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF B_type B_names])
qed

subsection \<open>UI and EG: the quantifier fixes the predicate domain\<close>

lemma paper_UI_guard_operands:
  fixes F A :: "'c paper_term"
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
proof -
  have parts: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical (SAll \<sigma>)) F) Prop \<and>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) Prop"
    using whole by (simp only: paper_imp_language_iff)
  have quantifier: "has_stype paper_logical_type \<Gamma>
    (SLogical (SAll \<sigma>) :: 'c paper_term) (Arr (Arr \<sigma> Prop) Prop)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l="SAll \<sigma>"] by simp
  have F_guard: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    by (rule source_app_argument_guard[OF conjunct1[OF parts] quantifier])
  have F_type: "has_stype paper_logical_type \<Gamma> F (Arr \<sigma> Prop)"
    using F_guard unfolding sterm_in_language_def by (rule conjunct1)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)" by (rule F_guard)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    by (rule source_app_argument_guard[OF conjunct2[OF parts] F_type])
qed

lemma paper_EG_guard_operands:
  fixes F A :: "'c paper_term"
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
proof -
  have parts: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) Prop \<and>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical (SEx \<sigma>)) F) Prop"
    using whole by (simp only: paper_imp_language_iff)
  have quantifier: "has_stype paper_logical_type \<Gamma>
    (SLogical (SEx \<sigma>) :: 'c paper_term) (Arr (Arr \<sigma> Prop) Prop)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l="SEx \<sigma>"] by simp
  have F_guard: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    by (rule source_app_argument_guard[OF conjunct2[OF parts] quantifier])
  have F_type: "has_stype paper_logical_type \<Gamma> F (Arr \<sigma> Prop)"
    using F_guard unfolding sterm_in_language_def by (rule conjunct1)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)" by (rule F_guard)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    by (rule source_app_argument_guard[OF conjunct1[OF parts] F_type])
qed

subsection \<open>Ref and LL: the identity index fixes both object types\<close>

lemma paper_identity_guard_operands:
  fixes A B :: "'c paper_term"
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) B) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
proof -
  have identity_type: "has_stype paper_logical_type \<Gamma>
    (SLogical (SEq \<sigma>) :: 'c paper_term) (Arr \<sigma> (Arr \<sigma> Prop))"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l="SEq \<sigma>"] by simp
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    by (rule source_binary_operands_guard(1)[OF whole identity_type])
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
    by (rule source_binary_operands_guard(2)[OF whole identity_type])
qed

lemma paper_Ref_guard_operand:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) A) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  by (rule paper_identity_guard_operands(1)[OF whole])

lemma paper_LL_guard_operands:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B)
      (paper_imp (SApp F A) (SApp F B))) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
proof -
  have parts: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) B) Prop \<and>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp (SApp F A) (SApp F B)) Prop"
    using whole by (simp only: paper_imp_language_iff)
  have A_guard: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    by (rule paper_identity_guard_operands(1)[OF conjunct1[OF parts]])
  have A_type: "has_stype paper_logical_type \<Gamma> A \<sigma>"
    using A_guard unfolding sterm_in_language_def by (rule conjunct1)
  have applications: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) Prop \<and>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F B) Prop"
    using conjunct2[OF parts] by (simp only: paper_imp_language_iff)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>" by (rule A_guard)
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
    by (rule paper_identity_guard_operands(2)[OF conjunct1[OF parts]])
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    by (rule source_app_function_guard[OF conjunct1[OF applications] A_type])
qed

subsection \<open>Translation endpoints with precisely the whole-axiom guard\<close>

theorem paper_UI_guarded_translation:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)) Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)))"
  by (rule paper_UI_translation[OF paper_UI_guard_operands(1)[OF whole] paper_UI_guard_operands(2)[OF whole]])

theorem paper_EG_guarded_translation:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)) Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)))"
  by (rule paper_EG_translation[OF paper_EG_guard_operands(1)[OF whole] paper_EG_guard_operands(2)[OF whole]])

theorem paper_Ref_guarded_translation:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) A) Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (SApp (SApp (SLogical (SEq \<sigma>)) A) A))"
  by (rule paper_Ref_translation[OF paper_Ref_guard_operand[OF whole]])

theorem paper_LL_guarded_translation:
  assumes whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B)
      (paper_imp (SApp F A) (SApp F B))) Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B)
      (paper_imp (SApp F A) (SApp F B))))"
  by (rule paper_LL_translation[OF paper_LL_guard_operands(1)[OF whole]
    paper_LL_guard_operands(2)[OF whole] paper_LL_guard_operands(3)[OF whole]])

end
