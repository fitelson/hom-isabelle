theory Bacon_C_PC_Zeroary
  imports Bacon_C_PC_Single_Abstraction
begin

section \<open>The zeroary PC identity in C\<close>

text \<open>
  If A is a propositional tautology, then ⊢C A =ₜ ⊤₀.  Introduce a
  dummy p:t, obtain (λp.A) =ₜ→ₜ (λp.⊤₀) by the single-abstraction
  PC theorem, apply both sides to ⊤₀, and β reduce.
  Source: the empty-abstraction-vector PC case of Bacon–Dorr
  Appendix A.2(i), p.65, using PC from Figure 2, p.8.

  Isabelle representation.  shift A inserts the unused de Bruijn slot;
  subst0_shift removes it after application.  ObjTrue represents the
  closed formula ⊤₀ := ∀p.(p → p).  Congruence applies the proved
  predicate identity; it does not abstract a previously proved C identity.

  Status.  Every object-language inference is in axiom-based C.  No CE,
  CEV, necessitation, or abstraction rule for arbitrary C theorems is used.
  This is the zeroary case, not the arbitrary-vector PC theorem or the
  whole Appendix A.2 proof induction.
\<close>

subsection \<open>Renaming preserves the propositional Boolean skeleton\<close>

lemma C_PC_zeroary_eval_rename:
  "prop_eval w (rename r A) = prop_eval (\<lambda>B. prop_eval w (rename r B)) A"
  by (induction A arbitrary: r) simp_all

lemma C_PC_zeroary_tautology_shift:
  assumes tautology: "prop_tautology \<Gamma> A"
  shows "prop_tautology (\<sigma> # \<Gamma>) (shift A)"
proof -
  have typed: "\<Gamma> \<turnstile> A : Prop" using tautology unfolding prop_tautology_def by (rule conjunct1)
  have shifted_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop" by (rule weakening_front[OF typed])
  have valid: "\<forall>w. prop_eval w A" using tautology unfolding prop_tautology_def by (rule conjunct2)
  have shifted_valid: "\<forall>w. prop_eval w (shift A)"
  proof (rule allI)
    fix w
    have original: "prop_eval (\<lambda>B. prop_eval w (rename Suc B)) A" by (rule spec[OF valid])
    have equation: "prop_eval w (shift A) = prop_eval (\<lambda>B. prop_eval w (rename Suc B)) A"
      unfolding shift_def by (rule C_PC_zeroary_eval_rename)
    show "prop_eval w (shift A)" by (rule iffD2[OF equation original])
  qed
  show ?thesis unfolding prop_tautology_def by (rule conjI[OF shifted_type shifted_valid])
qed

subsection \<open>Applying the one-abstraction identity removes the dummy slot\<close>

theorem C_PC_zeroary_identity:
  assumes tautology: "prop_tautology \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
proof -
  let ?F = "Lam Prop (shift A)"
  let ?G = "Lam Prop ObjTrue"
  have A_type: "\<Gamma> \<turnstile> A : Prop" using tautology unfolding prop_tautology_def by (rule conjunct1)
  have shifted_type: "Prop # \<Gamma> \<turnstile> shift A : Prop" by (rule weakening_front[OF A_type])
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF shifted_type])
  have G_type: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF typed_ObjTrue])
  have truth_type: "\<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  have shifted_tautology: "prop_tautology (Prop # \<Gamma>) (shift A)"
    by (rule C_PC_zeroary_tautology_shift[OF tautology])
  have predicate_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop) ?F ?G"
    by (rule C_PC_single_abstraction[OF shifted_tautology])
  have applied_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (App ?F ObjTrue) (App ?G ObjTrue)"
    by (rule C_closure_app_congruence_left[OF F_type G_type truth_type predicate_identity])
  have FA_type: "\<Gamma> \<turnstile> App ?F ObjTrue : Prop" by (rule has_type.App[OF F_type truth_type])
  have GA_type: "\<Gamma> \<turnstile> App ?G ObjTrue : Prop" by (rule has_type.App[OF G_type truth_type])
  have left_raw: "compatible_step beta_contract (App ?F ObjTrue) (subst0 ObjTrue (shift A))"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have left_step: "compatible_step beta_contract (App ?F ObjTrue) A"
    using left_raw by (simp only: subst0_shift)
  have left_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (App ?F ObjTrue) A"
    by (rule C_closure_beta_identity[OF FA_type A_type left_step])
  have right_raw: "compatible_step beta_contract (App ?G ObjTrue) (subst0 ObjTrue ObjTrue)"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have right_step: "compatible_step beta_contract (App ?G ObjTrue) ObjTrue"
    using right_raw by (simp add: subst0_def ObjTrue_def)
  have right_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (App ?G ObjTrue) ObjTrue"
    by (rule C_closure_beta_identity[OF GA_type truth_type right_step])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF left_identity]
    C_A1_trans[OF applied_identity right_identity]])
qed

end
