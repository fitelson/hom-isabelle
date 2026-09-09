theory Bacon_Parametric_H_Soundness
  imports Bacon_Parametric_H_Soundness_Basic
begin

section \<open>Soundness of H over arbitrary constant-name carriers\<close>

text \<open>
  From P → Q(v), infer P → ∀v.Q(v) when v ∉ FV(P).
  From P(v) → Q, infer (∃v.P(v)) → Q when v ∉ FV(Q).

  Isabelle representation: pH_BBK_Gen and pH_BBK_Inst use pshift to encode
  those side conditions.  The assignment-shift theorem compares the
  corresponding de Bruijn representations; UI/EG use the preceding
  one-binder substitution law.

  Status: quantifier-rule soundness followed by the full pH_proves induction.
  The model’s actual signature is retained, with no countability or universal-
  signature premise.  Soundness is not model existence or completeness.
\<close>

context pbbk_model
begin

lemma pH_BBK_Gen:
  assumes P: "has_ptype \<Gamma> P Prop" and Q: "has_ptype (\<sigma> # \<Gamma>) Q Prop"
    and sigP: "pterm_in_signature signature P" and sigQ: "pterm_in_signature signature Q"
    and premise: "\<And>h. pbbk_env_typed domain (\<sigma> # \<Gamma>) h \<Longrightarrow>
      valuation (denote h (PImp (pshift P) Q))"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PImp P (PForall \<sigma> Q)))"
proof -
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift P) Prop" by (rule pshift_preserves_typing[OF P])
  have sigShift: "pterm_in_signature signature (pshift P)" using sigP by (simp add: pshift_def)
  have quantified: "has_ptype \<Gamma> (PForall \<sigma> Q) Prop" by (rule has_ptype.PForall[OF Q])
  have sigForall: "pterm_in_signature signature (PForall \<sigma> Q)" using sigQ by simp
  have condition: "valuation (denote g P) \<longrightarrow> (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) Q))"
  proof (intro impI ballI)
    fix a
    assume truthP: "valuation (denote g P)" and element: "a \<in> domain \<sigma>"
    have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a g)"
      by (rule pbbk_env_extend[OF env element])
    have implication: "valuation (denote (pbbk_extend a g) (PImp (pshift P) Q))"
      by (rule premise[OF extended])
    have unchanged: "denote (pbbk_extend a g) (pshift P) = denote g P"
      by (rule pbbk_shift_assignment[OF P sigP env element])
    have material_implication: "valuation (denote g P) \<longrightarrow>
        valuation (denote (pbbk_extend a g) Q)"
      using implication
      by (simp only: valuation_imp[OF shifted Q sigShift sigQ extended] unchanged)
    show "valuation (denote (pbbk_extend a g) Q)"
      by (rule mp[OF material_implication truthP])
  qed
  show ?thesis using condition
    by (simp only: valuation_imp[OF P quantified sigP sigForall env] valuation_forall[OF Q sigQ env])
qed

lemma pH_BBK_Inst:
  assumes P: "has_ptype (\<sigma> # \<Gamma>) P Prop" and Q: "has_ptype \<Gamma> Q Prop"
    and sigP: "pterm_in_signature signature P" and sigQ: "pterm_in_signature signature Q"
    and premise: "\<And>h. pbbk_env_typed domain (\<sigma> # \<Gamma>) h \<Longrightarrow>
      valuation (denote h (PImp P (pshift Q)))"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PImp (PExists \<sigma> P) Q))"
proof -
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift Q) Prop" by (rule pshift_preserves_typing[OF Q])
  have sigShift: "pterm_in_signature signature (pshift Q)" using sigQ by (simp add: pshift_def)
  have quantified: "has_ptype \<Gamma> (PExists \<sigma> P) Prop" by (rule has_ptype.PExists[OF P])
  have sigExists: "pterm_in_signature signature (PExists \<sigma> P)" using sigP by simp
  have condition: "(\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) P)) \<longrightarrow> valuation (denote g Q)"
  proof (rule impI)
    assume witness: "\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) P)"
    obtain a where element: "a \<in> domain \<sigma>" and truthP: "valuation (denote (pbbk_extend a g) P)"
      using witness by blast
    have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a g)"
      by (rule pbbk_env_extend[OF env element])
    have implication: "valuation (denote (pbbk_extend a g) (PImp P (pshift Q)))"
      by (rule premise[OF extended])
    have unchanged: "denote (pbbk_extend a g) (pshift Q) = denote g Q"
      by (rule pbbk_shift_assignment[OF Q sigQ env element])
    have material_implication: "valuation (denote (pbbk_extend a g) P) \<longrightarrow>
        valuation (denote g Q)"
      using implication
      by (simp only: valuation_imp[OF P shifted sigP sigShift extended] unchanged)
    show "valuation (denote g Q)"
      by (rule mp[OF material_implication truthP])
  qed
  show ?thesis using condition
    by (simp only: valuation_imp[OF quantified Q sigExists sigQ env] valuation_exists[OF P sigP env])
qed

subsection \<open>Induction on the full signature-indexed derivation\<close>

text \<open>
  Σ; Γ ⊢H A entails M,g ⊨ A for every Γ-typed assignment g in each
  BBK model M of Σ.

  Isabelle representation: pH_BBK_soundness_at_assignment handles every pH_proves
  constructor; pH_BBK_soundness packages typing, signature membership,
  and truth at all typed assignments as pbbk_valid_in_context.

  Status: soundness for the actual arbitrary signature.  No countability,
  completeness, or canonical-model construction is used.
\<close>

theorem pH_BBK_soundness_at_assignment:
  assumes derivation: "pH_proves signature \<Gamma> A" and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g A)"
  using derivation env
proof (induction arbitrary: g rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pH_BBK_PC[OF PC.hyps(1,2) PC.prems])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule pH_BBK_IndividualExistence[OF IndividualExistence.prems])
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (rule pH_BBK_UI[OF UI.hyps(1,2,3,4) UI.prems])
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (rule pH_BBK_EG[OF EG.hyps(1,2,3,4) EG.prems])
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (rule pH_BBK_Ref[OF Ref.hyps(1,2) Ref.prems])
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (rule pH_BBK_LL[OF LL.hyps(1,2,3,4,5,6) LL.prems])
next
  case (Beta \<Gamma> A B)
  show ?case by (rule pH_BBK_Beta[OF Beta.hyps(1,2,3,4,5) Beta.prems])
next
  case (Eta \<Gamma> A B)
  show ?case by (rule pH_BBK_Eta[OF Eta.hyps(1,2,3,4,5) Eta.prems])
next
  case (MP \<Gamma> A B)
  have A_type: "has_ptype \<Gamma> A Prop" by (rule pH_proves_formula[OF MP.hyps(1)])
  have imp_type: "has_ptype \<Gamma> (PImp A B) Prop" by (rule pH_proves_formula[OF MP.hyps(2)])
  have B_type: "has_ptype \<Gamma> B Prop" using imp_type by (auto elim: has_ptype.cases)
  have truthA: "valuation (denote g A)" by (rule MP.IH(1)[where g=g, OF MP.prems])
  have truthImp: "valuation (denote g (PImp A B))" by (rule MP.IH(2)[where g=g, OF MP.prems])
  show ?case by (rule pH_BBK_MP[OF A_type B_type MP.hyps(3,4) MP.prems truthA truthImp])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule pH_BBK_Gen[OF Gen.hyps(1,2,3,4) Gen.IH Gen.prems])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule pH_BBK_Inst[OF Inst.hyps(1,2,3,4) Inst.IH Inst.prems])
qed

theorem pH_BBK_soundness:
  assumes derivation: "pH_proves signature \<Gamma> A"
  shows "pbbk_valid_in_context \<Gamma> A"
proof -
  have typed: "has_ptype \<Gamma> A Prop" by (rule pH_proves_formula[OF derivation])
  have sig: "pterm_in_signature signature A" by (rule pH_proves_in_signature[OF derivation])
  have all_assignments: "\<forall>g. pbbk_env_typed domain \<Gamma> g \<longrightarrow> pbbk_satisfies g A"
  proof (intro allI impI)
    fix g
    assume env: "pbbk_env_typed domain \<Gamma> g"
    show "pbbk_satisfies g A" unfolding pbbk_satisfies_def
      by (rule pH_BBK_soundness_at_assignment[OF derivation env])
  qed
  show ?thesis unfolding pbbk_valid_in_context_def using typed sig all_assignments by blast
qed

end
end
