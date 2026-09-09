theory Bacon_Parametric_Deduction
  imports Bacon_Parametric_Beta
begin

section \<open>H theoremhood in an arbitrary-name signature\<close>

text \<open>
  Σ; Γ ⊢H A means that A is an H theorem in ℒ(Σ), with the free-variable
  types recorded by Γ.  Γ is not a set of formula assumptions.

  Isabelle representation: pH_proves Σ Γ A guards every term by its signature,
  including intermediate MP formulas.  PObjIff is the conjunction of two
  implications; PObjTrue is ∀p(p → p), and PObjFalse is its negation.

  Status: the represented Bacon–Dorr Figure 2 calculus, with the explicit
  context-indexed IndividualExistence rule.  Names are arbitrary; full F
  types and primitive Imp remain.  No first-class-constant translation or
  completeness follows merely from this definition.
\<close>

abbreviation PObjIff :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "PObjIff A B \<equiv> PConj (PImp A B) (PImp B A)"

definition PObjTrue :: "'c pterm" where
  "PObjTrue = PForall Prop (PImp (PVar 0) (PVar 0))"

definition PObjFalse :: "'c pterm" where
  "PObjFalse = PNeg PObjTrue"

inductive pH_proves :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm \<Rightarrow> bool"
  for \<Sigma> :: "'c psignature" where
  PC: "pprop_tautology \<Gamma> A \<Longrightarrow> pterm_in_signature \<Sigma> A \<Longrightarrow> pH_proves \<Sigma> \<Gamma> A"
| IndividualExistence: "pH_proves \<Sigma> \<Gamma> (PExists Ind (PEq Ind (PVar 0) (PVar 0)))"
| UI: "has_ptype (\<sigma> # \<Gamma>) A Prop \<Longrightarrow> has_ptype \<Gamma> T \<sigma> \<Longrightarrow>
    pterm_in_signature \<Sigma> A \<Longrightarrow> pterm_in_signature \<Sigma> T \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp (PForall \<sigma> A) (psubst0 T A))"
| EG: "has_ptype (\<sigma> # \<Gamma>) A Prop \<Longrightarrow> has_ptype \<Gamma> T \<sigma> \<Longrightarrow>
    pterm_in_signature \<Sigma> A \<Longrightarrow> pterm_in_signature \<Sigma> T \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp (psubst0 T A) (PExists \<sigma> A))"
| Ref: "has_ptype \<Gamma> M \<sigma> \<Longrightarrow> pterm_in_signature \<Sigma> M \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PEq \<sigma> M M)"
| LL: "has_ptype \<Gamma> A \<sigma> \<Longrightarrow> has_ptype \<Gamma> B \<sigma> \<Longrightarrow>
    has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o Prop) \<Longrightarrow>
    pterm_in_signature \<Sigma> A \<Longrightarrow> pterm_in_signature \<Sigma> B \<Longrightarrow> pterm_in_signature \<Sigma> F \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B)))"
| Beta: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> B Prop \<Longrightarrow>
    pcompatible_step pbeta_contract A B \<Longrightarrow> pterm_in_signature \<Sigma> A \<Longrightarrow>
    pterm_in_signature \<Sigma> B \<Longrightarrow> pH_proves \<Sigma> \<Gamma> (PObjIff A B)"
| Eta: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> B Prop \<Longrightarrow>
    pcompatible_step peta_contract A B \<Longrightarrow> pterm_in_signature \<Sigma> A \<Longrightarrow>
    pterm_in_signature \<Sigma> B \<Longrightarrow> pH_proves \<Sigma> \<Gamma> (PObjIff A B)"
| MP: "pH_proves \<Sigma> \<Gamma> A \<Longrightarrow> pH_proves \<Sigma> \<Gamma> (PImp A B) \<Longrightarrow>
    pterm_in_signature \<Sigma> A \<Longrightarrow> pterm_in_signature \<Sigma> B \<Longrightarrow> pH_proves \<Sigma> \<Gamma> B"
| Gen: "has_ptype \<Gamma> P Prop \<Longrightarrow> has_ptype (\<sigma> # \<Gamma>) Q Prop \<Longrightarrow>
    pterm_in_signature \<Sigma> P \<Longrightarrow> pterm_in_signature \<Sigma> Q \<Longrightarrow>
    pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (pshift P) Q) \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp P (PForall \<sigma> Q))"
| Inst: "has_ptype (\<sigma> # \<Gamma>) P Prop \<Longrightarrow> has_ptype \<Gamma> Q Prop \<Longrightarrow>
    pterm_in_signature \<Sigma> P \<Longrightarrow> pterm_in_signature \<Sigma> Q \<Longrightarrow>
    pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp P (pshift Q)) \<Longrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp (PExists \<sigma> P) Q)"

subsection \<open>Typing and language invariants\<close>

text \<open>
  Σ; Γ ⊢H A entails Γ ⊢ A:t and A ∈ ℒ(Σ).

  Isabelle representation: pH_proves_formula and pH_proves_in_signature are
  separate inductions over the guarded constructors; pH_proves_in_language
  combines their conclusions.

  Status: well-formedness invariants, not semantic soundness or consistency.
\<close>

lemma psubst0_signature:
  assumes body: "pterm_in_signature \<Sigma> A" and arg: "pterm_in_signature \<Sigma> T"
  shows "pterm_in_signature \<Sigma> (psubst0 T A)"
  unfolding psubst0_def
proof (rule psubst_signature[OF body])
  fix n
  show "pterm_in_signature \<Sigma> (case_nat T PVar n)" by (cases n) (simp_all add: arg)
qed

lemma pH_proves_formula:
  assumes "pH_proves \<Sigma> \<Gamma> A"
  shows "has_ptype \<Gamma> A Prop"
  using assms
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case using PC.hyps(1) unfolding pprop_tautology_def by blast
next
  case (IndividualExistence \<Gamma>)
  show ?case by (intro has_ptype.PExists has_ptype.PEq has_ptype.PVar) simp_all
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (rule has_ptype.PImp[OF has_ptype.PForall[OF UI.hyps(1)]
    psubst0_preserves_typing[OF UI.hyps(1,2)]])
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (rule has_ptype.PImp[OF psubst0_preserves_typing[OF EG.hyps(1,2)]
    has_ptype.PExists[OF EG.hyps(1)]])
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (rule has_ptype.PEq[OF Ref.hyps(1) Ref.hyps(1)])
next
  case (LL \<Gamma> A \<sigma> B F)
  have A_type: "has_ptype \<Gamma> A \<sigma>" by (rule LL.hyps(1))
  have B_type: "has_ptype \<Gamma> B \<sigma>" by (rule LL.hyps(2))
  have F_type: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o Prop)" by (rule LL.hyps(3))
  have equality_type: "has_ptype \<Gamma> (PEq \<sigma> A B) Prop"
    by (rule has_ptype.PEq[OF A_type B_type])
  have FA_type: "has_ptype \<Gamma> (PApp F A) Prop"
    by (rule has_ptype.PApp[OF F_type A_type])
  have FB_type: "has_ptype \<Gamma> (PApp F B) Prop"
    by (rule has_ptype.PApp[OF F_type B_type])
  have implication_type: "has_ptype \<Gamma> (PImp (PApp F A) (PApp F B)) Prop"
    by (rule has_ptype.PImp[OF FA_type FB_type])
  show ?case by (rule has_ptype.PImp[OF equality_type implication_type])
next
  case (Beta \<Gamma> A B)
  show ?case by (intro has_ptype.PConj has_ptype.PImp Beta.hyps(1,2))
next
  case (Eta \<Gamma> A B)
  show ?case by (intro has_ptype.PConj has_ptype.PImp Eta.hyps(1,2))
next
  case (MP \<Gamma> A B)
  show ?case using MP.IH(2) by (auto elim: has_ptype.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule has_ptype.PImp[OF Gen.hyps(1) has_ptype.PForall[OF Gen.hyps(2)]])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule has_ptype.PImp[OF has_ptype.PExists[OF Inst.hyps(1)] Inst.hyps(2)])
qed

lemma pH_proves_in_signature:
  assumes "pH_proves \<Sigma> \<Gamma> A"
  shows "pterm_in_signature \<Sigma> A"
  using assms
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule PC.hyps(2))
next
  case (IndividualExistence \<Gamma>)
  show ?case by simp
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case using UI.hyps(3) psubst0_signature[OF UI.hyps(3,4)] by simp
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case using EG.hyps(3) psubst0_signature[OF EG.hyps(3,4)] by simp
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case using Ref.hyps(2) by simp
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case using LL.hyps(4,5,6) by simp
next
  case (Beta \<Gamma> A B)
  show ?case using Beta.hyps(4,5) by simp
next
  case (Eta \<Gamma> A B)
  show ?case using Eta.hyps(4,5) by simp
next
  case (MP \<Gamma> A B)
  show ?case by (rule MP.hyps(4))
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case using Gen.hyps(3,4) by simp
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case using Inst.hyps(3,4) by simp
qed

lemma pH_proves_in_language:
  "pH_proves \<Sigma> \<Gamma> A \<Longrightarrow> pterm_in_language \<Sigma> \<Gamma> A Prop"
  using pH_proves_formula pH_proves_in_signature unfolding pterm_in_language_def by blast

subsection \<open>String-instance translation after forgetting the signature\<close>

text \<open>
  At string names, Σ; Γ ⊢H A yields the corresponding unrestricted
  H theorem.  The converse here uses the universal signature.

  Isabelle representation: pH_string_proves_to_H forgets signature guards;
  H_to_pH_string_universal and pH_string_universal_iff prove the converse
  only when every typed string is available.

  Status: no reflection into an arbitrary smaller Σ is inferred from a guard
  on the conclusion alone.
\<close>

theorem pH_string_proves_to_H:
  assumes "pH_proves \<Sigma> \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H pterm_to_oterm A"
  using assms
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  have taut: "prop_tautology \<Gamma> (pterm_to_oterm A)"
    using PC.hyps(1) by (simp only: pprop_tautology_string_iff)
  show ?case by (rule H_proves.PC[OF taut])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (simp only: pterm_to_oterm.simps) (rule H_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_to_oterm.simps pterm_to_psubst0)
    (rule H_proves.UI[OF pterm_to_preserves_typing[OF UI.hyps(1)] pterm_to_preserves_typing[OF UI.hyps(2)]])
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_to_oterm.simps pterm_to_psubst0)
    (rule H_proves.EG[OF pterm_to_preserves_typing[OF EG.hyps(1)] pterm_to_preserves_typing[OF EG.hyps(2)]])
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.Ref[OF pterm_to_preserves_typing[OF Ref.hyps(1)]])
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.LL[OF pterm_to_preserves_typing[OF LL.hyps(1)]
      pterm_to_preserves_typing[OF LL.hyps(2)] pterm_to_preserves_typing[OF LL.hyps(3)]])
next
  case (Beta \<Gamma> A B)
  have step: "compatible_step beta_contract (pterm_to_oterm A) (pterm_to_oterm B)"
    using Beta.hyps(3) by (simp only: pcompatible_beta_string_iff)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.Beta[OF pterm_to_preserves_typing[OF Beta.hyps(1)] pterm_to_preserves_typing[OF Beta.hyps(2)] step])
next
  case (Eta \<Gamma> A B)
  have step: "compatible_step eta_contract (pterm_to_oterm A) (pterm_to_oterm B)"
    using Eta.hyps(3) by (simp only: pcompatible_eta_string_iff)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.Eta[OF pterm_to_preserves_typing[OF Eta.hyps(1)] pterm_to_preserves_typing[OF Eta.hyps(2)] step])
next
  case (MP \<Gamma> A B)
  have implication: "\<Gamma> \<turnstile>\<^sub>H Imp (pterm_to_oterm A) (pterm_to_oterm B)"
    using MP.IH(2) by simp
  show ?case by (rule H_proves.MP[OF MP.IH(1) implication])
next
  case (Gen \<Gamma> P \<sigma> Q)
  have implication: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift (pterm_to_oterm P)) (pterm_to_oterm Q)"
    using Gen.IH by (simp only: pterm_to_oterm.simps pterm_to_pshift)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.Gen[OF pterm_to_preserves_typing[OF Gen.hyps(1)] pterm_to_preserves_typing[OF Gen.hyps(2)] implication])
next
  case (Inst \<sigma> \<Gamma> P Q)
  have implication: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (pterm_to_oterm P) (shift (pterm_to_oterm Q))"
    using Inst.IH by (simp only: pterm_to_oterm.simps pterm_to_pshift)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_proves.Inst[OF pterm_to_preserves_typing[OF Inst.hyps(1)] pterm_to_preserves_typing[OF Inst.hyps(2)] implication])
qed

theorem H_to_pH_string_universal:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "pH_proves (\<lambda>_. UNIV) \<Gamma> (pterm_of_oterm A)"
  using assms
proof (induction rule: H_proves.induct)
  case (PC \<Gamma> A)
  have taut: "pprop_tautology \<Gamma> (pterm_of_oterm A)"
    using PC.hyps by (simp only: pprop_tautology_string_iff pterm_to_of)
  show ?case by (rule pH_proves.PC[OF taut]) simp
next
  case (IndividualExistence \<Gamma>)
  show ?case by (simp only: pterm_of_oterm.simps) (rule pH_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_of_oterm.simps pterm_of_subst0)
    (rule pH_proves.UI[OF pterm_of_preserves_typing[OF UI.hyps(1)] pterm_of_preserves_typing[OF UI.hyps(2)]]; simp)
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_of_oterm.simps pterm_of_subst0)
    (rule pH_proves.EG[OF pterm_of_preserves_typing[OF EG.hyps(1)] pterm_of_preserves_typing[OF EG.hyps(2)]]; simp)
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.Ref[OF pterm_of_preserves_typing[OF Ref.hyps]]; simp)
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.LL[OF pterm_of_preserves_typing[OF LL.hyps(1)]
      pterm_of_preserves_typing[OF LL.hyps(2)] pterm_of_preserves_typing[OF LL.hyps(3)]]; simp)
next
  case (Beta \<Gamma> A B)
  have step: "pcompatible_step pbeta_contract (pterm_of_oterm A) (pterm_of_oterm B)"
    by (rule pcompatible_of_oterm[OF Beta.hyps(3)]) (rule pbeta_of_oterm)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.Beta[OF pterm_of_preserves_typing[OF Beta.hyps(1)] pterm_of_preserves_typing[OF Beta.hyps(2)] step]; simp)
next
  case (Eta \<Gamma> A B)
  have step: "pcompatible_step peta_contract (pterm_of_oterm A) (pterm_of_oterm B)"
    by (rule pcompatible_of_oterm[OF Eta.hyps(3)]) (rule peta_of_oterm)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.Eta[OF pterm_of_preserves_typing[OF Eta.hyps(1)] pterm_of_preserves_typing[OF Eta.hyps(2)] step]; simp)
next
  case (MP \<Gamma> A B)
  have implication: "pH_proves (\<lambda>_. UNIV) \<Gamma> (PImp (pterm_of_oterm A) (pterm_of_oterm B))"
    using MP.IH(2) by simp
  show ?case by (rule pH_proves.MP[OF MP.IH(1) implication]; simp)
next
  case (Gen \<Gamma> P \<sigma> Q)
  have implication: "pH_proves (\<lambda>_. UNIV) (\<sigma> # \<Gamma>) (PImp (pshift (pterm_of_oterm P)) (pterm_of_oterm Q))"
    using Gen.IH by (simp only: pterm_of_oterm.simps pterm_of_shift)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.Gen[OF pterm_of_preserves_typing[OF Gen.hyps(1)] pterm_of_preserves_typing[OF Gen.hyps(2)] _ _ implication]; simp)
next
  case (Inst \<sigma> \<Gamma> P Q)
  have implication: "pH_proves (\<lambda>_. UNIV) (\<sigma> # \<Gamma>) (PImp (pterm_of_oterm P) (pshift (pterm_of_oterm Q)))"
    using Inst.IH by (simp only: pterm_of_oterm.simps pterm_of_shift)
  show ?case by (simp only: pterm_of_oterm.simps)
    (rule pH_proves.Inst[OF pterm_of_preserves_typing[OF Inst.hyps(1)] pterm_of_preserves_typing[OF Inst.hyps(2)] _ _ implication]; simp)
qed

theorem pH_string_universal_iff:
  "pH_proves (\<lambda>_. UNIV) \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>H pterm_to_oterm A"
proof
  assume derivation: "pH_proves (\<lambda>_. UNIV) \<Gamma> A"
  show "\<Gamma> \<turnstile>\<^sub>H pterm_to_oterm A" by (rule pH_string_proves_to_H[OF derivation])
next
  assume derivation: "\<Gamma> \<turnstile>\<^sub>H pterm_to_oterm A"
  show "pH_proves (\<lambda>_. UNIV) \<Gamma> A"
    using H_to_pH_string_universal[OF derivation] by simp
qed

text \<open>
  Σ; Γ ⊢H A must not be inferred from an unrestricted ⊢H A merely because
  A ∈ ℒ(Σ): the intermediate proof terms must also respect Σ.

  Isabelle representation: pH_string_universal_iff gives the two-way string
  comparison only for the universal signature.  String_Bridge records the
  guarded cross-session contract; H_Soundness supplies arbitrary-signature
  semantic soundness in its own theory.

  Status: universal-signature proof correspondence here.  Restricted-signature
  comparison, witness-axiom consistency, and completeness have their own
  proof obligations.
\<close>

end
