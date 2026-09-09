theory Bacon_Parametric_String_Bridge
  imports Bacon_Parametric_Deduction
begin

section \<open>The string instance on the original term syntax\<close>

text \<open>
  Σ; Γ ⊢H A uses the same typed-string signature in either term syntax.
  A change of representation must preserve every proof-step guard.

  Isabelle representation: pH_on_string_syntax exposes pH_proves on oterm
  through pterm_of_oterm.  The inverse translation is pterm_to_oterm.
  H_signature_proves belongs to a later session and is not imported here.

  Status: exact syntax transport and universal-signature H correspondence.
  The guarded constructor lemmas prepare a downstream bridge; this file
  does not instantiate that bridge or prove smaller-signature conservativity.
\<close>

definition pH_on_string_syntax ::
    "(otype \<Rightarrow> string set) \<Rightarrow> ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "pH_on_string_syntax \<Sigma> \<Gamma> A \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"

lemma pH_string_translation_iff:
  "pH_proves \<Sigma> \<Gamma> A \<longleftrightarrow> pH_on_string_syntax \<Sigma> \<Gamma> (pterm_to_oterm A)"
  by (simp only: pH_on_string_syntax_def pterm_of_to)

lemma pH_on_string_formula:
  assumes "pH_on_string_syntax \<Sigma> \<Gamma> A"
  shows "\<Gamma> \<turnstile> A : Prop"
proof -
  have p: "pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
    using assms unfolding pH_on_string_syntax_def .
  have "has_ptype \<Gamma> (pterm_of_oterm A) Prop"
    by (rule pH_proves_formula[OF p])
  then have "\<Gamma> \<turnstile> pterm_to_oterm (pterm_of_oterm A) : Prop"
    by (rule pterm_to_preserves_typing)
  then show ?thesis by (simp only: pterm_to_of)
qed

lemma pH_on_string_signature:
  assumes "pH_on_string_syntax \<Sigma> \<Gamma> A"
  shows "oterm_in_string_signature \<Sigma> A"
proof -
  have p: "pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
    using assms unfolding pH_on_string_syntax_def .
  have "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    by (rule pH_proves_in_signature[OF p])
  then show ?thesis by (simp only: pterm_of_signature_iff)
qed

theorem pH_on_string_universal_iff:
  "pH_on_string_syntax (\<lambda>_. UNIV) \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>H A"
  by (simp only: pH_on_string_syntax_def pH_string_universal_iff pterm_to_of)

section \<open>Constructor translations retain the signature guards\<close>

text \<open>
  Each rule producing Σ; Γ ⊢H A translates without discarding its
  intermediate language-membership conditions.

  Isabelle representation: pH_on_string_PC through pH_on_string_Inst express
  the guarded parametric constructors directly on oterm.

  Status: constructor-by-constructor translation, ready for the downstream
  guarded-calculus comparison.
\<close>

lemma pH_on_string_PC:
  assumes "prop_tautology \<Gamma> A" and "oterm_in_string_signature \<Sigma> A"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> A"
proof -
  have taut: "pprop_tautology \<Gamma> (pterm_of_oterm A)"
    using assms(1) by (simp only: pprop_tautology_string_iff pterm_to_of)
  have sig: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(2) by (simp only: pterm_of_signature_iff)
  show ?thesis unfolding pH_on_string_syntax_def by (rule pH_proves.PC[OF taut sig])
qed

lemma pH_on_string_IndividualExistence:
  "pH_on_string_syntax \<Sigma> \<Gamma> (Exists Ind (Eq Ind (Var 0) (Var 0)))"
  unfolding pH_on_string_syntax_def
  by (simp only: pterm_of_oterm.simps) (rule pH_proves.IndividualExistence)

lemma pH_on_string_UI:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> T : \<sigma>"
    and "oterm_in_string_signature \<Sigma> A" and "oterm_in_string_signature \<Sigma> T"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Imp (Forall \<sigma> A) (subst0 T A))"
proof -
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(3) by (simp only: pterm_of_signature_iff)
  have st: "pterm_in_signature \<Sigma> (pterm_of_oterm T)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps pterm_of_subst0)
      (rule pH_proves.UI[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] sa st])
qed

lemma pH_on_string_EG:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> T : \<sigma>"
    and "oterm_in_string_signature \<Sigma> A" and "oterm_in_string_signature \<Sigma> T"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Imp (subst0 T A) (Exists \<sigma> A))"
proof -
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(3) by (simp only: pterm_of_signature_iff)
  have st: "pterm_in_signature \<Sigma> (pterm_of_oterm T)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps pterm_of_subst0)
      (rule pH_proves.EG[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] sa st])
qed

lemma pH_on_string_Ref:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "oterm_in_string_signature \<Sigma> M"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Eq \<sigma> M M)"
proof -
  have sig: "pterm_in_signature \<Sigma> (pterm_of_oterm M)"
    using assms(2) by (simp only: pterm_of_signature_iff)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.Ref[OF pterm_of_preserves_typing[OF assms(1)] sig])
qed

lemma pH_on_string_LL:
  assumes "\<Gamma> \<turnstile> A : \<sigma>" and "\<Gamma> \<turnstile> B : \<sigma>" and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and "oterm_in_string_signature \<Sigma> A" and "oterm_in_string_signature \<Sigma> B"
    and "oterm_in_string_signature \<Sigma> F"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)))"
proof -
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  have sb: "pterm_in_signature \<Sigma> (pterm_of_oterm B)"
    using assms(5) by (simp only: pterm_of_signature_iff)
  have sf: "pterm_in_signature \<Sigma> (pterm_of_oterm F)"
    using assms(6) by (simp only: pterm_of_signature_iff)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.LL[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] pterm_of_preserves_typing[OF assms(3)] sa sb sf])
qed

lemma pH_on_string_Beta:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
    and "oterm_in_string_signature \<Sigma> A" and "oterm_in_string_signature \<Sigma> B"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  have sb: "pterm_in_signature \<Sigma> (pterm_of_oterm B)"
    using assms(5) by (simp only: pterm_of_signature_iff)
  have step: "pcompatible_step pbeta_contract (pterm_of_oterm A) (pterm_of_oterm B)"
    by (rule pcompatible_of_oterm[OF assms(3)]) (rule pbeta_of_oterm)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.Beta[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] step sa sb])
qed

lemma pH_on_string_Eta:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
    and "oterm_in_string_signature \<Sigma> A" and "oterm_in_string_signature \<Sigma> B"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  have sb: "pterm_in_signature \<Sigma> (pterm_of_oterm B)"
    using assms(5) by (simp only: pterm_of_signature_iff)
  have step: "pcompatible_step peta_contract (pterm_of_oterm A) (pterm_of_oterm B)"
    by (rule pcompatible_of_oterm[OF assms(3)]) (rule peta_of_oterm)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.Eta[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] step sa sb])
qed

lemma pH_on_string_MP:
  assumes a: "pH_on_string_syntax \<Sigma> \<Gamma> A"
    and imp: "pH_on_string_syntax \<Sigma> \<Gamma> (Imp A B)"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> B"
proof -
  have pa: "pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
    using a unfolding pH_on_string_syntax_def .
  have pi: "pH_proves \<Sigma> \<Gamma> (PImp (pterm_of_oterm A) (pterm_of_oterm B))"
    using imp unfolding pH_on_string_syntax_def by (simp only: pterm_of_oterm.simps)
  have sa: "pterm_in_signature \<Sigma> (pterm_of_oterm A)" by (rule pH_proves_in_signature[OF pa])
  have si: "pterm_in_signature \<Sigma> (PImp (pterm_of_oterm A) (pterm_of_oterm B))"
    by (rule pH_proves_in_signature[OF pi])
  have sig_pair: "pterm_in_signature \<Sigma> (pterm_of_oterm A) \<and>
      pterm_in_signature \<Sigma> (pterm_of_oterm B)"
    using si by (simp only: pterm_in_signature.simps)
  have sb: "pterm_in_signature \<Sigma> (pterm_of_oterm B)"
    by (rule conjunct2[OF sig_pair])
  show ?thesis unfolding pH_on_string_syntax_def by (rule pH_proves.MP[OF pa pi sa sb])
qed

lemma pH_on_string_Gen:
  assumes "\<Gamma> \<turnstile> P : Prop" and "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and "oterm_in_string_signature \<Sigma> P" and "oterm_in_string_signature \<Sigma> Q"
    and "pH_on_string_syntax \<Sigma> (\<sigma> # \<Gamma>) (Imp (shift P) Q)"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Imp P (Forall \<sigma> Q))"
proof -
  have sp: "pterm_in_signature \<Sigma> (pterm_of_oterm P)"
    using assms(3) by (simp only: pterm_of_signature_iff)
  have sq: "pterm_in_signature \<Sigma> (pterm_of_oterm Q)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  have prem: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (pshift (pterm_of_oterm P)) (pterm_of_oterm Q))"
    using assms(5) unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps pterm_of_shift)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.Gen[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] sp sq prem])
qed

lemma pH_on_string_Inst:
  assumes "\<sigma> # \<Gamma> \<turnstile> P : Prop" and "\<Gamma> \<turnstile> Q : Prop"
    and "oterm_in_string_signature \<Sigma> P" and "oterm_in_string_signature \<Sigma> Q"
    and "pH_on_string_syntax \<Sigma> (\<sigma> # \<Gamma>) (Imp P (shift Q))"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> (Imp (Exists \<sigma> P) Q)"
proof -
  have sp: "pterm_in_signature \<Sigma> (pterm_of_oterm P)"
    using assms(3) by (simp only: pterm_of_signature_iff)
  have sq: "pterm_in_signature \<Sigma> (pterm_of_oterm Q)"
    using assms(4) by (simp only: pterm_of_signature_iff)
  have prem: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (pterm_of_oterm P) (pshift (pterm_of_oterm Q)))"
    using assms(5) unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps pterm_of_shift)
  show ?thesis unfolding pH_on_string_syntax_def
    by (simp only: pterm_of_oterm.simps)
      (rule pH_proves.Inst[OF pterm_of_preserves_typing[OF assms(1)]
        pterm_of_preserves_typing[OF assms(2)] sp sq prem])
qed

section \<open>Contract for the downstream cross-session theorem\<close>

text \<open>
  For a candidate old-syntax relation R, require Σ; Γ ⊢H A iff
  R holds of the translated A.

  Isabelle representation: pH_string_bridge states this agreement for every Σ,
  Γ, and A.  pH_string_bridge_from_old_syntax reduces it to an old-syntax
  correspondence premise.

  Status: a proved conditional reduction, not an unconditional identification
  of R with the later H_signature_proves.
\<close>

definition pH_string_bridge ::
    "((otype \<Rightarrow> string set) \<Rightarrow> ctx \<Rightarrow> oterm \<Rightarrow> bool) \<Rightarrow> bool" where
  "pH_string_bridge R \<longleftrightarrow>
    (\<forall>\<Sigma> \<Gamma> A. pH_proves \<Sigma> \<Gamma> A \<longleftrightarrow> R \<Sigma> \<Gamma> (pterm_to_oterm A))"

lemma pH_string_bridge_from_old_syntax:
  assumes correspond: "\<And>\<Sigma> \<Gamma> A. pH_on_string_syntax \<Sigma> \<Gamma> A \<longleftrightarrow> R \<Sigma> \<Gamma> A"
  shows "pH_string_bridge R"
proof (unfold pH_string_bridge_def, intro allI)
  fix \<Sigma> \<Gamma> A
  have syntax_eq: "pH_proves \<Sigma> \<Gamma> A \<longleftrightarrow>
      pH_on_string_syntax \<Sigma> \<Gamma> (pterm_to_oterm A)"
    by (rule pH_string_translation_iff)
  have relation_eq: "pH_on_string_syntax \<Sigma> \<Gamma> (pterm_to_oterm A) \<longleftrightarrow>
      R \<Sigma> \<Gamma> (pterm_to_oterm A)"
    by (rule correspond)
  show "pH_proves \<Sigma> \<Gamma> A \<longleftrightarrow> R \<Sigma> \<Gamma> (pterm_to_oterm A)"
  proof
    assume p: "pH_proves \<Sigma> \<Gamma> A"
    have old: "pH_on_string_syntax \<Sigma> \<Gamma> (pterm_to_oterm A)"
      by (rule iffD1[OF syntax_eq p])
    show "R \<Sigma> \<Gamma> (pterm_to_oterm A)" by (rule iffD1[OF relation_eq old])
  next
    assume r: "R \<Sigma> \<Gamma> (pterm_to_oterm A)"
    have old: "pH_on_string_syntax \<Sigma> \<Gamma> (pterm_to_oterm A)"
      by (rule iffD2[OF relation_eq r])
    show "pH_proves \<Sigma> \<Gamma> A" by (rule iffD2[OF syntax_eq old])
  qed
qed

text \<open>
  Σ; Γ ⊢H A in the parametric string instance is to coincide with the
  existing guarded H judgement, not merely unrestricted ⊢H A.

  Isabelle representation: instantiate pH_string_bridge with H_signature_proves
  in a theory importing both sessions.  The proof must identify the two
  signature predicates and use the guarded constructor translations.

  Status: the contract is conditional on that correspondence.  Its
  instantiation is not a theorem asserted by this file.
\<close>

end
