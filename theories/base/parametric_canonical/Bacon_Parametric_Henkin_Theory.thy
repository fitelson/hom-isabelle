theory Bacon_Parametric_Henkin_Theory
  imports
    Bacon_Parametric_Signature_Development.Bacon_Parametric_H_Soundness
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Local_Derivability
begin

section \<open>Maximal consistent Henkin theories over arbitrary name carriers\<close>

text \<open>
  M ∼ₜ N ⇔ (M =σ N) ∈ T, and [M]ₜ = {N : M ∼ₜ N}.
  Source: Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Proposition 15.4
  and Theorem 15.3, pp. 319–321.

  Isabelle representation: the name type is arbitrary.  We use the shared
  finitary local consequence relation, not a duplicate calculus.  A maximal
  consistent theory is explicitly typed, deductively closed, consistent,
  and negation-complete.  Henkin witnesses are in-signature typed terms.
  The canonical locale specializes the typing context to closed sentences.
  The equality laws use typedness and closure; consistency, negation
  completeness, and witnesses are retained for the later truth construction.

  Status: conditional theory and identity-class infrastructure.  No
  existence theorem or enumeration of the language is used, and
  no canonical semantic model or completeness theorem is asserted.
\<close>

definition pH_deductively_closed ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_deductively_closed \<Sigma> \<Gamma> T \<longleftrightarrow>
    (\<forall>A. pH_set_derivable \<Sigma> \<Gamma> T A \<longrightarrow> A \<in> T)"

definition pH_negation_complete ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_negation_complete \<Sigma> \<Gamma> T \<longleftrightarrow>
    (\<forall>A. pterm_in_language \<Sigma> \<Gamma> A Prop \<longrightarrow> A \<in> T \<or> PNeg A \<in> T)"

definition pH_maximal_consistent ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_maximal_consistent \<Sigma> \<Gamma> T \<longleftrightarrow>
    pH_typed_theory \<Sigma> \<Gamma> T \<and> pH_deductively_closed \<Sigma> \<Gamma> T \<and>
    pH_consistent \<Sigma> \<Gamma> T \<and> pH_negation_complete \<Sigma> \<Gamma> T"

definition pH_Henkin_witnessed ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_Henkin_witnessed \<Sigma> \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> A. pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop \<longrightarrow>
      PExists \<sigma> A \<in> T \<longrightarrow>
      (\<exists>W. pterm_in_language \<Sigma> \<Gamma> W \<sigma> \<and> psubst0 W A \<in> T))"

definition pH_Henkin_theory ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_Henkin_theory \<Sigma> \<Gamma> T \<longleftrightarrow>
    pH_maximal_consistent \<Sigma> \<Gamma> T \<and> pH_Henkin_witnessed \<Sigma> \<Gamma> T"

lemma pH_inst_Eq:
  "psubst0 W (PEq \<sigma> M N) = PEq \<sigma> (psubst0 W M) (psubst0 W N)"
  by (simp only: psubst0_def psubst.simps)

lemma pH_inst_App:
  "psubst0 W (PApp M N) = PApp (psubst0 W M) (psubst0 W N)"
  by (simp only: psubst0_def psubst.simps)

lemma pH_inst_zero: "psubst0 W (PVar 0) = W"
  by (simp add: psubst0_def)

locale pH_closed_Henkin =
  fixes signature :: "'c psignature" and T :: "'c pterm set"
  assumes henkin: "pH_Henkin_theory signature [] T"
begin

lemma pH_member_language:
  assumes "A \<in> T"
  shows "pterm_in_language signature [] A Prop"
  using henkin assms
  unfolding pH_Henkin_theory_def pH_maximal_consistent_def
    pH_typed_theory_def pterm_in_language_def by blast

lemma pH_local_member:
  assumes "pH_set_derivable signature [] T A"
  shows "A \<in> T"
  using henkin assms
  unfolding pH_Henkin_theory_def pH_maximal_consistent_def pH_deductively_closed_def by blast

lemma pH_theorem_member:
  assumes "pH_proves signature [] A"
  shows "A \<in> T"
  by (rule pH_local_member; rule pH_set_Theorem[OF assms])

lemma pH_member_MP:
  assumes a: "A \<in> T" and ab: "PImp A B \<in> T"
  shows "B \<in> T"
proof -
  have la: "pterm_in_language signature [] A Prop" by (rule pH_member_language[OF a])
  have lab: "pterm_in_language signature [] (PImp A B) Prop" by (rule pH_member_language[OF ab])
  have ta: "has_ptype [] A Prop" using la unfolding pterm_in_language_def by (rule conjunct1)
  have sa: "pterm_in_signature signature A" using la unfolding pterm_in_language_def by (rule conjunct2)
  have tab: "has_ptype [] (PImp A B) Prop" using lab unfolding pterm_in_language_def by (rule conjunct1)
  have sab: "pterm_in_signature signature (PImp A B)" using lab unfolding pterm_in_language_def by (rule conjunct2)
  have da: "pH_set_derivable signature [] T A"
    by (rule pH_set_Assumption[OF a ta sa])
  have dab: "pH_set_derivable signature [] T (PImp A B)"
    by (rule pH_set_Assumption[OF ab tab sab])
  show ?thesis by (rule pH_local_member; rule pH_set_MP[OF da dab])
qed

lemma pH_PC_member:
  assumes ty: "has_ptype [] A Prop" and sig: "pterm_in_signature signature A"
    and valid: "\<forall>v. pprop_eval v A"
  shows "A \<in> T"
proof -
  have taut: "pprop_tautology [] A"
    unfolding pprop_tautology_def by (rule conjI[OF ty valid])
  show ?thesis by (rule pH_theorem_member; rule pH_proves.PC[OF taut sig])
qed

section \<open>Identity and formula transport\<close>

text \<open>
  M ∼ₜ N and A[M/x] ∈ T ⇒ A[N/x] ∈ T.  Source: Bacon–Dorr,
  p. 45 n. 64, using Figure 2's LL and β rules.

  Isabelle representation: both representatives are closed terms in the
  signature.  The predicate λx.A mediates transport, and β conversion
  removes its two applications.

  Status: identity substitution at one parameter, including binder-containing
  bodies; not full simultaneous-substitution independence.
\<close>

definition pH_term_eq :: "otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pH_term_eq \<sigma> M N \<longleftrightarrow>
    pterm_in_language signature [] M \<sigma> \<and>
    pterm_in_language signature [] N \<sigma> \<and> PEq \<sigma> M N \<in> T"

definition pH_term_class :: "otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm set" where
  "pH_term_class \<sigma> M = {N. pH_term_eq \<sigma> M N}"

definition pH_term_domain :: "otype \<Rightarrow> 'c pterm set set" where
  "pH_term_domain \<sigma> = {pH_term_class \<sigma> M |M. pterm_in_language signature [] M \<sigma>}"

lemma pH_term_eq_left:
  "pH_term_eq \<sigma> M N \<Longrightarrow> pterm_in_language signature [] M \<sigma>"
  unfolding pH_term_eq_def by (rule conjunct1)

lemma pH_term_eq_right:
  "pH_term_eq \<sigma> M N \<Longrightarrow> pterm_in_language signature [] N \<sigma>"
  unfolding pH_term_eq_def by (elim conjE) assumption

lemma pH_term_eq_member:
  "pH_term_eq \<sigma> M N \<Longrightarrow> PEq \<sigma> M N \<in> T"
  unfolding pH_term_eq_def by (elim conjE) assumption

lemma pH_term_eq_refl:
  assumes lang: "pterm_in_language signature [] M \<sigma>"
  shows "pH_term_eq \<sigma> M M"
proof -
  have ty: "has_ptype [] M \<sigma>" using lang unfolding pterm_in_language_def by (rule conjunct1)
  have sig: "pterm_in_signature signature M" using lang unfolding pterm_in_language_def by (rule conjunct2)
  have mem: "PEq \<sigma> M M \<in> T" by (rule pH_theorem_member; rule pH_proves.Ref[OF ty sig])
  show ?thesis unfolding pH_term_eq_def by (intro conjI lang mem)
qed

lemma pH_biconditional_membership:
  assumes A: "has_ptype [] A Prop" and B: "has_ptype [] B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and proved: "pH_proves signature [] (PObjIff A B)"
  shows "A \<in> T \<longleftrightarrow> B \<in> T"
proof -
  have bic: "PObjIff A B \<in> T" by (rule pH_theorem_member[OF proved])
  have left: "PImp (PObjIff A B) (PImp A B) \<in> T"
  proof (rule pH_PC_member)
    show "has_ptype [] (PImp (PObjIff A B) (PImp A B)) Prop"
      by (intro has_ptype.PImp has_ptype.PConj A B)
    show "pterm_in_signature signature (PImp (PObjIff A B) (PImp A B))"
      by (simp only: pterm_in_signature.simps sa sb)
    show "\<forall>v. pprop_eval v (PImp (PObjIff A B) (PImp A B))"
      by (intro allI) (simp only: pprop_eval.simps; blast)
  qed
  have right: "PImp (PObjIff A B) (PImp B A) \<in> T"
  proof (rule pH_PC_member)
    show "has_ptype [] (PImp (PObjIff A B) (PImp B A)) Prop"
      by (intro has_ptype.PImp has_ptype.PConj A B)
    show "pterm_in_signature signature (PImp (PObjIff A B) (PImp B A))"
      by (simp only: pterm_in_signature.simps sa sb)
    show "\<forall>v. pprop_eval v (PImp (PObjIff A B) (PImp B A))"
      by (intro allI) (simp only: pprop_eval.simps; blast)
  qed
  have ab: "PImp A B \<in> T" by (rule pH_member_MP[OF bic left])
  have ba: "PImp B A \<in> T" by (rule pH_member_MP[OF bic right])
  show ?thesis
  proof
    assume "A \<in> T"
    then show "B \<in> T" by (rule pH_member_MP[OF _ ab])
  next
    assume "B \<in> T"
    then show "A \<in> T" by (rule pH_member_MP[OF _ ba])
  qed
qed

lemma pH_beta_application_membership:
  assumes body: "has_ptype [\<sigma>] A Prop" and arg: "has_ptype [] M \<sigma>"
    and sa: "pterm_in_signature signature A" and sm: "pterm_in_signature signature M"
  shows "PApp (PLam \<sigma> A) M \<in> T \<longleftrightarrow> psubst0 M A \<in> T"
proof -
  have app: "has_ptype [] (PApp (PLam \<sigma> A) M) Prop"
    by (rule has_ptype.PApp[OF has_ptype.PLam[OF body] arg])
  have inst: "has_ptype [] (psubst0 M A) Prop" by (rule psubst0_preserves_typing[OF body arg])
  have s_app: "pterm_in_signature signature (PApp (PLam \<sigma> A) M)" using sa sm by simp
  have s_inst: "pterm_in_signature signature (psubst0 M A)" by (rule psubst0_signature[OF sa sm])
  have step: "pcompatible_step pbeta_contract (PApp (PLam \<sigma> A) M) (psubst0 M A)"
    by (rule pcompatible_step.root[where R=pbeta_contract]; rule pbeta_contract.beta)
  have proved: "pH_proves signature [] (PObjIff (PApp (PLam \<sigma> A) M) (psubst0 M A))"
    by (rule pH_proves.Beta[OF app inst step s_app s_inst])
  show ?thesis by (rule pH_biconditional_membership[OF app inst s_app s_inst proved])
qed

lemma pH_identity_body_transport:
  assumes eq: "pH_term_eq \<sigma> M N" and body: "has_ptype [\<sigma>] A Prop"
    and sa: "pterm_in_signature signature A" and source: "psubst0 M A \<in> T"
  shows "psubst0 N A \<in> T"
proof -
  have lm: "pterm_in_language signature [] M \<sigma>" by (rule pH_term_eq_left[OF eq])
  have ln: "pterm_in_language signature [] N \<sigma>" by (rule pH_term_eq_right[OF eq])
  have mt: "has_ptype [] M \<sigma>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  have nt: "has_ptype [] N \<sigma>" and ns: "pterm_in_signature signature N"
    using ln unfolding pterm_in_language_def by simp_all
  have ft: "has_ptype [] (PLam \<sigma> A) (\<sigma> \<rightarrow>\<^sub>o Prop)" by (rule has_ptype.PLam[OF body])
  have fs: "pterm_in_signature signature (PLam \<sigma> A)" using sa by simp
  have am: "PApp (PLam \<sigma> A) M \<in> T"
    by (rule iffD2[OF pH_beta_application_membership[OF body mt sa ms] source])
  have ll: "PImp (PEq \<sigma> M N) (PImp (PApp (PLam \<sigma> A) M) (PApp (PLam \<sigma> A) N)) \<in> T"
    by (rule pH_theorem_member; rule pH_proves.LL[OF mt nt ft ms ns fs])
  have impl: "PImp (PApp (PLam \<sigma> A) M) (PApp (PLam \<sigma> A) N) \<in> T"
    by (rule pH_member_MP[OF pH_term_eq_member[OF eq] ll])
  have an: "PApp (PLam \<sigma> A) N \<in> T" by (rule pH_member_MP[OF am impl])
  show ?thesis by (rule iffD1[OF pH_beta_application_membership[OF body nt sa ns] an])
qed

section \<open>Equivalence laws for canonical representatives\<close>

text \<open>
  M ∼ₜ M; M ∼ₜ N ⇒ N ∼ₜ M; M ∼ₜ N ∧ N ∼ₜ P ⇒ M ∼ₜ P.
  Source: Bacon–Dorr, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: identity transport uses the predicates
  λx. x = M and λx. M = x.  The classes are sets of closed in-language terms.

  Status: identity-equivalence laws; domain inhabitation and simultaneous
  substitution independence still require their own arguments.
\<close>

lemma pH_term_eq_sym:
  assumes eq: "pH_term_eq \<sigma> M N"
  shows "pH_term_eq \<sigma> N M"
proof -
  have lm: "pterm_in_language signature [] M \<sigma>" by (rule pH_term_eq_left[OF eq])
  have ln: "pterm_in_language signature [] N \<sigma>" by (rule pH_term_eq_right[OF eq])
  have mt: "has_ptype [] M \<sigma>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  let ?A = "PEq \<sigma> (PVar 0) (pshift M)"
  have body: "has_ptype [\<sigma>] ?A Prop"
    by (rule has_ptype.PEq[OF _ pshift_preserves_typing[OF mt]]; rule has_ptype.PVar; simp)
  have sig: "pterm_in_signature signature ?A" using ms by (simp add: pshift_def)
  have ref: "PEq \<sigma> M M \<in> T" by (rule pH_term_eq_member[OF pH_term_eq_refl[OF lm]])
  have source: "psubst0 M ?A \<in> T" using ref by (simp only: pH_inst_Eq pH_inst_zero psubst0_pshift)
  have target: "psubst0 N ?A \<in> T" by (rule pH_identity_body_transport[OF eq body sig source])
  have mem: "PEq \<sigma> N M \<in> T" using target by (simp only: pH_inst_Eq pH_inst_zero psubst0_pshift)
  show ?thesis unfolding pH_term_eq_def by (intro conjI ln lm mem)
qed

lemma pH_term_eq_trans:
  assumes mn: "pH_term_eq \<sigma> M N" and np: "pH_term_eq \<sigma> N P"
  shows "pH_term_eq \<sigma> M P"
proof -
  have lm: "pterm_in_language signature [] M \<sigma>" by (rule pH_term_eq_left[OF mn])
  have lp: "pterm_in_language signature [] P \<sigma>" by (rule pH_term_eq_right[OF np])
  have mt: "has_ptype [] M \<sigma>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  let ?A = "PEq \<sigma> (pshift M) (PVar 0)"
  have body: "has_ptype [\<sigma>] ?A Prop"
    by (rule has_ptype.PEq[OF pshift_preserves_typing[OF mt]]; rule has_ptype.PVar; simp)
  have sig: "pterm_in_signature signature ?A" using ms by (simp add: pshift_def)
  have old: "PEq \<sigma> M N \<in> T" by (rule pH_term_eq_member[OF mn])
  have source: "psubst0 N ?A \<in> T" using old by (simp only: pH_inst_Eq pH_inst_zero psubst0_pshift)
  have target: "psubst0 P ?A \<in> T" by (rule pH_identity_body_transport[OF np body sig source])
  have mem: "PEq \<sigma> M P \<in> T" using target by (simp only: pH_inst_Eq pH_inst_zero psubst0_pshift)
  show ?thesis unfolding pH_term_eq_def by (intro conjI lm lp mem)
qed

lemma pH_term_class_eq_iff:
  assumes lm: "pterm_in_language signature [] M \<sigma>"
    and ln: "pterm_in_language signature [] N \<sigma>"
  shows "pH_term_class \<sigma> M = pH_term_class \<sigma> N \<longleftrightarrow> pH_term_eq \<sigma> M N"
proof
  assume same: "pH_term_class \<sigma> M = pH_term_class \<sigma> N"
  have self: "M \<in> pH_term_class \<sigma> M" using pH_term_eq_refl[OF lm] unfolding pH_term_class_def by simp
  have "M \<in> pH_term_class \<sigma> N" using self by (simp only: same)
  then have nm: "pH_term_eq \<sigma> N M" unfolding pH_term_class_def by simp
  show "pH_term_eq \<sigma> M N" by (rule pH_term_eq_sym[OF nm])
next
  assume mn: "pH_term_eq \<sigma> M N"
  show "pH_term_class \<sigma> M = pH_term_class \<sigma> N"
  proof (rule set_eqI)
    fix P
    show "P \<in> pH_term_class \<sigma> M \<longleftrightarrow> P \<in> pH_term_class \<sigma> N"
      unfolding pH_term_class_def
      using pH_term_eq_trans[OF pH_term_eq_sym[OF mn]]
        pH_term_eq_trans[OF mn] by blast
  qed
qed

section \<open>Application congruence and one-parameter representative independence\<close>

text \<open>
  M ∼ₜ N ⇒ C[M/x] ∼ₜ C[N/x]; hence F ∼ₜ G and A ∼ₜ B ⇒ FA ∼ₜ GB.
  Source: Bacon–Dorr, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.
  Isabelle representation: an identity-valued predicate turns formula
  transport into term-context congruence.  Status: application and one-parameter
  independence are proved; simultaneous substitution remains a later step.
\<close>

lemma pH_term_body_congruence:
  assumes eq: "pH_term_eq \<sigma> M N" and body: "has_ptype [\<sigma>] C \<tau>"
    and sc: "pterm_in_signature signature C"
  shows "pH_term_eq \<tau> (psubst0 M C) (psubst0 N C)"
proof -
  have lm: "pterm_in_language signature [] M \<sigma>" by (rule pH_term_eq_left[OF eq])
  have ln: "pterm_in_language signature [] N \<sigma>" by (rule pH_term_eq_right[OF eq])
  have mt: "has_ptype [] M \<sigma>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  have nt: "has_ptype [] N \<sigma>" and ns: "pterm_in_signature signature N"
    using ln unfolding pterm_in_language_def by simp_all
  have mc: "has_ptype [] (psubst0 M C) \<tau>" by (rule psubst0_preserves_typing[OF body mt])
  have nc: "has_ptype [] (psubst0 N C) \<tau>" by (rule psubst0_preserves_typing[OF body nt])
  have smc: "pterm_in_signature signature (psubst0 M C)" by (rule psubst0_signature[OF sc ms])
  have snc: "pterm_in_signature signature (psubst0 N C)" by (rule psubst0_signature[OF sc ns])
  let ?E = "PEq \<tau> (pshift (psubst0 M C)) C"
  have et: "has_ptype [\<sigma>] ?E Prop" by (rule has_ptype.PEq[OF pshift_preserves_typing[OF mc] body])
  have es: "pterm_in_signature signature ?E" using smc sc by (simp add: pshift_def)
  have ref: "PEq \<tau> (psubst0 M C) (psubst0 M C) \<in> T"
    by (rule pH_theorem_member; rule pH_proves.Ref[OF mc smc])
  have source: "psubst0 M ?E \<in> T" using ref by (simp only: pH_inst_Eq psubst0_pshift)
  have target: "psubst0 N ?E \<in> T" by (rule pH_identity_body_transport[OF eq et es source])
  have mem: "PEq \<tau> (psubst0 M C) (psubst0 N C) \<in> T"
    using target by (simp only: pH_inst_Eq psubst0_pshift)
  show ?thesis unfolding pH_term_eq_def pterm_in_language_def by (intro conjI mc smc nc snc mem)
qed

lemma pH_term_eq_app:
  assumes fg: "pH_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G" and ab: "pH_term_eq \<sigma> A B"
  shows "pH_term_eq \<tau> (PApp F A) (PApp G B)"
proof -
  have lf: "pterm_in_language signature [] F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" by (rule pH_term_eq_left[OF fg])
  have lb: "pterm_in_language signature [] B \<sigma>" by (rule pH_term_eq_right[OF ab])
  have ft: "has_ptype [] F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and fs: "pterm_in_signature signature F"
    using lf unfolding pterm_in_language_def by simp_all
  have bt: "has_ptype [] B \<sigma>" and bs: "pterm_in_signature signature B"
    using lb unfolding pterm_in_language_def by simp_all
  let ?C = "PApp (pshift F) (PVar 0)"
  let ?D = "PApp (PVar 0) (pshift B)"
  have ct: "has_ptype [\<sigma>] ?C \<tau>"
    by (rule has_ptype.PApp[OF pshift_preserves_typing[OF ft]]; rule has_ptype.PVar; simp)
  have dt: "has_ptype [\<sigma> \<rightarrow>\<^sub>o \<tau>] ?D \<tau>"
    by (rule has_ptype.PApp[OF _ pshift_preserves_typing[OF bt]]; rule has_ptype.PVar; simp)
  have cs: "pterm_in_signature signature ?C" using fs by (simp add: pshift_def)
  have ds: "pterm_in_signature signature ?D" using bs by (simp add: pshift_def)
  have first: "pH_term_eq \<tau> (PApp F A) (PApp F B)"
    using pH_term_body_congruence[OF ab ct cs] by (simp only: pH_inst_App pH_inst_zero psubst0_pshift)
  have second: "pH_term_eq \<tau> (PApp F B) (PApp G B)"
    using pH_term_body_congruence[OF fg dt ds] by (simp only: pH_inst_App pH_inst_zero psubst0_pshift)
  show ?thesis by (rule pH_term_eq_trans[OF first second])
qed

end

end
