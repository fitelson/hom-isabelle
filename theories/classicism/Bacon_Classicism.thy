theory Bacon_Classicism
  imports Bacon_Abbreviations
begin

section \<open>Classicism\<close>

text \<open>
  This file gives the axiom presentation of Classicism: the smallest extension
  of H containing the Boolean identities and the Classicist identities and
  closed under MP, Gen, and Inst.  The five Classicist
  identity schemas follow Bacon and Dorr's Figure 4: the identity identity,
  absorption and distribution for universal quantification, and absorption and
  distribution for existential quantification.

  We write \<open>\<Gamma> \<turnstile>\<^sub>C A\<close> for theoremhood in this axiom system and
  \<open>\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A\<close> for its MP-based local consequence relation.
  Here \<open>\<Gamma>\<close> is a type context and \<open>\<Delta>\<close> is a list of assumptions.

  Bacon's book, Definition 6.1, officially characterizes C as H closed under
  the Rule of Equivalence, and Theorem 6.1 proves that this agrees with the
  displayed axiom presentation.  The present repository represents the
  propositional and vector forms of that rule in the later CE and CEV calculi.
  The downstream Bacon_C_Presentation_Development session now proves the
  converse reductions CE_proves_to_C and CEV_proves_to_C, using the independent
  C-only Appendix A reconstruction. This foundational definition does not
  import those later theorems. Transfer an earlier CEV result through the
  checked bridge; do not substitute a stronger calculus during the C-only
  proof of that bridge. Literal source-language correspondence and semantic
  completeness remain separate obligations.
\<close>

inductive C_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" ("_ \<turnstile>\<^sub>C _" [50, 50] 50) where
  H[intro]: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
| BooleanIdentity[intro]: "A \<in> set all_boolean_identities \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
| IdentityIdentity[intro]: "\<Gamma> \<turnstile>\<^sub>C classic_identity_identity \<sigma>"
| AbsorbDisjForall[intro]: "\<Gamma> \<turnstile>\<^sub>C classic_absorb_disj_forall \<sigma>"
| DistDisjForall[intro]: "\<Gamma> \<turnstile>\<^sub>C classic_dist_disj_forall \<sigma>"
| AbsorbConjExists[intro]: "\<Gamma> \<turnstile>\<^sub>C classic_absorb_conj_exists \<sigma>"
| DistConjExists[intro]: "\<Gamma> \<turnstile>\<^sub>C classic_dist_conj_exists \<sigma>"
| MP[intro]: "\<Gamma> \<turnstile>\<^sub>C A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C Imp A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C B"
| Gen[intro]: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>C Imp (shift P) Q \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C Imp P (Forall \<sigma> Q)"
| Inst[intro]: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>C Imp P (shift Q) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C Imp (Exists \<sigma> P) Q"

lemma C_proves_formula:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: C_proves.induct)
  case (H \<Gamma> A)
  then show ?case
    by (rule H_proves_formula)
next
  case (BooleanIdentity A \<Gamma>)
  then show ?case
    by (rule typed_boolean_identity)
next
  case (IdentityIdentity \<Gamma> \<sigma>)
  then show ?case
    by (rule typed_classic_identity_identity)
next
  case (AbsorbDisjForall \<Gamma> \<sigma>)
  then show ?case
    by (rule typed_classic_absorb_disj_forall)
next
  case (DistDisjForall \<Gamma> \<sigma>)
  then show ?case
    by (rule typed_classic_dist_disj_forall)
next
  case (AbsorbConjExists \<Gamma> \<sigma>)
  then show ?case
    by (rule typed_classic_absorb_conj_exists)
next
  case (DistConjExists \<Gamma> \<sigma>)
  then show ?case
    by (rule typed_classic_dist_conj_exists)
next
  case (MP \<Gamma> A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  then show ?case
    by auto
next
  case (Inst \<sigma> \<Gamma> P Q)
  then show ?case
    by auto
qed

inductive C_derivable :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>C _" [50, 50, 50] 50) where
  Assumption[intro]: "A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>C A \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
| Derive_MP[intro]: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A B \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C B"

lemma C_derivable_formula:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by (rule C_proves_formula)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  then show ?case
    by (auto elim: has_type.cases)
qed

end
