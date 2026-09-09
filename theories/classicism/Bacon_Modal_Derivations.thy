theory Bacon_Modal_Derivations
  imports Bacon_Modal
begin

section \<open>Restricted necessitation and equivalence closure\<close>

text \<open>
  Since \<open>\<box>\<^sub>o A\<close> is defined as \<open>Eq Prop A ObjTrue\<close>, the restricted
  necessitation principle is immediate once the relevant identity with truth has
  already been derived.
\<close>

lemma C_restricted_necessitation:
  assumes "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C \<box>\<^sub>o A"
  using assms by (simp add: ObjBox_def)

lemma H_restricted_necessitation:
  assumes "\<Gamma> \<turnstile>\<^sub>H Eq Prop A ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>H \<box>\<^sub>o A"
  using assms by (simp add: ObjBox_def)

text \<open>
  The bridge from theoremhood of \<open>A\<close> to necessitation of \<open>A\<close> is not the
  definition of box.  What is needed is a way to turn suitable equivalence with
  truth into propositional identity with truth.  The following extension isolates
  the propositional, zero-ary case of Bacon and Dorr's Equivalence rule:

    if \<open>A\<close> and \<open>B\<close> are provably biconditional, infer \<open>A =\<^sub>t B\<close>.

  This is sufficient for necessitation once one has proved \<open>A \<longleftrightarrow>\<^sub>o ObjTrue\<close>.

  We call this explicit rule-extension CE.  Bacon and Dorr use
  ``Propositional Equivalence'' for the rule, but regard it as an alternative
  presentation of Classicism after proving the relevant equivalence theorem.
  The Isabelle inclusion \<open>C_proves \<subseteq> CE_proves\<close> is immediate; the converse
  is now proved downstream by CE_proves_to_C in the separate
  Bacon_C_Presentation_Development session, after the C-only Appendix A proof.
  It is not assumed by this definition.
\<close>

inductive CE_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" ("_ \<turnstile>\<^sub>CE _" [50, 50] 50) where
  C[intro]: "\<Gamma> \<turnstile>\<^sub>C A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
| PropEquivalence[intro]:
    "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o B) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE Eq Prop A B"
| MP[intro]: "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE Imp A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE B"
| Gen[intro]: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp (shift P) Q \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE Imp P (Forall \<sigma> Q)"
| Inst[intro]: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE Imp (Exists \<sigma> P) Q"

lemma CE_proves_formula:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CE_proves.induct)
  case (C \<Gamma> A)
  then show ?case
    by (rule C_proves_formula)
next
  case (PropEquivalence \<Gamma> A B)
  then show ?case
    by auto
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

lemma CE_restricted_necessitation:
  assumes "\<Gamma> \<turnstile>\<^sub>CE Eq Prop A ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>CE \<box>\<^sub>o A"
  using assms by (simp add: ObjBox_def)

lemma CE_necessitation_from_equivalence_to_truth:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>CE \<box>\<^sub>o A"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CE Eq Prop A ObjTrue"
    using assms typed_ObjTrue by (intro CE_proves.PropEquivalence)
  then show ?thesis
    by (rule CE_restricted_necessitation)
qed

lemma CE_lifts_C_box_truth:
  "\<Gamma> \<turnstile>\<^sub>CE \<box>\<^sub>o ObjTrue"
  by (intro CE_proves.C C_proves_modal_box_truth)

text \<open>
  At this stage of the import chain, the sufficient missing theorem for
  unrestricted CE necessitation is:

    if \<open>\<Gamma> \<turnstile>\<^sub>CE A\<close>, then \<open>\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o ObjTrue)\<close>.

  Propositional equivalence closure then immediately yields \<open>\<Gamma> \<turnstile>\<^sub>CE \<box>\<^sub>o A\<close>.
  The later theory \<open>Bacon_Zeta\<close> proves unrestricted necessitation in CEV,
  the vector-rule extension.  Bacon and Dorr's Appendix A proves the stronger
  source result that axiom-based C itself is closed under Equivalence, by showing
  identities between abstractions of theorems and truth.  That Appendix A
  induction is not reconstructed here.
\<close>

text \<open>
  For full S4-style results, the propositional rule above is only the zero-ary
  fragment of the Equivalence rule.  The higher-type cases require the general
  vector form:

    if \<open>F v\<^sub>1 \<dots> v\<^sub>n\<close> and \<open>G v\<^sub>1 \<dots> v\<^sub>n\<close> are provably biconditional,
    infer \<open>F = G\<close>, with the variables \<open>v\<^sub>i\<close> fresh for \<open>F\<close> and \<open>G\<close>.

  Equivalently, one can use Bacon and Dorr's zeta-equivalence rule.  The next
  theory, \<open>Bacon_Zeta\<close>, supplies vector application, prefix shifting, and
  freshness and defines the resulting CEV calculus.  \<open>Bacon_S4\<close> then proves
  the positive K, T, and 4 package in CEV.
\<close>

end
