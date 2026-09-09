theory Bacon_Modal
  imports Bacon_Classicism
begin

section \<open>Modal logicism definitions\<close>

text \<open>
  Bacon and Dorr define broad necessity by propositional identity with truth.
  Here \<open>ObjBox A\<close> represents the object-language formula saying that proposition
  \<open>A\<close> is identical to truth.

  In standard notation the definitions are \<open>\<box>A \<equiv> A =\<^sub>t \<top>\<close>,
  \<open>\<diamond>A \<equiv> \<not>\<box>\<not>A\<close>, and \<open>A \<preceq> B \<equiv> \<box>(A \<longrightarrow> B)\<close>.  The last
  expression is strict implication; it is not the paper's type-indexed
  algebraic order.  Our \<open>\<top>\<close> is the particular \<open>ObjTrue\<close> formula from
  \<open>Bacon_Syntax\<close>.  Bacon and Dorr print a different tautological
  representative.  Interchangeability as an object of type \<open>Prop\<close> requires
  an identity theorem in a suitably strong system.
\<close>

definition ObjBox :: "oterm \<Rightarrow> oterm" ("\<box>\<^sub>o _" [60] 60) where
  "\<box>\<^sub>o A = Eq Prop A ObjTrue"

definition ObjDiamond :: "oterm \<Rightarrow> oterm" ("\<diamond>\<^sub>o _" [60] 60) where
  "\<diamond>\<^sub>o A = Neg (\<box>\<^sub>o (Neg A))"

definition ObjEntails :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infixr "\<preceq>\<^sub>o" 35) where
  "(A \<preceq>\<^sub>o B) = \<box>\<^sub>o (Imp A B)"

definition box_operator :: oterm where
  "box_operator = Lam Prop (\<box>\<^sub>o (Var 0))"

definition diamond_operator :: oterm where
  "diamond_operator = Lam Prop (\<diamond>\<^sub>o (Var 0))"

definition modal_K :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "modal_K A B = Imp (\<box>\<^sub>o (Imp A B)) (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B))"

definition modal_T :: "oterm \<Rightarrow> oterm" where
  "modal_T A = Imp (\<box>\<^sub>o A) A"

definition modal_4 :: "oterm \<Rightarrow> oterm" where
  "modal_4 A = Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (\<box>\<^sub>o A))"

lemma typed_ObjTrue:
  "\<Gamma> \<turnstile> ObjTrue : Prop"
  unfolding ObjTrue_def
  by (intro has_type.Forall has_type.Imp has_type.Var) simp_all

lemma typed_ObjFalse:
  "\<Gamma> \<turnstile> ObjFalse : Prop"
  by (auto simp: ObjFalse_def intro: typed_ObjTrue)

lemma typed_ObjBox:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
  using assms typed_ObjTrue by (auto simp: ObjBox_def)

lemma typed_ObjDiamond:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> \<diamond>\<^sub>o A : Prop"
  using assms by (auto simp: ObjDiamond_def intro: typed_ObjBox)

lemma typed_ObjEntails:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile> (A \<preceq>\<^sub>o B) : Prop"
  using assms by (auto simp: ObjEntails_def intro: typed_ObjBox)

lemma typed_box_operator:
  "\<Gamma> \<turnstile> box_operator : Prop \<rightarrow>\<^sub>o Prop"
  unfolding box_operator_def
  by (intro has_type.Lam typed_ObjBox has_type.Var) simp_all

lemma typed_diamond_operator:
  "\<Gamma> \<turnstile> diamond_operator : Prop \<rightarrow>\<^sub>o Prop"
  unfolding diamond_operator_def
  by (intro has_type.Lam typed_ObjDiamond has_type.Var) simp_all

lemma typed_modal_K:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile> modal_K A B : Prop"
  using assms by (auto simp: modal_K_def intro: typed_ObjBox)

lemma typed_modal_T:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> modal_T A : Prop"
  using assms by (auto simp: modal_T_def intro: typed_ObjBox)

lemma typed_modal_4:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> modal_4 A : Prop"
  using assms by (auto simp: modal_4_def intro: typed_ObjBox)

section \<open>Small derivability sanity checks\<close>

lemma H_proves_reflexive_truth:
  "\<Gamma> \<turnstile>\<^sub>H Eq Prop ObjTrue ObjTrue"
  by (intro H_proves.Ref typed_ObjTrue)

lemma C_proves_reflexive_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue ObjTrue"
  by (intro C_proves.H H_proves_reflexive_truth)

lemma C_proves_modal_box_truth:
  "\<Gamma> \<turnstile>\<^sub>C \<box>\<^sub>o ObjTrue"
  by (simp add: ObjBox_def C_proves_reflexive_truth)

lemma C_proves_boolean_comm_conj:
  "\<Gamma> \<turnstile>\<^sub>C bool_comm_conj"
  by (intro C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)

lemma C_proves_identity_identity:
  "\<Gamma> \<turnstile>\<^sub>C classic_identity_identity \<sigma>"
  by (rule C_proves.IdentityIdentity)

end
