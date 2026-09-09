theory Bacon_H_Henkin_Equality
  imports Bacon_Classicism.Bacon_Clean_Canonical_Base
begin

section \<open>Identity classes of closed terms in an H Henkin theory\<close>

text \<open>
  M ∼ₜ N ⇔ (M =σ N) ∈ T, and [M]ₜ = {N : M ∼ₜ N}. Bacon–Dorr, Theorem 3.2, p. 45 n.
  64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: H_closed_Henkin fixes a closed H Henkin theory. H_term_eq
  and H_term_class use closed, well-typed representatives; these are identity classes,
  not material-equivalence classes.

  Status: First quotient ingredients; interpretation and model existence are
  constructed in later theories. No Functionality is assumed.
\<close>

locale H_closed_Henkin =
  fixes T :: "oterm set"
  assumes henkin: "H_Henkin_theory [] T"
begin

definition H_term_eq :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_term_eq \<sigma> M N \<longleftrightarrow>
    [] \<turnstile> M : \<sigma> \<and> [] \<turnstile> N : \<sigma> \<and> Eq \<sigma> M N \<in> T"

definition H_term_class :: "otype \<Rightarrow> oterm \<Rightarrow> oterm set" where
  "H_term_class \<sigma> M = {N. H_term_eq \<sigma> M N}"

definition H_term_domain :: "otype \<Rightarrow> oterm set set" where
  "H_term_domain \<sigma> = {H_term_class \<sigma> M |M. [] \<turnstile> M : \<sigma>}"

text \<open>
  Thus \<open>H_term_eq \<sigma> M N\<close> reads \<open>M \<sim>\<^sub>T N\<close> at type
  \<open>\<sigma>\<close>, and \<open>H_term_class \<sigma> M\<close> is \<open>[M]\<^sub>T\<close>.
  Both representatives must be closed and well typed.  The prospective
  domain contains these classes, not functions on lower-type domains.
\<close>

lemma H_term_eq_types:
  "H_term_eq \<sigma> M N \<Longrightarrow> [] \<turnstile> M : \<sigma> \<and> [] \<turnstile> N : \<sigma>"
  by (simp add: H_term_eq_def)

lemma H_term_eq_refl:
  assumes "[] \<turnstile> M : \<sigma>"
  shows "H_term_eq \<sigma> M M"
  using assms H_identity_refl_in[OF H_Henkin_deductively_closed[OF henkin] assms]
  by (simp add: H_term_eq_def)

subsection \<open>Transport through a formula with one parameter\<close>

text \<open>
  M ∼ₜ N and A[M/x] ∈ T ⇒ A[N/x] ∈ T. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: Leibniz's law applies to λx.A, then β conversion removes
  the applications. Slot zero represents the parameter even when A contains further
  binders.

  Status: Substitution of identical parameters, not extensional identification of
  functions.
\<close>

lemma H_biconditional_membership:
  assumes A_type: "[] \<turnstile> A : Prop"
    and B_type: "[] \<turnstile> B : Prop"
    and bicond: "[] \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  shows "A \<in> T \<longleftrightarrow> B \<in> T"
proof -
  have bicond_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
    using henkin bicond by (rule H_Henkin_contains_theorems)
  have AB_type: "[] \<turnstile> Imp A B : Prop"
    and BA_type: "[] \<turnstile> Imp B A : Prop"
    using A_type B_type by auto
  have "Imp A B \<in> T \<and> Imp B A \<in> T"
    using bicond_in H_Henkin_conj_mem_iff[OF henkin AB_type BA_type] by blast
  then show ?thesis
    using H_Henkin_closed_under_MP[OF henkin] by blast
qed

lemma H_beta_application_membership:
  assumes body: "[\<sigma>] \<turnstile> A : Prop"
    and arg: "[] \<turnstile> M : \<sigma>"
  shows "App (Lam \<sigma> A) M \<in> T \<longleftrightarrow> subst0 M A \<in> T"
proof -
  have app_type: "[] \<turnstile> App (Lam \<sigma> A) M : Prop"
    using body arg by auto
  have subst_type: "[] \<turnstile> subst0 M A : Prop"
    using body arg by (rule subst0_preserves_typing)
  have step: "compatible_step beta_contract (App (Lam \<sigma> A) M) (subst0 M A)"
    by (intro compatible_step.root beta_contract.beta)
  have bicond: "[] \<turnstile>\<^sub>H (App (Lam \<sigma> A) M \<longleftrightarrow>\<^sub>o subst0 M A)"
    using app_type subst_type step by (rule H_proves.Beta)
  show ?thesis
    using app_type subst_type bicond by (rule H_biconditional_membership)
qed

text \<open>
  If \<open>M = N\<close> belongs to T, a formula \<open>A(x)\<close> true of M is true
  of N.  The parameter is de Bruijn slot zero.  Leibniz's law applies to
  \<open>λx. A(x)\<close>; β conversion then removes the two applications.
  A may itself contain binders.  This is substitution of identical
  parameters, not the extensional identification of arbitrary functions.
\<close>

lemma H_identity_body_transport:
  assumes eq: "H_term_eq \<sigma> M N"
    and body: "[\<sigma>] \<turnstile> A : Prop"
    and source: "subst0 M A \<in> T"
  shows "subst0 N A \<in> T"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>"
    and N_type: "[] \<turnstile> N : \<sigma>"
    and eq_in: "Eq \<sigma> M N \<in> T"
    using eq unfolding H_term_eq_def by auto
  have F_type: "[] \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body by auto
  have app_M: "App (Lam \<sigma> A) M \<in> T"
    using H_beta_application_membership[OF body M_type] source by blast
  have app_N: "App (Lam \<sigma> A) N \<in> T"
    using H_Henkin_typed_theory[OF henkin]
      H_Henkin_deductively_closed[OF henkin] eq_in app_M M_type N_type F_type
    by (rule H_identity_subst_in)
  show ?thesis
    using H_beta_application_membership[OF body N_type] app_N by blast
qed

subsection \<open>Equivalence and truth of representatives\<close>

text \<open>
  M ∼ₜ M; M ∼ₜ N ⇒ N ∼ₜ M; M ∼ₜ N ∧ N ∼ₜ P ⇒ M ∼ₜ P. Bacon–Dorr, Theorem 3.2, p. 45 n.
  64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: The H identity lemmas establish an equivalence relation and
  preserve formula truth when representatives are changed.

  Status: Typed closed terms only; these facts precede the semantic truth lemma.
\<close>

lemma H_term_eq_sym:
  assumes eq: "H_term_eq \<sigma> M N"
  shows "H_term_eq \<sigma> N M"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>"
    and N_type: "[] \<turnstile> N : \<sigma>"
    using eq unfolding H_term_eq_def by auto
  have shift_type: "[\<sigma>] \<turnstile> shift M : \<sigma>"
    using M_type by (rule weakening_front)
  have body: "[\<sigma>] \<turnstile> Eq \<sigma> (Var 0) (shift M) : Prop"
    using shift_type by auto
  have ref: "Eq \<sigma> M M \<in> T"
    using H_term_eq_refl[OF M_type] unfolding H_term_eq_def by blast
  have source: "subst0 M (Eq \<sigma> (Var 0) (shift M)) \<in> T"
    using ref by (simp add: subst0_def)
  have "subst0 N (Eq \<sigma> (Var 0) (shift M)) \<in> T"
    using eq body source by (rule H_identity_body_transport)
  then have "Eq \<sigma> N M \<in> T"
    by (simp add: subst0_def)
  then show ?thesis
    using M_type N_type unfolding H_term_eq_def by blast
qed

lemma H_term_eq_trans:
  assumes MN: "H_term_eq \<sigma> M N"
    and NP: "H_term_eq \<sigma> N P"
  shows "H_term_eq \<sigma> M P"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>"
    and P_type: "[] \<turnstile> P : \<sigma>"
    and MN_in: "Eq \<sigma> M N \<in> T"
    using MN NP unfolding H_term_eq_def by auto
  have shift_type: "[\<sigma>] \<turnstile> shift M : \<sigma>"
    using M_type by (rule weakening_front)
  have body: "[\<sigma>] \<turnstile> Eq \<sigma> (shift M) (Var 0) : Prop"
    using shift_type by auto
  have source: "subst0 N (Eq \<sigma> (shift M) (Var 0)) \<in> T"
    using MN_in by (simp add: subst0_def)
  have "subst0 P (Eq \<sigma> (shift M) (Var 0)) \<in> T"
    using NP body source by (rule H_identity_body_transport)
  then have "Eq \<sigma> M P \<in> T"
    by (simp add: subst0_def)
  then show ?thesis
    using M_type P_type unfolding H_term_eq_def by blast
qed

lemma H_term_eq_prop_truth_iff:
  assumes eq: "H_term_eq Prop M N"
  shows "M \<in> T \<longleftrightarrow> N \<in> T"
proof -
  have body: "[Prop] \<turnstile> Var 0 : Prop" by simp
  have forward: "M \<in> T \<Longrightarrow> N \<in> T"
    using H_identity_body_transport[OF eq body] by (simp add: subst0_def)
  have backward: "N \<in> T \<Longrightarrow> M \<in> T"
    using H_identity_body_transport[OF H_term_eq_sym[OF eq] body]
    by (simp add: subst0_def)
  show ?thesis using forward backward by blast
qed

subsection \<open>Beta-eta conversion implies identity at every type\<close>

text \<open>
  M ≡βη N ⇒ M ∼ₜ N. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp.
  320–321.

  Isabelle representation: The conversion and H identity machinery applies at each
  object type, including functional types.

  Status: Identity follows from conversion, not from agreement on all arguments.
\<close>

lemma H_beta_eta_eq_right:
  assumes conv: "beta_eta_equiv \<Gamma> \<sigma> M N"
    and L_type: "\<Gamma> \<turnstile> L : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop (Eq \<sigma> L M) (Eq \<sigma> L N)"
  using conv L_type
proof (induction arbitrary: L rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  then show ?case by auto
next
  case (Beta \<Gamma> M \<tau> N)
  then show ?case
    by (intro beta_eta_equiv.Beta) (auto intro: compatible_step.Eq_right)
next
  case (Eta \<Gamma> M \<tau> N)
  then show ?case
    by (intro beta_eta_equiv.Eta) (auto intro: compatible_step.Eq_right)
next
  case (Sym \<Gamma> \<tau> M N)
  then show ?case by (meson beta_eta_equiv.Sym)
next
  case (Trans \<Gamma> \<tau> M N P)
  then show ?case by (meson beta_eta_equiv.Trans)
qed

lemma H_term_eq_beta_eta:
  assumes conv: "beta_eta_equiv [] \<sigma> M N"
  shows "H_term_eq \<sigma> M N"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>"
    and N_type: "[] \<turnstile> N : \<sigma>"
    using beta_eta_equiv_types[OF conv] by auto
  have MM_type: "[] \<turnstile> Eq \<sigma> M M : Prop"
    and MN_type: "[] \<turnstile> Eq \<sigma> M N : Prop"
    using M_type N_type by auto
  have eq_conv: "beta_eta_equiv [] Prop (Eq \<sigma> M M) (Eq \<sigma> M N)"
    using conv M_type by (rule H_beta_eta_eq_right)
  have bicond: "[] \<turnstile>\<^sub>H (Eq \<sigma> M M \<longleftrightarrow>\<^sub>o Eq \<sigma> M N)"
    using eq_conv by (rule H_beta_eta_equiv)
  have ref: "Eq \<sigma> M M \<in> T"
    using H_term_eq_refl[OF M_type] unfolding H_term_eq_def by blast
  have "Eq \<sigma> M N \<in> T"
    using H_biconditional_membership[OF MM_type MN_type bicond] ref by blast
  then show ?thesis
    using M_type N_type unfolding H_term_eq_def by blast
qed

subsection \<open>Application is independent of representatives\<close>

text \<open>
  F ∼ₜ F′ and A ∼ₜ A′ ⇒ FA ∼ₜ F′A′. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: Application congruence allows [F]ₜ · [A]ₜ to be defined as
  [FA]ₜ.

  Status: This is well-defined application on classes, not local functionality.
\<close>

lemma H_term_eq_app_right:
  assumes F_type: "[] \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and eq: "H_term_eq \<sigma> M N"
  shows "H_term_eq \<tau> (App F M) (App F N)"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>" and N_type: "[] \<turnstile> N : \<sigma>"
    using eq unfolding H_term_eq_def by auto
  have FM_type: "[] \<turnstile> App F M : \<tau>"
    and FN_type: "[] \<turnstile> App F N : \<tau>"
    using F_type M_type N_type by auto
  have shift_F: "[\<sigma>] \<turnstile> shift F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F_type by (rule weakening_front)
  have shift_FM: "[\<sigma>] \<turnstile> shift (App F M) : \<tau>"
    using FM_type by (rule weakening_front)
  have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
    by simp
  have app_type: "[\<sigma>] \<turnstile> App (shift F) (Var 0) : \<tau>"
    using shift_F var_type by (rule has_type.App)
  let ?A = "Eq \<tau> (shift (App F M)) (App (shift F) (Var 0))"
  have body: "[\<sigma>] \<turnstile> ?A : Prop"
    using shift_FM app_type by (rule has_type.Eq)
  have ref: "Eq \<tau> (App F M) (App F M) \<in> T"
    using H_term_eq_refl[OF FM_type] unfolding H_term_eq_def by blast
  have source: "subst0 M ?A \<in> T"
    using ref by (simp add: subst0_def)
  have "subst0 N ?A \<in> T"
    using eq body source by (rule H_identity_body_transport)
  then have "Eq \<tau> (App F M) (App F N) \<in> T"
    by (simp add: subst0_def)
  then show ?thesis
    using FM_type FN_type unfolding H_term_eq_def by blast
qed

lemma H_term_eq_app_left:
  assumes eq: "H_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
    and M_type: "[] \<turnstile> M : \<sigma>"
  shows "H_term_eq \<tau> (App F M) (App G M)"
proof -
  have F_type: "[] \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and G_type: "[] \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using eq unfolding H_term_eq_def by auto
  have FM_type: "[] \<turnstile> App F M : \<tau>"
    and GM_type: "[] \<turnstile> App G M : \<tau>"
    using F_type G_type M_type by auto
  have shift_M: "[\<sigma> \<rightarrow>\<^sub>o \<tau>] \<turnstile> shift M : \<sigma>"
    using M_type by (rule weakening_front)
  have shift_FM: "[\<sigma> \<rightarrow>\<^sub>o \<tau>] \<turnstile> shift (App F M) : \<tau>"
    using FM_type by (rule weakening_front)
  have var_type: "[\<sigma> \<rightarrow>\<^sub>o \<tau>] \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by simp
  have app_type: "[\<sigma> \<rightarrow>\<^sub>o \<tau>] \<turnstile> App (Var 0) (shift M) : \<tau>"
    using var_type shift_M by (rule has_type.App)
  let ?A = "Eq \<tau> (shift (App F M)) (App (Var 0) (shift M))"
  have body: "[\<sigma> \<rightarrow>\<^sub>o \<tau>] \<turnstile> ?A : Prop"
    using shift_FM app_type by (rule has_type.Eq)
  have ref: "Eq \<tau> (App F M) (App F M) \<in> T"
    using H_term_eq_refl[OF FM_type] unfolding H_term_eq_def by blast
  have source: "subst0 F ?A \<in> T"
    using ref by (simp add: subst0_def)
  have "subst0 G ?A \<in> T"
    using eq body source by (rule H_identity_body_transport)
  then have "Eq \<tau> (App F M) (App G M) \<in> T"
    by (simp add: subst0_def)
  then show ?thesis
    using FM_type GM_type unfolding H_term_eq_def by blast
qed

lemma H_term_eq_app_cong:
  assumes FG: "H_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
    and MN: "H_term_eq \<sigma> M N"
  shows "H_term_eq \<tau> (App F M) (App G N)"
proof -
  have M_type: "[] \<turnstile> M : \<sigma>"
    using MN unfolding H_term_eq_def by blast
  have G_type: "[] \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using FG unfolding H_term_eq_def by blast
  have left: "H_term_eq \<tau> (App F M) (App G M)"
    using FG M_type by (rule H_term_eq_app_left)
  have right: "H_term_eq \<tau> (App G M) (App G N)"
    using G_type MN by (rule H_term_eq_app_right)
  show ?thesis using left right by (rule H_term_eq_trans)
qed

subsection \<open>Elementary facts about identity classes\<close>

text \<open>
  [M]ₜ = [N]ₜ ⇔ M ∼ₜ N; each typed domain has a representative. Bacon–Dorr, Theorem
  3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Classes are HOL sets of closed terms. Nonemptiness uses the
  unrestricted typed-string stock.

  Status: Class algebra only; smaller signatures need their own language-extension
  argument.
\<close>

lemma H_term_class_self:
  "[] \<turnstile> M : \<sigma> \<Longrightarrow> M \<in> H_term_class \<sigma> M"
  using H_term_eq_refl unfolding H_term_class_def by blast

lemma H_term_class_eq_iff:
  assumes "[] \<turnstile> M : \<sigma>" and "[] \<turnstile> N : \<sigma>"
  shows "H_term_class \<sigma> M = H_term_class \<sigma> N \<longleftrightarrow> H_term_eq \<sigma> M N"
  using H_term_class_self[OF assms(2)] H_term_eq_sym H_term_eq_trans
  unfolding H_term_class_def by blast

lemma H_term_domain_nonempty:
  "H_term_domain \<sigma> \<noteq> {}"
proof -
  have "[] \<turnstile> Const '''' \<sigma> : \<sigma>" by auto
  then have "H_term_class \<sigma> (Const '''' \<sigma>) \<in> H_term_domain \<sigma>"
    unfolding H_term_domain_def by blast
  then show ?thesis by blast
qed

text \<open>
  Nonemptiness here uses the existing unrestricted stock of typed constants.
  For a specified smaller signature, the completeness construction must
  first provide an expanded signature with witnesses.  A full interpretation
  additionally uses simultaneous-substitution congruence, representative
  independence, the quantifier truth lemma, and the BBK model conditions,
  supplied in the subsequent exact-H directories.
\<close>

end
end
