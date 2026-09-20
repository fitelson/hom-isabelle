theory Bacon_PP_Intensionality
  imports 
    "Bacon_Classicism.Bacon_S4"
begin

section \<open>Intensionality is a theorem of CEV\<close>

text \<open>
  Bacon--Dorr, \emph{Classicism} \<open>\<section>1.5\<close> (p.\ 17), states \<^bold>\<open>Intensionality\<close>

  \begin{center}
  \<open>\<box>\<forall>z\<^sub>1\<dots>z\<^sub>n (X z\<^sub>1\<dots>z\<^sub>n \<longleftrightarrow> Y z\<^sub>1\<dots>z\<^sub>n) \<longrightarrow> X = Y\<close>
  \end{center}

  and proves it a theorem of Classicism.  Footnote 18 (p.\ 16) records that \<open>C\<close> thereby
  includes Modalized Functionality.  This theory carries out the \<open>\<section>1.5\<close> derivation in
  the unary case, inside repo-\<open>CEV\<close>.

  The route.  \<open>\<zeta>\<close>-Equivalence is theorem-level, so it cannot be applied to the
  hypothesis \<open>\<forall>z. X z \<longleftrightarrow> Y z\<close> directly.  The trick is to build that very formula into
  both sides as a conjunct, which makes the pointwise biconditional an \<open>H\<close>-theorem; then
  use \<open>\<box>C\<close>, i.e.\ \<open>C = \<top>\<close>, to replace the conjunct by \<open>\<top>\<close> via Leibniz, and finally
  discharge \<open>\<top>\<close>.

  Stage one, below, is the discharge step, which also validates the beta bookkeeping.
\<close>

subsection \<open>The builder\<close>

definition intens_builder :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_builder \<sigma> X =
    Lam Prop (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))"

text \<open>
  Under the two binders \<open>Var 0\<close> is the argument of type \<open>\<sigma>\<close> and \<open>Var 1\<close> is the
  conjunct of type \<open>Prop\<close>; \<open>X\<close> is shifted past both.
\<close>

lemma typed_intens_builder:
  assumes "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> intens_builder \<sigma> X : Prop \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
  unfolding intens_builder_def
proof (intro has_type.Lam has_type.Conj has_type.App)
  have "[\<sigma>, Prop] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>, Prop]) X : \<sigma> \<rightarrow>\<^sub>o Prop"
    using assms by (rule shift_by_preserves_typing)
  then show "\<sigma> # Prop # \<Gamma> \<turnstile> shift_by 2 X : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (simp add: numeral_2_eq_2)
  show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
qed

subsection \<open>The guarded operator, and the Leibniz predicate\<close>

text \<open>
  \<open>intens_conj \<sigma> X c\<close> is \<open>\<lambda>z. (X z \<and> c)\<close>, built at the meta level so that no beta step is
  needed to name it.  \<open>intens_pred\<close> is the object-level predicate in \<open>c\<close> that Leibniz
  will be applied to; one beta step turns \<open>intens_pred \<sigma> X Y c\<close> into the identity
  between the two guarded operators.
\<close>

definition intens_conj :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_conj \<sigma> X c =
    Lam \<sigma> (Conj (App (shift X) (Var 0)) (shift c))"

definition intens_pred :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_pred \<sigma> X Y =
    Lam Prop
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
        (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))"

lemma typed_intens_conj:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and c: "\<Gamma> \<turnstile> c : Prop"
  shows "\<Gamma> \<turnstile> intens_conj \<sigma> X c : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding intens_conj_def
proof (intro has_type.Lam has_type.Conj has_type.App)
  have "[\<sigma>] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>]) X : \<sigma> \<rightarrow>\<^sub>o Prop"
    using X by (rule shift_by_preserves_typing)
  then show "\<sigma> # \<Gamma> \<turnstile> shift X : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (simp add: shift_by_1)
  show "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  have "[\<sigma>] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>]) c : Prop"
    using c by (rule shift_by_preserves_typing)
  then show "\<sigma> # \<Gamma> \<turnstile> shift c : Prop"
    by (simp add: shift_by_1)
qed

text \<open>
  The beta computation.  This is the step Goodman's notes flag as the project's
  single largest source of corrected errors, so it is isolated and checked rather
  than performed inline.
\<close>

lemma subst_rename_to_rename:
  assumes "\<And>n. s (\<rho> n) = Var (\<tau> n)"
  shows "subst s (rename \<rho> M) = rename \<tau> M"
  using assms
proof (induction M arbitrary: s \<rho> \<tau>)
  case (Lam \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed (simp_all add: assms)

lemma subst_lift_shift_by_2:
  "subst (lift_subst (case_nat c Var)) (rename (shift_ren 2 0) M)
    = shift M"
proof -
  have "\<And>n. lift_subst (case_nat c Var) (shift_ren 2 0 n) = Var (Suc n)"
    by (simp add: shift_ren_def)
  then have "subst (lift_subst (case_nat c Var))
      (rename (shift_ren 2 0) M) = rename Suc M"
    by (rule subst_rename_to_rename)
  then show ?thesis by (simp add: shift_def)
qed

lemma intens_pred_beta:
  "beta_contract (App (intens_pred \<sigma> X Y) c)
    (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c))"
proof -
  have "beta_contract
      (App (Lam Prop
        (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
          (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))) c)
      (subst0 c
        (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
          (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1)))))"
    by (rule beta_contract.beta)
  moreover have
    "subst0 c
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
        (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))
      = Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c)"
    by (simp add: subst0_def intens_conj_def shift_by_def
        subst_lift_shift_by_2 shift_def)
  ultimately show ?thesis
    unfolding intens_pred_def by simp
qed

subsection \<open>Two more substitution facts\<close>

lemma subst0_var0_shift_by_2:
  "subst0 (Var 0) (shift_by 2 M) = shift M"
proof -
  have "\<And>n. case_nat (Var 0) Var (shift_ren 2 0 n) = Var (Suc n)"
    by (simp add: shift_ren_def)
  then have "subst (case_nat (Var 0) Var) (rename (shift_ren 2 0) M)
      = rename Suc M"
    by (rule subst_rename_to_rename)
  then show ?thesis
    by (simp add: subst0_def shift_by_def shift_def)
qed

lemma subst0_var0_lift_ren_Suc:
  "subst0 (Var 0) (rename (lift_ren Suc) M) = M"
  unfolding subst0_def
proof (rule subst_rename_inverse)
  fix n show "case_nat (Var 0) Var (lift_ren Suc n) = Var n"
    by (cases n) simp_all
qed

lemma shift_ObjTrue[simp]: "shift ObjTrue = ObjTrue"
  by (simp add: ObjTrue_def shift_def)

subsection \<open>Typing helpers\<close>

lemma typed_shift_ctx:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<sigma> # \<Gamma> \<turnstile> shift M : \<tau>"
proof -
  have "[\<sigma>] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>]) M : \<tau>"
    using assms by (rule shift_by_preserves_typing)
  then show ?thesis by (simp add: shift_by_1)
qed

lemma typed_var0: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
  by (rule has_type.Var) (simp add: lookup_def)

lemma typed_shift_app:
  assumes "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<sigma> # \<Gamma> \<turnstile> App (shift F) (Var 0) : Prop"
  using typed_shift_ctx[OF assms] typed_var0 by (rule has_type.App)

lemma typed_intens_conj_body:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop" and c: "\<Gamma> \<turnstile> c : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile> Conj (App (shift X) (Var 0)) (shift c) : Prop"
  using typed_shift_app[OF X] typed_shift_ctx[OF c]
  by (rule has_type.Conj)

lemma typed_shift_intens_conj_app:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop" and c: "\<Gamma> \<turnstile> c : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile> App (shift (intens_conj \<sigma> X c)) (Var 0) : Prop"
  using typed_intens_conj[OF X c] by (rule typed_shift_app)

subsection \<open>Cheap biconditional transitivity through identity\<close>

text \<open>
  Expanding biconditional transitivity as one propositional tautology makes the
  evaluator normalize six nested implications.  The identity route is smaller:
  zero-ary \<open>\<zeta>\<close>-Equivalence turns biconditionals into proposition identities,
  identity transitivity composes them, and Leibniz at the proposition identity
  function recovers the two implications.
\<close>

lemma CEV_eq_prop_imp:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq_AB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
proof -
  let ?IA = "App prop_id A"
  let ?IB = "App prop_id B"
  have id_type: "\<Gamma> \<turnstile> prop_id : Prop \<rightarrow>\<^sub>o Prop"
    by (rule typed_prop_id)
  have IA_type: "\<Gamma> \<turnstile> ?IA : Prop"
    using id_type A_type by (rule has_type.App)
  have IB_type: "\<Gamma> \<turnstile> ?IB : Prop"
    using id_type B_type by (rule has_type.App)
  have ll:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq Prop A B) (Imp ?IA ?IB)"
    using A_type B_type id_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have IA_IB: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?IA ?IB"
    using eq_AB ll by (rule CEV_proves.MP)
  have local_B: "CEV_from \<Gamma> A B"
  proof -
    have local_A: "CEV_from \<Gamma> A A"
      by (rule CEV_from.Assumption[OF A_type])
    have local_IA: "CEV_from \<Gamma> A ?IA"
      using local_A
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF CEV_imp_app_prop_id[OF A_type]]])
    have local_IB: "CEV_from \<Gamma> A ?IB"
      using local_IA
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF IA_IB]])
    show ?thesis
      using local_IB
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF CEV_app_prop_id_imp[OF B_type]]])
  qed
  show ?thesis
    using local_B A_type by (rule CEV_from_deduction)
qed

lemma CEV_eq_prop_biconditional:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq_AB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have A_B: "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
    using A_type B_type eq_AB by (rule CEV_eq_prop_imp)
  have eq_BA: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop B A"
    using A_type B_type eq_AB by (rule CEV_eq_sym_from)
  have B_A: "\<Gamma> \<turnstile>\<^sub>CEV Imp B A"
    using B_type A_type eq_BA by (rule CEV_eq_prop_imp)
  show ?thesis
    using A_B B_A by (rule CEV_conj_intro)
qed

lemma CEV_biconditional_trans:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
    and BC: "\<Gamma> \<turnstile>\<^sub>CEV (B \<longleftrightarrow>\<^sub>o C)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o C)"
proof -
  have eq_AB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
    using A_type B_type AB by (rule CEV_zeroary_equivalence)
  have eq_BC: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop B C"
    using B_type C_type BC by (rule CEV_zeroary_equivalence)
  have eq_AC: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A C"
    using A_type B_type C_type eq_AB eq_BC by (rule CEV_eq_trans_from)
  show ?thesis
    using A_type C_type eq_AC by (rule CEV_eq_prop_biconditional)
qed

lemma CEV_biconditional_sym:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (B \<longleftrightarrow>\<^sub>o A)"
proof -
  have eq_AB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
    using A_type B_type AB by (rule CEV_zeroary_equivalence)
  have eq_BA: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop B A"
    using A_type B_type eq_AB by (rule CEV_eq_sym_from)
  show ?thesis
    using B_type A_type eq_BA by (rule CEV_eq_prop_biconditional)
qed

lemma CEV_guarded_imp:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and C_AB: "\<Gamma> \<turnstile>\<^sub>CEV Imp C (Imp A B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A C) (Conj B C)"
proof -
  let ?AC = "Conj A C"
  let ?BC = "Conj B C"
  have AC_type: "\<Gamma> \<turnstile> ?AC : Prop"
    using A_type C_type by (rule has_type.Conj)
  have BC_type: "\<Gamma> \<turnstile> ?BC : Prop"
    using B_type C_type by (rule has_type.Conj)
  have intro_BC: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp C ?BC)"
  proof -
    have "prop_tautology \<Gamma> (Imp B (Imp C ?BC))"
      unfolding prop_tautology_def
      using B_type C_type BC_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have local_BC: "CEV_from \<Gamma> ?AC ?BC"
  proof -
    have local_AC: "CEV_from \<Gamma> ?AC ?AC"
      by (rule CEV_from.Assumption[OF AC_type])
    have local_A: "CEV_from \<Gamma> ?AC A"
      using local_AC
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[
            OF CEV_conj_left_imp[OF A_type C_type]]])
    have local_C: "CEV_from \<Gamma> ?AC C"
      using local_AC
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[
            OF CEV_conj_right_imp[OF A_type C_type]]])
    have local_AB: "CEV_from \<Gamma> ?AC (Imp A B)"
      using local_C
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF C_AB]])
    have local_B: "CEV_from \<Gamma> ?AC B"
      using local_A local_AB by (rule CEV_from.MP)
    have local_C_BC: "CEV_from \<Gamma> ?AC (Imp C ?BC)"
      using local_B
      by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF intro_BC]])
    show ?thesis
      using local_C local_C_BC by (rule CEV_from.MP)
  qed
  show ?thesis
    using local_BC AC_type by (rule CEV_from_deduction)
qed

lemma CEV_guarded_biconditional:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and C_AB: "\<Gamma> \<turnstile>\<^sub>CEV Imp C (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (Conj A C \<longleftrightarrow>\<^sub>o Conj B C)"
proof -
  have iff_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have iff_left:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B)"
  proof -
    have "prop_tautology \<Gamma>
        (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
      unfolding prop_tautology_def
      using A_type B_type iff_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have iff_right:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A)"
  proof -
    have "prop_tautology \<Gamma>
        (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
      unfolding prop_tautology_def
      using A_type B_type iff_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have C_A_B: "\<Gamma> \<turnstile>\<^sub>CEV Imp C (Imp A B)"
  proof -
    have local: "CEV_from \<Gamma> C (Imp A B)"
    proof -
      have local_C: "CEV_from \<Gamma> C C"
        by (rule CEV_from.Assumption[OF C_type])
      have local_iff: "CEV_from \<Gamma> C (A \<longleftrightarrow>\<^sub>o B)"
        using local_C
        by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF C_AB]])
      show ?thesis
        using local_iff
        by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF iff_left]])
    qed
    show ?thesis
      using local C_type by (rule CEV_from_deduction)
  qed
  have C_B_A: "\<Gamma> \<turnstile>\<^sub>CEV Imp C (Imp B A)"
  proof -
    have local: "CEV_from \<Gamma> C (Imp B A)"
    proof -
      have local_C: "CEV_from \<Gamma> C C"
        by (rule CEV_from.Assumption[OF C_type])
      have local_iff: "CEV_from \<Gamma> C (A \<longleftrightarrow>\<^sub>o B)"
        using local_C
        by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF C_AB]])
      show ?thesis
        using local_iff
        by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF iff_right]])
    qed
    show ?thesis
      using local C_type by (rule CEV_from_deduction)
  qed
  have left:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A C) (Conj B C)"
    using A_type B_type C_type C_A_B by (rule CEV_guarded_imp)
  have right:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj B C) (Conj A C)"
    using B_type A_type C_type C_B_A by (rule CEV_guarded_imp)
  show ?thesis
    using left right by (rule CEV_conj_intro)
qed

lemma intens_conj_shift_app_beta:
  "compatible_step beta_contract
    (App (shift (intens_conj \<sigma> X c)) (Var 0))
    (Conj (App (shift X) (Var 0)) (shift c))"
proof -
  let ?body = "Conj (App (shift X) (Var 0)) (shift c)"
  have step: "compatible_step beta_contract
      (App
        (Lam \<sigma>
          (rename (lift_ren Suc) ?body))
        (Var 0))
      (subst0 (Var 0)
        (rename (lift_ren Suc) ?body))"
    by (intro compatible_step.root beta_contract.beta)
  have subst: "subst0 (Var 0) (rename (lift_ren Suc) ?body) = ?body"
    by (rule subst0_var0_lift_ren_Suc)
  have step': "compatible_step beta_contract
      (App (Lam \<sigma> (rename (lift_ren Suc) ?body)) (Var 0))
      ?body"
    using step subst by simp
  have shifted:
      "shift (intens_conj \<sigma> X c) =
        Lam \<sigma> (rename (lift_ren Suc) ?body)"
    unfolding intens_conj_def shift_def by simp
  show ?thesis
    using step' shifted by simp
qed

lemma CEV_intens_conj_shift_app_beta:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and c_type: "\<Gamma> \<turnstile> c : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift (intens_conj \<sigma> X c)) (Var 0)
      \<longleftrightarrow>\<^sub>o
     Conj (App (shift X) (Var 0)) (shift c))"
proof -
  have app_type:
      "\<sigma> # \<Gamma> \<turnstile>
        App (shift (intens_conj \<sigma> X c)) (Var 0) : Prop"
    using X_type c_type by (rule typed_shift_intens_conj_app)
  have body_type:
      "\<sigma> # \<Gamma> \<turnstile>
        Conj (App (shift X) (Var 0)) (shift c) : Prop"
    using X_type c_type by (rule typed_intens_conj_body)
  show ?thesis
    using app_type body_type intens_conj_shift_app_beta
    by (rule CEV_beta_step)
qed

subsection \<open>The guarded \<open>\<zeta>\<close>-Equivalence step\<close>

definition intens_condition ::
    "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_condition \<sigma> X Y =
    Forall \<sigma>
      (App (shift X) (Var 0) \<longleftrightarrow>\<^sub>o
       App (shift Y) (Var 0))"

lemma typed_intens_condition:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> intens_condition \<sigma> X Y : Prop"
  unfolding intens_condition_def
  using typed_shift_app[OF X_type] typed_shift_app[OF Y_type]
  by (intro has_type.Forall has_type.Conj has_type.Imp)

lemma CEV_intens_condition_UI:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (intens_condition \<sigma> X Y))
      (App (shift X) (Var 0) \<longleftrightarrow>\<^sub>o
       App (shift Y) (Var 0))"
proof -
  let ?body =
    "App (shift X) (Var 0) \<longleftrightarrow>\<^sub>o
     App (shift Y) (Var 0)"
  have C_type: "\<Gamma> \<turnstile> intens_condition \<sigma> X Y : Prop"
    using X_type Y_type by (rule typed_intens_condition)
  have shifted_C_type:
      "\<sigma> # \<Gamma> \<turnstile> shift (intens_condition \<sigma> X Y) : Prop"
    using C_type by (rule typed_shift_ctx)
  have shifted_C:
      "shift (intens_condition \<sigma> X Y) =
        Forall \<sigma> (rename (lift_ren Suc) ?body)"
    unfolding intens_condition_def shift_def by simp
  have forall_type:
      "\<sigma> # \<Gamma> \<turnstile>
        Forall \<sigma> (rename (lift_ren Suc) ?body) : Prop"
    using shifted_C_type shifted_C by simp
  have lifted_body_type:
      "\<sigma> # \<sigma> # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?body : Prop"
    using forall_type by (cases rule: has_type.cases) auto
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule typed_var0)
  have ui:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Forall \<sigma> (rename (lift_ren Suc) ?body))
          (subst0 (Var 0) (rename (lift_ren Suc) ?body))"
    using lifted_body_type var_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have subst:
      "subst0 (Var 0) (rename (lift_ren Suc) ?body) = ?body"
    by (rule subst0_var0_lift_ren_Suc)
  show ?thesis
    using ui shifted_C subst by simp
qed

theorem CEV_intens_guarded_eq:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (intens_conj \<sigma> X (intens_condition \<sigma> X Y))
      (intens_conj \<sigma> Y (intens_condition \<sigma> X Y))"
proof -
  let ?C = "intens_condition \<sigma> X Y"
  let ?A = "App (shift X) (Var 0)"
  let ?B = "App (shift Y) (Var 0)"
  let ?SC = "shift ?C"
  let ?AX = "App (shift (intens_conj \<sigma> X ?C)) (Var 0)"
  let ?BY = "App (shift (intens_conj \<sigma> Y ?C)) (Var 0)"
  let ?bodyX = "Conj ?A ?SC"
  let ?bodyY = "Conj ?B ?SC"
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using X_type Y_type by (rule typed_intens_condition)
  have A_type: "\<sigma> # \<Gamma> \<turnstile> ?A : Prop"
    using X_type by (rule typed_shift_app)
  have B_type: "\<sigma> # \<Gamma> \<turnstile> ?B : Prop"
    using Y_type by (rule typed_shift_app)
  have SC_type: "\<sigma> # \<Gamma> \<turnstile> ?SC : Prop"
    using C_type by (rule typed_shift_ctx)
  have bodyX_type: "\<sigma> # \<Gamma> \<turnstile> ?bodyX : Prop"
    using A_type SC_type by (rule has_type.Conj)
  have bodyY_type: "\<sigma> # \<Gamma> \<turnstile> ?bodyY : Prop"
    using B_type SC_type by (rule has_type.Conj)
  have AX_type: "\<sigma> # \<Gamma> \<turnstile> ?AX : Prop"
    using X_type C_type by (rule typed_shift_intens_conj_app)
  have BY_type: "\<sigma> # \<Gamma> \<turnstile> ?BY : Prop"
    using Y_type C_type by (rule typed_shift_intens_conj_app)
  have ui:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp ?SC (?A \<longleftrightarrow>\<^sub>o ?B)"
    using X_type Y_type by (rule CEV_intens_condition_UI)
  have guarded:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?bodyX \<longleftrightarrow>\<^sub>o ?bodyY)"
    using A_type B_type SC_type ui by (rule CEV_guarded_biconditional)
  have beta_X:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?AX \<longleftrightarrow>\<^sub>o ?bodyX)"
    using X_type C_type by (rule CEV_intens_conj_shift_app_beta)
  have beta_Y:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?BY \<longleftrightarrow>\<^sub>o ?bodyY)"
    using Y_type C_type by (rule CEV_intens_conj_shift_app_beta)
  have beta_Y_sym:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?bodyY \<longleftrightarrow>\<^sub>o ?BY)"
    using BY_type bodyY_type beta_Y by (rule CEV_biconditional_sym)
  have AX_bodyY:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?AX \<longleftrightarrow>\<^sub>o ?bodyY)"
    using AX_type bodyX_type bodyY_type beta_X guarded
    by (rule CEV_biconditional_trans)
  have pointwise:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?AX \<longleftrightarrow>\<^sub>o ?BY)"
    using AX_type bodyY_type BY_type AX_bodyY beta_Y_sym
    by (rule CEV_biconditional_trans)
  show ?thesis
    using typed_intens_conj[OF X_type C_type]
      typed_intens_conj[OF Y_type C_type] pointwise
    by (rule CEV_unary_equivalence)
qed

subsection \<open>Replacing the guard by truth\<close>

lemma typed_intens_pred:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> intens_pred \<sigma> X Y : Prop \<rightarrow>\<^sub>o Prop"
proof -
  let ?LX =
    "Lam \<sigma>
      (Conj (App (shift_by 2 X) (Var 0)) (Var 1))"
  let ?LY =
    "Lam \<sigma>
      (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))"
  have LX_type:
      "Prop # \<Gamma> \<turnstile> ?LX : \<sigma> \<rightarrow>\<^sub>o Prop"
  proof (intro has_type.Lam has_type.Conj has_type.App)
    have "[\<sigma>, Prop] @ \<Gamma> \<turnstile>
        shift_by (length [\<sigma>, Prop]) X : \<sigma> \<rightarrow>\<^sub>o Prop"
      using X_type by (rule shift_by_preserves_typing)
    then show "\<sigma> # Prop # \<Gamma> \<turnstile>
        shift_by 2 X : \<sigma> \<rightarrow>\<^sub>o Prop"
      by (simp add: numeral_2_eq_2)
    show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 0 : \<sigma>"
      by (rule has_type.Var) (simp add: lookup_def)
    show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
      by (rule has_type.Var) (simp add: lookup_def)
  qed
  have LY_type:
      "Prop # \<Gamma> \<turnstile> ?LY : \<sigma> \<rightarrow>\<^sub>o Prop"
  proof (intro has_type.Lam has_type.Conj has_type.App)
    have "[\<sigma>, Prop] @ \<Gamma> \<turnstile>
        shift_by (length [\<sigma>, Prop]) Y : \<sigma> \<rightarrow>\<^sub>o Prop"
      using Y_type by (rule shift_by_preserves_typing)
    then show "\<sigma> # Prop # \<Gamma> \<turnstile>
        shift_by 2 Y : \<sigma> \<rightarrow>\<^sub>o Prop"
      by (simp add: numeral_2_eq_2)
    show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 0 : \<sigma>"
      by (rule has_type.Var) (simp add: lookup_def)
    show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
      by (rule has_type.Var) (simp add: lookup_def)
  qed
  have eq_type:
      "Prop # \<Gamma> \<turnstile>
        Eq (\<sigma> \<rightarrow>\<^sub>o Prop) ?LX ?LY : Prop"
    using LX_type LY_type by (rule has_type.Eq)
  show ?thesis
    unfolding intens_pred_def
    using eq_type by (rule has_type.Lam)
qed

lemma CEV_intens_pred_beta:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
    and c_type: "\<Gamma> \<turnstile> c : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App (intens_pred \<sigma> X Y) c
      \<longleftrightarrow>\<^sub>o
     Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
       (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c))"
proof -
  have pred_type:
      "\<Gamma> \<turnstile> intens_pred \<sigma> X Y : Prop \<rightarrow>\<^sub>o Prop"
    using X_type Y_type by (rule typed_intens_pred)
  have app_type:
      "\<Gamma> \<turnstile> App (intens_pred \<sigma> X Y) c : Prop"
    using pred_type c_type by (rule has_type.App)
  have Xc_type:
      "\<Gamma> \<turnstile> intens_conj \<sigma> X c : \<sigma> \<rightarrow>\<^sub>o Prop"
    using X_type c_type by (rule typed_intens_conj)
  have Yc_type:
      "\<Gamma> \<turnstile> intens_conj \<sigma> Y c : \<sigma> \<rightarrow>\<^sub>o Prop"
    using Y_type c_type by (rule typed_intens_conj)
  have eq_type:
      "\<Gamma> \<turnstile>
        Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c) : Prop"
    using Xc_type Yc_type by (rule has_type.Eq)
  have step:
      "compatible_step beta_contract
        (App (intens_pred \<sigma> X Y) c)
        (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c))"
    using intens_pred_beta by (rule compatible_step.root)
  show ?thesis
    using app_type eq_type step by (rule CEV_beta_step)
qed

lemma CEV_intens_conj_true_eq:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (intens_conj \<sigma> X ObjTrue) X"
proof -
  let ?A = "App (shift X) (Var 0)"
  let ?GX = "intens_conj \<sigma> X ObjTrue"
  let ?appGX = "App (shift ?GX) (Var 0)"
  let ?body = "Conj ?A ObjTrue"
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have A_type: "\<sigma> # \<Gamma> \<turnstile> ?A : Prop"
    using X_type by (rule typed_shift_app)
  have appGX_type: "\<sigma> # \<Gamma> \<turnstile> ?appGX : Prop"
    using X_type true_type by (rule typed_shift_intens_conj_app)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> ?body : Prop"
    using A_type typed_ObjTrue by (rule has_type.Conj)
  have beta:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?appGX \<longleftrightarrow>\<^sub>o ?body)"
  proof -
    have raw:
        "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
          (?appGX \<longleftrightarrow>\<^sub>o
           Conj ?A (shift ObjTrue))"
      using X_type true_type
      by (rule CEV_intens_conj_shift_app_beta)
    then show ?thesis by simp
  qed
  have discharge:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV (?body \<longleftrightarrow>\<^sub>o ?A)"
  proof -
    have true_type': "\<sigma> # \<Gamma> \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    have left: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp ?body ?A"
      using A_type true_type' by (rule CEV_conj_left_imp)
    have intro:
        "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
          Imp ?A (Imp ObjTrue ?body)"
    proof -
      have "prop_tautology (\<sigma> # \<Gamma>)
          (Imp ?A (Imp ObjTrue ?body))"
        unfolding prop_tautology_def
        using A_type true_type' body_type by auto
      then show ?thesis by (rule CEV_prop_tautology)
    qed
    have local_body: "CEV_from (\<sigma> # \<Gamma>) ?A ?body"
    proof -
      have local_A: "CEV_from (\<sigma> # \<Gamma>) ?A ?A"
        by (rule CEV_from.Assumption[OF A_type])
      have local_true_imp:
          "CEV_from (\<sigma> # \<Gamma>) ?A (Imp ObjTrue ?body)"
        using local_A
        by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF intro]])
      have local_true: "CEV_from (\<sigma> # \<Gamma>) ?A ObjTrue"
        by (rule CEV_from.Theorem[OF CEV_proves_ObjTrue])
      show ?thesis
        using local_true local_true_imp by (rule CEV_from.MP)
    qed
    have right: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp ?A ?body"
      using local_body A_type by (rule CEV_from_deduction)
    show ?thesis
      using left right by (rule CEV_conj_intro)
  qed
  have pointwise:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        (?appGX \<longleftrightarrow>\<^sub>o ?A)"
    using appGX_type body_type A_type beta discharge
    by (rule CEV_biconditional_trans)
  show ?thesis
    using typed_intens_conj[OF X_type true_type] X_type pointwise
    by (rule CEV_unary_equivalence)
qed

lemma CEV_intens_guarded_true_from_box:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "CEV_from \<Gamma> (\<box>\<^sub>o (intens_condition \<sigma> X Y))
    (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (intens_conj \<sigma> X ObjTrue)
      (intens_conj \<sigma> Y ObjTrue))"
proof -
  let ?C = "intens_condition \<sigma> X Y"
  let ?Pred = "intens_pred \<sigma> X Y"
  let ?appC = "App ?Pred ?C"
  let ?appT = "App ?Pred ObjTrue"
  let ?eqC =
    "Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (intens_conj \<sigma> X ?C) (intens_conj \<sigma> Y ?C)"
  let ?eqT =
    "Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (intens_conj \<sigma> X ObjTrue) (intens_conj \<sigma> Y ObjTrue)"
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using X_type Y_type by (rule typed_intens_condition)
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have pred_type: "\<Gamma> \<turnstile> ?Pred : Prop \<rightarrow>\<^sub>o Prop"
    using X_type Y_type by (rule typed_intens_pred)
  have appC_type: "\<Gamma> \<turnstile> ?appC : Prop"
    using pred_type C_type by (rule has_type.App)
  have appT_type: "\<Gamma> \<turnstile> ?appT : Prop"
    using pred_type true_type by (rule has_type.App)
  have eqC_type: "\<Gamma> \<turnstile> ?eqC : Prop"
    using typed_intens_conj[OF X_type C_type]
      typed_intens_conj[OF Y_type C_type]
    by (rule has_type.Eq)
  have eqT_type: "\<Gamma> \<turnstile> ?eqT : Prop"
    using typed_intens_conj[OF X_type true_type]
      typed_intens_conj[OF Y_type true_type]
    by (rule has_type.Eq)
  have guarded_eq: "\<Gamma> \<turnstile>\<^sub>CEV ?eqC"
    using X_type Y_type by (rule CEV_intens_guarded_eq)
  have beta_C: "\<Gamma> \<turnstile>\<^sub>CEV (?appC \<longleftrightarrow>\<^sub>o ?eqC)"
    using X_type Y_type C_type by (rule CEV_intens_pred_beta)
  have eqC_appC: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?eqC ?appC"
    using appC_type eqC_type beta_C by (rule CEV_beta_right_imp)
  have appC: "\<Gamma> \<turnstile>\<^sub>CEV ?appC"
    using guarded_eq eqC_appC by (rule CEV_proves.MP)
  have beta_T: "\<Gamma> \<turnstile>\<^sub>CEV (?appT \<longleftrightarrow>\<^sub>o ?eqT)"
    using X_type Y_type true_type by (rule CEV_intens_pred_beta)
  have appT_eqT: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?appT ?eqT"
    using appT_type eqT_type beta_T by (rule CEV_beta_left_imp)
  have ll:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq Prop ?C ObjTrue) (Imp ?appC ?appT)"
    using C_type true_type pred_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?C : Prop"
    using C_type by (rule typed_ObjBox)
  have ll_box:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (\<box>\<^sub>o ?C) (Imp ?appC ?appT)"
    using ll by (simp add: ObjBox_def)
  have local_box: "CEV_from \<Gamma> (\<box>\<^sub>o ?C) (\<box>\<^sub>o ?C)"
    by (rule CEV_from.Assumption[OF box_type])
  have local_appC_appT:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) (Imp ?appC ?appT)"
    using local_box
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF ll_box]])
  have local_appC: "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?appC"
    by (rule CEV_from.Theorem[OF appC])
  have local_appT: "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?appT"
    using local_appC local_appC_appT by (rule CEV_from.MP)
  show ?thesis
    using local_appT
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF appT_eqT]])
qed

subsection \<open>Unary Intensionality\<close>

theorem CEV_unary_intensionality:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (\<box>\<^sub>o (intens_condition \<sigma> X Y))
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X Y)"
proof -
  let ?C = "intens_condition \<sigma> X Y"
  let ?GX = "intens_conj \<sigma> X ObjTrue"
  let ?GY = "intens_conj \<sigma> Y ObjTrue"
  let ?E_X_GX = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X ?GX"
  let ?E_GX_GY = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) ?GX ?GY"
  let ?E_X_GY = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X ?GY"
  let ?E_GY_Y = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) ?GY Y"
  let ?E_X_Y = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X Y"
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using X_type Y_type by (rule typed_intens_condition)
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?C : Prop"
    using C_type by (rule typed_ObjBox)
  have GX_type: "\<Gamma> \<turnstile> ?GX : \<sigma> \<rightarrow>\<^sub>o Prop"
    using X_type true_type by (rule typed_intens_conj)
  have GY_type: "\<Gamma> \<turnstile> ?GY : \<sigma> \<rightarrow>\<^sub>o Prop"
    using Y_type true_type by (rule typed_intens_conj)
  have GX_X: "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (\<sigma> \<rightarrow>\<^sub>o Prop) ?GX X"
    using X_type by (rule CEV_intens_conj_true_eq)
  have X_GX: "\<Gamma> \<turnstile>\<^sub>CEV ?E_X_GX"
    using GX_type X_type GX_X by (rule CEV_eq_sym_from)
  have GY_Y: "\<Gamma> \<turnstile>\<^sub>CEV ?E_GY_Y"
    using Y_type by (rule CEV_intens_conj_true_eq)
  have local_GX_GY:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?E_GX_GY"
    using X_type Y_type by (rule CEV_intens_guarded_true_from_box)
  have trans1:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?E_X_GX (Imp ?E_GX_GY ?E_X_GY)"
    using X_type GX_type GY_type by (rule CEV_eq_trans)
  have mid_to_X_GY:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E_GX_GY ?E_X_GY"
    using X_GX trans1 by (rule CEV_proves.MP)
  have local_X_GY:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?E_X_GY"
    using local_GX_GY
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF mid_to_X_GY]])
  have trans2:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?E_X_GY (Imp ?E_GY_Y ?E_X_Y)"
    using X_type GY_type Y_type by (rule CEV_eq_trans)
  have local_GY_Y_to_X_Y:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) (Imp ?E_GY_Y ?E_X_Y)"
    using local_X_GY
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF trans2]])
  have local_GY_Y:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?E_GY_Y"
    by (rule CEV_from.Theorem[OF GY_Y])
  have local_X_Y:
      "CEV_from \<Gamma> (\<box>\<^sub>o ?C) ?E_X_Y"
    using local_GY_Y local_GY_Y_to_X_Y by (rule CEV_from.MP)
  show ?thesis
    using local_X_Y box_type by (rule CEV_from_deduction)
qed

text \<open>
  This is Bacon--Dorr's unary Intensionality theorem inside repository \<open>CEV\<close>.
  The proof uses theorem-level \<open>\<zeta>\<close>-Equivalence only on the guarded pair, transports
  the guard along \<open>\<box>C\<close> by Leibniz, and then removes the truth conjunct.  No
  contextual Equivalence rule is used.
\<close>

end
