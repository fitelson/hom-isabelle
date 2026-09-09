theory Bacon_S4
  imports Bacon_Conversion
begin

section \<open>Modal schema derivations\<close>

text \<open>
  This theory proves in CEV the positive S4 principles K, T, and 4, together
  with theorem necessitation.  In standard notation these are
  \<open>\<box>(A \<longrightarrow> B) \<longrightarrow> (\<box>A \<longrightarrow> \<box>B)\<close>, \<open>\<box>A \<longrightarrow> A\<close>, and
  \<open>\<box>A \<longrightarrow> \<box>\<box>A\<close>.

  The auxiliary relation \<open>CEV_from \<Gamma> A B\<close> permits only the displayed
  assumption, CEV theorems, and modus ponens.  Its deduction theorem therefore
  does not apply Equivalence or necessitation beneath an undischarged
  assumption.  The final package does not prove the converse source claim that
  the propositional modal fragment is exactly S4, nor does it yet reduce CEV
  derivations to the axiom presentation \<open>C_proves\<close>.
\<close>

lemma subst_rename_inverse:
  assumes "\<And>n. s (\<rho> n) = Var n"
  shows "subst s (rename \<rho> M) = M"
  using assms
proof (induction M arbitrary: s \<rho>)
  case (Lam \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case
    by simp
next
  case (Forall \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case
    by simp
next
  case (Exists \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case
    by simp
qed (simp_all add: assms)

lemma subst0_shift[simp]:
  "subst0 N (shift M) = M"
  unfolding subst0_def shift_def
  by (rule subst_rename_inverse) simp

lemma subst_case_nat_shift[simp]:
  "subst (case_nat N Var) (shift M) = M"
  using subst0_shift[of N M] by (simp add: subst0_def)

inductive CEV_from :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  Assumption[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> CEV_from \<Gamma> A A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> CEV_from \<Gamma> A B"
| MP[intro]: "CEV_from \<Gamma> A B \<Longrightarrow>
    CEV_from \<Gamma> A (Imp B C) \<Longrightarrow> CEV_from \<Gamma> A C"

lemma CEV_from_formula:
  assumes "CEV_from \<Gamma> A B"
  shows "\<Gamma> \<turnstile> B : Prop"
  using assms
proof (induction rule: CEV_from.induct)
  case (Assumption \<Gamma> A)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> B A)
  then show ?case
    by (rule CEV_proves_formula)
next
  case (MP \<Gamma> A B C)
  then show ?case
    by (auto elim: has_type.cases)
qed

lemma CEV_from_deduction:
  assumes "CEV_from \<Gamma> A B"
  shows "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp A B"
  using assms
proof (induction rule: CEV_from.induct)
  case Assumption
  then show ?case
    by (intro CEV_prop_tautology prop_tautology_imp_self)
next
  case Theorem
  show ?case
    by (rule CEV_imp_of_right_theorem[OF Theorem.prems Theorem.hyps])
next
  case (MP \<Gamma> A B C)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using MP.hyps(1) by (rule CEV_from_formula)
  have imp_type: "\<Gamma> \<turnstile> Imp B C : Prop"
    using MP.hyps(2) by (rule CEV_from_formula)
  have C_type: "\<Gamma> \<turnstile> C : Prop"
    using imp_type by (auto elim: has_type.cases)
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
    unfolding prop_tautology_def
    using MP.prems B_type C_type imp_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
    by (rule CEV_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A (Imp B C)) (Imp A C)"
    by (rule CEV_proves.MP[OF MP.IH(1)[OF MP.prems]])
  then show ?case
    by (rule CEV_proves.MP[OF MP.IH(2)[OF MP.prems]])
qed

lemma CEV_from_local_MP:
  assumes "CEV_from \<Gamma> A B"
    and "CEV_from \<Gamma> A (Imp B C)"
  shows "CEV_from \<Gamma> A C"
  using assms by (rule CEV_from.MP)

lemma CEV_taut_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B A)"
proof -
  have "prop_tautology \<Gamma> (Imp A (Imp B A))"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj_left_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) A"
proof -
  have "prop_tautology \<Gamma> (Imp (Conj A B) A)"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj_right_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) B"
proof -
  have "prop_tautology \<Gamma> (Imp (Conj A B) B)"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_uncurry_conj:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<Gamma> \<turnstile> R : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj P Q) R"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Imp Q R)"
proof -
  have imp_type: "\<Gamma> \<turnstile> Imp (Conj P Q) R : Prop"
    using assms(1) assms(2) assms(3) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp (Conj P Q) R) (Imp P (Imp Q R)))"
    unfolding prop_tautology_def
    using assms(1) assms(2) assms(3) imp_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp (Conj P Q) R) (Imp P (Imp Q R))"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(4)])
qed

definition prop_id :: oterm where
  "prop_id = Lam Prop (Var 0)"

lemma typed_prop_id:
  "\<Gamma> \<turnstile> prop_id : Prop \<rightarrow>\<^sub>o Prop"
  unfolding prop_id_def by auto

lemma CEV_beta_left_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
proof -
  have AB_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    unfolding prop_tautology_def
    using assms(1,2) AB_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B)"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(3)])
qed

lemma CEV_beta_right_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp B A"
proof -
  have AB_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    unfolding prop_tautology_def
    using assms(1,2) AB_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A)"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(3)])
qed

lemma CEV_beta_prop_id:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App prop_id A \<longleftrightarrow>\<^sub>o A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  have step: "compatible_step beta_contract (App prop_id A) A"
  proof -
    have "beta_contract (App (Lam Prop (Var 0)) A) (subst0 A (Var 0))"
      by (rule beta_contract.beta)
    then show ?thesis
      unfolding prop_id_def subst0_def by auto
  qed
  show ?thesis
    using app_type assms step by (rule CEV_beta_step)
qed

lemma CEV_app_prop_id_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (App prop_id A) A"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  show ?thesis
    using app_type assms CEV_beta_prop_id[OF assms]
    by (rule CEV_beta_left_imp)
qed

lemma CEV_imp_app_prop_id:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A (App prop_id A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  show ?thesis
    using app_type assms CEV_beta_prop_id[OF assms]
    by (rule CEV_beta_right_imp)
qed

lemma CEV_prop_id_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>CEV App prop_id ObjTrue"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjTrue (App prop_id ObjTrue)"
    using true_type by (rule CEV_imp_app_prop_id)
  then show ?thesis
    by (rule CEV_proves.MP[OF CEV_proves_ObjTrue])
qed

lemma CEV_eq_sym:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
proof -
  let ?F = "Lam \<sigma> (Eq \<sigma> (Var 0) (shift M))"
  have shifted_M_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    using assms(1) by (rule weakening_front)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (Var 0) (shift M) : Prop"
    using shifted_M_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_M_type: "\<Gamma> \<turnstile> App ?F M : Prop"
    using F_type assms(1) by auto
  have app_N_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type assms(2) by auto
  have ref_M: "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> M M"
    using assms(1) by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have beta_M: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F M \<longleftrightarrow>\<^sub>o Eq \<sigma> M M)"
  proof -
    have target_type: "\<Gamma> \<turnstile> Eq \<sigma> M M : Prop"
      using assms(1) by auto
    have step: "compatible_step beta_contract (App ?F M) (Eq \<sigma> M M)"
    proof -
      have "compatible_step beta_contract (App ?F M)
          (subst0 M (Eq \<sigma> (Var 0) (shift M)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_M_type target_type step by (rule CEV_beta_step)
  qed
  have app_M: "\<Gamma> \<turnstile>\<^sub>CEV App ?F M"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M M) (App ?F M)"
      using app_M_type CEV_proves_formula[OF ref_M] beta_M
      by (rule CEV_beta_right_imp)
    then show ?thesis
      by (rule CEV_proves.MP[OF ref_M])
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))"
    using assms(1,2) F_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have local_N: "CEV_from \<Gamma> (Eq \<sigma> M N) (App ?F N)"
  proof -
    have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
      using assms by auto
    have local_E: "CEV_from \<Gamma> (Eq \<sigma> M N) (Eq \<sigma> M N)"
      by (intro CEV_from.Assumption E_type)
    have local_ll: "CEV_from \<Gamma> (Eq \<sigma> M N)
        (Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N)))"
      by (intro CEV_from.Theorem ll)
    have local_imp: "CEV_from \<Gamma> (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))"
      by (rule CEV_from.MP[OF local_E local_ll])
    have local_app_M: "CEV_from \<Gamma> (Eq \<sigma> M N) (App ?F M)"
      by (intro CEV_from.Theorem app_M)
    show ?thesis
      by (rule CEV_from.MP[OF local_app_M local_imp])
  qed
  have local_sym: "CEV_from \<Gamma> (Eq \<sigma> M N) (Eq \<sigma> N M)"
  proof -
    have target_type: "\<Gamma> \<turnstile> Eq \<sigma> N M : Prop"
      using assms by auto
    have beta_N: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F N \<longleftrightarrow>\<^sub>o Eq \<sigma> N M)"
    proof -
      have step: "compatible_step beta_contract (App ?F N) (Eq \<sigma> N M)"
      proof -
        have "compatible_step beta_contract (App ?F N)
            (subst0 N (Eq \<sigma> (Var 0) (shift M)))"
          by (intro compatible_step.root beta_contract.beta)
        then show ?thesis
          by (simp add: subst0_def)
      qed
      show ?thesis
        using app_N_type target_type step by (rule CEV_beta_step)
    qed
    have imp_sym: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?F N) (Eq \<sigma> N M)"
      using app_N_type target_type beta_N by (rule CEV_beta_left_imp)
    have local_imp_sym: "CEV_from \<Gamma> (Eq \<sigma> M N) (Imp (App ?F N) (Eq \<sigma> N M))"
      by (intro CEV_from.Theorem imp_sym)
    have "CEV_from \<Gamma> (Eq \<sigma> M N) (App ?F N)"
      by (rule local_N)
    then show ?thesis
      by (rule CEV_from.MP[OF _ local_imp_sym])
  qed
  have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using assms by auto
  from local_sym E_type show ?thesis
    by (rule CEV_from_deduction)
qed

lemma CEV_eq_sym_from:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> M N"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> N M"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
    using assms(1,2) by (rule CEV_eq_sym)
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(3)])
qed

lemma CEV_eq_trans:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> P : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
proof -
  let ?E_MN = "Eq \<sigma> M N"
  let ?E_NP = "Eq \<sigma> N P"
  let ?E_MP = "Eq \<sigma> M P"
  let ?C = "Conj ?E_MN ?E_NP"
  let ?F = "Lam \<sigma> (Eq \<sigma> (shift M) (Var 0))"
  have shifted_M_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    using assms(1) by (rule weakening_front)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (shift M) (Var 0) : Prop"
    using shifted_M_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_N_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type assms(2) by auto
  have app_P_type: "\<Gamma> \<turnstile> App ?F P : Prop"
    using F_type assms(3) by auto
  have E_MN_type: "\<Gamma> \<turnstile> ?E_MN : Prop"
    using assms(1,2) by auto
  have E_NP_type: "\<Gamma> \<turnstile> ?E_NP : Prop"
    using assms(2,3) by auto
  have E_MP_type: "\<Gamma> \<turnstile> ?E_MP : Prop"
    using assms(1,3) by auto
  have beta_N: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F N \<longleftrightarrow>\<^sub>o ?E_MN)"
  proof -
    have step: "compatible_step beta_contract (App ?F N) ?E_MN"
    proof -
      have "compatible_step beta_contract (App ?F N)
          (subst0 N (Eq \<sigma> (shift M) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_N_type E_MN_type step by (rule CEV_beta_step)
  qed
  have beta_P: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F P \<longleftrightarrow>\<^sub>o ?E_MP)"
  proof -
    have step: "compatible_step beta_contract (App ?F P) ?E_MP"
    proof -
      have "compatible_step beta_contract (App ?F P)
          (subst0 P (Eq \<sigma> (shift M) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_P_type E_MP_type step by (rule CEV_beta_step)
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E_NP (Imp (App ?F N) (App ?F P))"
    using assms(2,3) F_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have local_MP: "CEV_from \<Gamma> ?C ?E_MP"
  proof -
    have C_type: "\<Gamma> \<turnstile> ?C : Prop"
      using E_MN_type E_NP_type by auto
    have local_C: "CEV_from \<Gamma> ?C ?C"
      by (intro CEV_from.Assumption C_type)
    have left_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?E_MN"
      using E_MN_type E_NP_type by (rule CEV_conj_left_imp)
    have right_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?E_NP"
      using E_MN_type E_NP_type by (rule CEV_conj_right_imp)
    have local_MN: "CEV_from \<Gamma> ?C ?E_MN"
      by (rule CEV_from.MP[OF local_C CEV_from.Theorem[OF left_imp]])
    have local_NP: "CEV_from \<Gamma> ?C ?E_NP"
      by (rule CEV_from.MP[OF local_C CEV_from.Theorem[OF right_imp]])
    have imp_MN_app_N: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E_MN (App ?F N)"
      using app_N_type E_MN_type beta_N by (rule CEV_beta_right_imp)
    have local_app_N: "CEV_from \<Gamma> ?C (App ?F N)"
      by (rule CEV_from.MP[OF local_MN CEV_from.Theorem[OF imp_MN_app_N]])
    have local_app_imp: "CEV_from \<Gamma> ?C (Imp (App ?F N) (App ?F P))"
      by (rule CEV_from.MP[OF local_NP CEV_from.Theorem[OF ll]])
    have local_app_P: "CEV_from \<Gamma> ?C (App ?F P)"
      by (rule CEV_from.MP[OF local_app_N local_app_imp])
    have imp_app_P_MP: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?F P) ?E_MP"
      using app_P_type E_MP_type beta_P by (rule CEV_beta_left_imp)
    show ?thesis
      by (rule CEV_from.MP[OF local_app_P CEV_from.Theorem[OF imp_app_P_MP]])
  qed
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?E_MP"
  proof (rule CEV_from_deduction[OF local_MP])
    show "\<Gamma> \<turnstile> ?C : Prop"
      using E_MN_type E_NP_type by auto
  qed
  then show ?thesis
    by (rule CEV_uncurry_conj[OF E_MN_type E_NP_type E_MP_type])
qed

lemma CEV_eq_trans_from:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> P : \<sigma>"
    and "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> M N"
    and "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> N P"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> M P"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
    using assms(1) assms(2) assms(3) by (rule CEV_eq_trans)
  then have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> N P) (Eq \<sigma> M P)"
    by (rule CEV_proves.MP[OF assms(4)])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(5)])
qed

lemma CEV_imp_ObjTrue_left_biconditional:
  assumes "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (Imp ObjTrue B \<longleftrightarrow>\<^sub>o B)"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have imp_type: "\<Gamma> \<turnstile> Imp ObjTrue B : Prop"
    using true_type assms by auto
  have left_to_right: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp ObjTrue B) B"
  proof -
    have local_B: "CEV_from \<Gamma> (Imp ObjTrue B) B"
    proof -
      have local_true: "CEV_from \<Gamma> (Imp ObjTrue B) ObjTrue"
        by (intro CEV_from.Theorem CEV_proves_ObjTrue)
      have local_imp: "CEV_from \<Gamma> (Imp ObjTrue B) (Imp ObjTrue B)"
        by (intro CEV_from.Assumption imp_type)
      show ?thesis
        by (rule CEV_from.MP[OF local_true local_imp])
    qed
    show ?thesis
      using local_B imp_type by (rule CEV_from_deduction)
  qed
  have right_to_left: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp ObjTrue B)"
    using assms true_type by (rule CEV_taut_imp)
  show ?thesis
    by (rule CEV_conj_intro[OF left_to_right right_to_left])
qed

lemma CEV_eq_imp_ObjTrue_left:
  assumes "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (Imp ObjTrue B) B"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have imp_type: "\<Gamma> \<turnstile> Imp ObjTrue B : Prop"
    using true_type assms by auto
  have bicond: "\<Gamma> \<turnstile>\<^sub>CEV (Imp ObjTrue B \<longleftrightarrow>\<^sub>o B)"
    using assms by (rule CEV_imp_ObjTrue_left_biconditional)
  show ?thesis
    using imp_type assms bicond by (rule CEV_zeroary_equivalence)
qed

lemma CEV_eq_truth_of_eq:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Eq Prop (Eq \<sigma> M N) ObjTrue)"
proof -
  let ?E_MN = "Eq \<sigma> M N"
  let ?E_MM = "Eq \<sigma> M M"
  let ?Box_MM = "Eq Prop ?E_MM ObjTrue"
  let ?Box_MN = "Eq Prop ?E_MN ObjTrue"
  let ?F = "Lam \<sigma> (Eq Prop (Eq \<sigma> (shift M) (Var 0)) (shift ObjTrue))"
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have E_MN_type: "\<Gamma> \<turnstile> ?E_MN : Prop"
    using assms by auto
  have E_MM_type: "\<Gamma> \<turnstile> ?E_MM : Prop"
    using assms(1) by auto
  have Box_MM_type: "\<Gamma> \<turnstile> ?Box_MM : Prop"
    using E_MM_type true_type by auto
  have Box_MN_type: "\<Gamma> \<turnstile> ?Box_MN : Prop"
    using E_MN_type true_type by auto
  have shifted_M_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    using assms(1) by (rule weakening_front)
  have shifted_true_type: "\<sigma> # \<Gamma> \<turnstile> shift ObjTrue : Prop"
    using true_type by (rule weakening_front)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by auto
  have shifted_eq_type: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (shift M) (Var 0) : Prop"
    using shifted_M_type var0_type by auto
  have body_type: "\<sigma> # \<Gamma> \<turnstile> Eq Prop (Eq \<sigma> (shift M) (Var 0)) (shift ObjTrue) : Prop"
    using shifted_eq_type shifted_true_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_M_type: "\<Gamma> \<turnstile> App ?F M : Prop"
    using F_type assms(1) by auto
  have app_N_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type assms(2) by auto
  have ref_M: "\<Gamma> \<turnstile>\<^sub>CEV ?E_MM"
    using assms(1) by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have box_ref_M: "\<Gamma> \<turnstile>\<^sub>CEV ?Box_MM"
    using CEV_necessitation[OF ref_M] by (simp add: ObjBox_def)
  have beta_M: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F M \<longleftrightarrow>\<^sub>o ?Box_MM)"
  proof -
    have step: "compatible_step beta_contract (App ?F M) ?Box_MM"
    proof -
      have "compatible_step beta_contract (App ?F M)
          (subst0 M (Eq Prop (Eq \<sigma> (shift M) (Var 0)) (shift ObjTrue)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_M_type Box_MM_type step by (rule CEV_beta_step)
  qed
  have beta_N: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F N \<longleftrightarrow>\<^sub>o ?Box_MN)"
  proof -
    have step: "compatible_step beta_contract (App ?F N) ?Box_MN"
    proof -
      have "compatible_step beta_contract (App ?F N)
          (subst0 N (Eq Prop (Eq \<sigma> (shift M) (Var 0)) (shift ObjTrue)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_N_type Box_MN_type step by (rule CEV_beta_step)
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E_MN (Imp (App ?F M) (App ?F N))"
    using assms(1,2) F_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have local_box: "CEV_from \<Gamma> ?E_MN ?Box_MN"
  proof -
    have local_E: "CEV_from \<Gamma> ?E_MN ?E_MN"
      by (intro CEV_from.Assumption E_MN_type)
    have imp_Box_MM_app_M: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Box_MM (App ?F M)"
      using app_M_type Box_MM_type beta_M by (rule CEV_beta_right_imp)
    have local_app_M: "CEV_from \<Gamma> ?E_MN (App ?F M)"
    proof -
      have local_Box_MM: "CEV_from \<Gamma> ?E_MN ?Box_MM"
        by (intro CEV_from.Theorem box_ref_M)
      show ?thesis
        by (rule CEV_from.MP[OF local_Box_MM CEV_from.Theorem[OF imp_Box_MM_app_M]])
    qed
    have local_app_imp: "CEV_from \<Gamma> ?E_MN (Imp (App ?F M) (App ?F N))"
      by (rule CEV_from.MP[OF local_E CEV_from.Theorem[OF ll]])
    have local_app_N: "CEV_from \<Gamma> ?E_MN (App ?F N)"
      by (rule CEV_from.MP[OF local_app_M local_app_imp])
    have imp_app_N_Box_MN: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?F N) ?Box_MN"
      using app_N_type Box_MN_type beta_N by (rule CEV_beta_left_imp)
    show ?thesis
      by (rule CEV_from.MP[OF local_app_N CEV_from.Theorem[OF imp_app_N_Box_MN]])
  qed
  show ?thesis
    using local_box E_MN_type by (rule CEV_from_deduction)
qed

lemma CEV_modal_T:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV modal_T A"
proof -
  have E_type: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
    using assms by (rule typed_ObjBox)
  have sym: "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o A) (Eq Prop ObjTrue A)"
    unfolding ObjBox_def using assms typed_ObjTrue by (rule CEV_eq_sym)
  let ?TT = "App prop_id ObjTrue"
  let ?TA = "App prop_id A"
  have TT_type: "\<Gamma> \<turnstile> ?TT : Prop"
    using typed_prop_id typed_ObjTrue by auto
  have TA_type: "\<Gamma> \<turnstile> ?TA : Prop"
    using typed_prop_id assms by auto
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq Prop ObjTrue A) (Imp ?TT ?TA)"
    using typed_ObjTrue assms typed_prop_id
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have local_A: "CEV_from \<Gamma> (\<box>\<^sub>o A) A"
  proof -
    have local_box: "CEV_from \<Gamma> (\<box>\<^sub>o A) (\<box>\<^sub>o A)"
      by (intro CEV_from.Assumption E_type)
    have local_sym_imp: "CEV_from \<Gamma> (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o A) (Eq Prop ObjTrue A))"
      by (intro CEV_from.Theorem sym)
    have local_eq: "CEV_from \<Gamma> (\<box>\<^sub>o A) (Eq Prop ObjTrue A)"
      by (rule CEV_from.MP[OF local_box local_sym_imp])
    have local_ll: "CEV_from \<Gamma> (\<box>\<^sub>o A) (Imp (Eq Prop ObjTrue A) (Imp ?TT ?TA))"
      by (intro CEV_from.Theorem ll)
    have imp_TT_TA: "CEV_from \<Gamma> (\<box>\<^sub>o A) (Imp ?TT ?TA)"
      by (rule CEV_from.MP[OF local_eq local_ll])
    have local_TT: "CEV_from \<Gamma> (\<box>\<^sub>o A) ?TT"
      by (intro CEV_from.Theorem CEV_prop_id_ObjTrue)
    have local_TA: "CEV_from \<Gamma> (\<box>\<^sub>o A) ?TA"
      by (rule CEV_from.MP[OF local_TT imp_TT_TA])
    have local_imp_A: "CEV_from \<Gamma> (\<box>\<^sub>o A) (Imp ?TA A)"
      by (intro CEV_from.Theorem CEV_app_prop_id_imp assms)
    show ?thesis
      by (rule CEV_from.MP[OF local_TA local_imp_A])
  qed
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o A) A"
    using local_A E_type by (rule CEV_from_deduction)
  then show ?thesis
    by (simp add: modal_T_def)
qed

lemma CEV_modal_K:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV modal_K A B"
proof -
  let ?Eimp = "Eq Prop (Imp A B) ObjTrue"
  let ?EA = "Eq Prop A ObjTrue"
  let ?EB = "Eq Prop B ObjTrue"
  let ?C = "Conj ?Eimp ?EA"
  let ?X = "Imp ObjTrue B"
  let ?F = "Lam Prop (Eq Prop (Imp (Var 0) (shift B)) (shift ObjTrue))"
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms by auto
  have Eimp_type: "\<Gamma> \<turnstile> ?Eimp : Prop"
    using imp_type true_type by auto
  have EA_type: "\<Gamma> \<turnstile> ?EA : Prop"
    using assms(1) true_type by auto
  have EB_type: "\<Gamma> \<turnstile> ?EB : Prop"
    using assms(2) true_type by auto
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using Eimp_type EA_type by auto
  have X_type: "\<Gamma> \<turnstile> ?X : Prop"
    using true_type assms(2) by auto
  have shifted_B_type: "Prop # \<Gamma> \<turnstile> shift B : Prop"
    using assms(2) by (rule weakening_front)
  have shifted_true_type: "Prop # \<Gamma> \<turnstile> shift ObjTrue : Prop"
    using true_type by (rule weakening_front)
  have var0_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by auto
  have shifted_imp_type: "Prop # \<Gamma> \<turnstile> Imp (Var 0) (shift B) : Prop"
    using var0_type shifted_B_type by auto
  have body_type: "Prop # \<Gamma> \<turnstile> Eq Prop (Imp (Var 0) (shift B)) (shift ObjTrue) : Prop"
    using shifted_imp_type shifted_true_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_A_type: "\<Gamma> \<turnstile> App ?F A : Prop"
    using F_type assms(1) by auto
  have app_true_type: "\<Gamma> \<turnstile> App ?F ObjTrue : Prop"
    using F_type true_type by auto
  have XT_type: "\<Gamma> \<turnstile> Eq Prop ?X ObjTrue : Prop"
    using X_type true_type by auto
  have beta_A: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F A \<longleftrightarrow>\<^sub>o ?Eimp)"
  proof -
    have step: "compatible_step beta_contract (App ?F A) ?Eimp"
    proof -
      have "compatible_step beta_contract (App ?F A)
          (subst0 A (Eq Prop (Imp (Var 0) (shift B)) (shift ObjTrue)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_A_type Eimp_type step by (rule CEV_beta_step)
  qed
  have beta_true: "\<Gamma> \<turnstile>\<^sub>CEV (App ?F ObjTrue \<longleftrightarrow>\<^sub>o Eq Prop ?X ObjTrue)"
  proof -
    have step: "compatible_step beta_contract (App ?F ObjTrue) (Eq Prop ?X ObjTrue)"
    proof -
      have "compatible_step beta_contract (App ?F ObjTrue)
          (subst0 ObjTrue (Eq Prop (Imp (Var 0) (shift B)) (shift ObjTrue)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_true_type XT_type step by (rule CEV_beta_step)
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?EA (Imp (App ?F A) (App ?F ObjTrue))"
    using assms(1) true_type F_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have XB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?X B"
    using assms(2) by (rule CEV_eq_imp_ObjTrue_left)
  have BX: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop B ?X"
    by (rule CEV_eq_sym_from[OF X_type assms(2) XB])
  have trans_BX_true: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq Prop B ?X) (Imp (Eq Prop ?X ObjTrue) ?EB)"
    using assms(2) X_type true_type by (rule CEV_eq_trans)
  have local_EB: "CEV_from \<Gamma> ?C ?EB"
  proof -
    have local_C: "CEV_from \<Gamma> ?C ?C"
      by (intro CEV_from.Assumption C_type)
    have left_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?Eimp"
      using Eimp_type EA_type by (rule CEV_conj_left_imp)
    have right_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?EA"
      using Eimp_type EA_type by (rule CEV_conj_right_imp)
    have local_Eimp: "CEV_from \<Gamma> ?C ?Eimp"
      by (rule CEV_from.MP[OF local_C CEV_from.Theorem[OF left_imp]])
    have local_EA: "CEV_from \<Gamma> ?C ?EA"
      by (rule CEV_from.MP[OF local_C CEV_from.Theorem[OF right_imp]])
    have imp_Eimp_app_A: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Eimp (App ?F A)"
      using app_A_type Eimp_type beta_A by (rule CEV_beta_right_imp)
    have local_app_A: "CEV_from \<Gamma> ?C (App ?F A)"
      by (rule CEV_from.MP[OF local_Eimp CEV_from.Theorem[OF imp_Eimp_app_A]])
    have local_app_imp: "CEV_from \<Gamma> ?C (Imp (App ?F A) (App ?F ObjTrue))"
      by (rule CEV_from.MP[OF local_EA CEV_from.Theorem[OF ll]])
    have local_app_true: "CEV_from \<Gamma> ?C (App ?F ObjTrue)"
      by (rule CEV_from.MP[OF local_app_A local_app_imp])
    have imp_app_true_XT: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?F ObjTrue) (Eq Prop ?X ObjTrue)"
      using app_true_type XT_type beta_true by (rule CEV_beta_left_imp)
    have local_XT: "CEV_from \<Gamma> ?C (Eq Prop ?X ObjTrue)"
      by (rule CEV_from.MP[OF local_app_true CEV_from.Theorem[OF imp_app_true_XT]])
    have local_BX: "CEV_from \<Gamma> ?C (Eq Prop B ?X)"
      by (intro CEV_from.Theorem BX)
    have local_trans_1: "CEV_from \<Gamma> ?C (Imp (Eq Prop ?X ObjTrue) ?EB)"
      by (rule CEV_from.MP[OF local_BX CEV_from.Theorem[OF trans_BX_true]])
    show ?thesis
      by (rule CEV_from.MP[OF local_XT local_trans_1])
  qed
  have C_imp_EB: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C ?EB"
    using local_EB C_type by (rule CEV_from_deduction)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Eimp (Imp ?EA ?EB)"
    using Eimp_type EA_type EB_type C_imp_EB by (rule CEV_uncurry_conj)
  then show ?thesis
    by (simp add: modal_K_def ObjBox_def)
qed

lemma CEV_modal_4:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV modal_4 A"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq Prop A ObjTrue)
      (Eq Prop (Eq Prop A ObjTrue) ObjTrue)"
    using assms true_type by (rule CEV_eq_truth_of_eq)
  then show ?thesis
    by (simp add: modal_4_def ObjBox_def)
qed

theorem CEV_S4_package:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV modal_K A B"
    and "\<Gamma> \<turnstile>\<^sub>CEV modal_T A"
    and "\<Gamma> \<turnstile>\<^sub>CEV modal_4 A"
    and "\<And>C. \<Gamma> \<turnstile>\<^sub>CEV C \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o C"
  using assms
  by (auto intro: CEV_modal_K CEV_modal_T CEV_modal_4 CEV_necessitation)

end
