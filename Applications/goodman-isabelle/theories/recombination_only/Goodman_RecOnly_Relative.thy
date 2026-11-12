theory Goodman_RecOnly_Relative
  imports Goodman_RecOnly_Closure
begin

text \<open>Recombination without Exhaustion: the relativized Lettie construction (Lemmas 3 to 9,
  Section 4 of the hand proof). Everything here is a theorem of Lettie's U with no
  added premise: the guard b and the purity assertions \<pi>(P_b), \<pi>(P'_b) occur only as
  antecedents.\<close>

declare has_type.App[rule del]

section \<open>1. The combinators, with \<pi> and the guard b abstracted\<close>

text \<open>R_b(x,y) := \<forall>Y (\<pi>(Y) \<longrightarrow> (Y y \<longrightarrow> \<diamond>(b \<and> Y x))), possibility written as not-box-not.\<close>
definition ro_R :: oterm where
  "ro_R = Lam rc_c (Lam Prop (Lam Prop (Lam Prop (Forall rc_u (Imp (App (Var 4) (Var 0))
     (Imp (App (Var 0) (Var 1)) (Neg (\<box>\<^sub>o (Neg (Conj (Var 3) (App (Var 0) (Var 2))))))))))))"

text \<open>F_b(z) := \<box>(b \<longrightarrow> C_b(z)), C_b(z) := \<not>R_b(z,\<not>z) \<and> \<not>R_b(\<not>z,z).\<close>
definition ro_F :: oterm where
  "ro_F = Lam rc_c (Lam Prop (Lam Prop (\<box>\<^sub>o (Imp (Var 1)
     (Conj (Neg (App (App (App (App ro_R (Var 2)) (Var 1)) (Var 0)) (Neg (Var 0))))
           (Neg (App (App (App (App ro_R (Var 2)) (Var 1)) (Neg (Var 0))) (Var 0))))))))"

definition ro_Q :: oterm where
  "ro_Q = Lam rc_c (Lam Prop (Lam Prop (Imp (App (App (App ro_F (Var 2)) (Var 1)) (Var 0)) (Var 0))))"
definition ro_P :: oterm where
  "ro_P = Lam rc_c (Lam Prop (Lam Prop (Conj (Neg (Var 0)) (Neg (App (App (App ro_F (Var 2)) (Var 1)) (Var 0))))))"
definition ro_Pp :: oterm where
  "ro_Pp = Lam rc_c (Lam Prop (Lam Prop (Conj (Var 0) (Neg (App (App (App ro_F (Var 2)) (Var 1)) (Var 0))))))"

text \<open>\<Phi> := \<lambda>b. b \<and> \<kappa>(b), \<kappa>(b) := \<pi>(P_b) \<and> \<pi>(P'_b).\<close>
definition ro_Phi :: oterm where
  "ro_Phi = Lam rc_c (Lam Prop (Conj (Var 0) (Conj (App (Var 1) (App (App ro_P (Var 1)) (Var 0)))
     (App (Var 1) (App (App ro_Pp (Var 1)) (Var 0))))))"

lemma ro_R_ty: "\<Gamma> \<turnstile> ro_R : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)))"
  by (rule infer_type_sound) (simp add: ro_R_def ObjBox_def ObjTrue_def lookup_def)
lemma ro_F_ty: "\<Gamma> \<turnstile> ro_F : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop))"
  by (rule infer_type_sound) (simp add: ro_F_def ro_R_def ObjBox_def ObjTrue_def lookup_def)
lemma ro_Q_ty: "\<Gamma> \<turnstile> ro_Q : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)"
  by (rule infer_type_sound) (simp add: ro_Q_def ro_F_def ro_R_def ObjBox_def ObjTrue_def lookup_def)
lemma ro_P_ty: "\<Gamma> \<turnstile> ro_P : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)"
  by (rule infer_type_sound) (simp add: ro_P_def ro_F_def ro_R_def ObjBox_def ObjTrue_def lookup_def)
lemma ro_Pp_ty: "\<Gamma> \<turnstile> ro_Pp : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)"
  by (rule infer_type_sound) (simp add: ro_Pp_def ro_F_def ro_R_def ObjBox_def ObjTrue_def lookup_def)
lemma ro_Phi_ty: "\<Gamma> \<turnstile> ro_Phi : rc_c \<rightarrow>\<^sub>o rc_u"
  by (rule infer_type_sound) (simp add: ro_Phi_def ro_P_def ro_Pp_def ro_F_def ro_R_def ObjBox_def ObjTrue_def lookup_def)

lemma ro_rel_consts: "consts_of ro_R = {}" "consts_of ro_F = {}" "consts_of ro_Q = {}" "consts_of ro_P = {}"
  "consts_of ro_Pp = {}" "consts_of ro_Phi = {}"
  by (simp_all add: ro_R_def ro_F_def ro_Q_def ro_P_def ro_Pp_def ro_Phi_def ObjBox_def ObjTrue_def)

lemma ro_rel_closed[simp]:
  "subst s ro_R = ro_R" "subst s ro_F = ro_F" "subst s ro_Q = ro_Q" "subst s ro_P = ro_P" "subst s ro_Pp = ro_Pp"
  "subst s ro_Phi = ro_Phi"
  by (simp_all add: ro_R_def ro_F_def ro_Q_def ro_P_def ro_Pp_def ro_Phi_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma ro_rel_rename[simp]:
  "rename \<rho> ro_R = ro_R" "rename \<rho> ro_F = ro_F" "rename \<rho> ro_Q = ro_Q" "rename \<rho> ro_P = ro_P" "rename \<rho> ro_Pp = ro_Pp"
  "rename \<rho> ro_Phi = ro_Phi"
  by (simp_all add: ro_R_def ro_F_def ro_Q_def ro_P_def ro_Pp_def ro_Phi_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma ro_rel_shift[simp]:
  "shift ro_R = ro_R" "shift ro_F = ro_F" "shift ro_Q = ro_Q" "shift ro_P = ro_P" "shift ro_Pp = ro_Pp" "shift ro_Phi = ro_Phi"
  by (simp_all add: shift_def)

section \<open>2. The relativized notions at \<pi>\<close>

definition roR :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roR b x y = App (App (App (App ro_R rc_p) b) x) y"
definition roFf :: "oterm \<Rightarrow> oterm" where "roFf b = App (App ro_F rc_p) b"
definition roF :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roF b z = App (roFf b) z"
definition roQf :: "oterm \<Rightarrow> oterm" where "roQf b = App (App ro_Q rc_p) b"
definition roQ :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roQ b z = App (roQf b) z"
definition roP :: "oterm \<Rightarrow> oterm" where "roP b = App (App ro_P rc_p) b"
definition roPp :: "oterm \<Rightarrow> oterm" where "roPp b = App (App ro_Pp rc_p) b"
definition roC :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roC b z = Conj (Neg (roR b z (Neg z))) (Neg (roR b (Neg z) z))"
definition rok :: "oterm \<Rightarrow> oterm" where "rok b = Conj (App rc_p (roP b)) (App rc_p (roPp b))"
definition roPhi :: oterm where "roPhi = App ro_Phi rc_p"

lemma ro_rel_subst[simp]:
  "subst s (roR b x y) = roR (subst s b) (subst s x) (subst s y)" "subst s (roFf b) = roFf (subst s b)"
  "subst s (roF b z) = roF (subst s b) (subst s z)" "subst s (roQf b) = roQf (subst s b)"
  "subst s (roQ b z) = roQ (subst s b) (subst s z)" "subst s (roP b) = roP (subst s b)" "subst s (roPp b) = roPp (subst s b)"
  "subst s (roC b z) = roC (subst s b) (subst s z)" "subst s (rok b) = rok (subst s b)" "subst s roPhi = roPhi"
  by (simp_all add: roR_def roFf_def roF_def roQf_def roQ_def roP_def roPp_def roC_def rok_def roPhi_def)

lemma ro_rel_ren[simp]:
  "rename \<rho> (roR b x y) = roR (rename \<rho> b) (rename \<rho> x) (rename \<rho> y)" "rename \<rho> (roFf b) = roFf (rename \<rho> b)"
  "rename \<rho> (roF b z) = roF (rename \<rho> b) (rename \<rho> z)" "rename \<rho> (roQf b) = roQf (rename \<rho> b)"
  "rename \<rho> (roQ b z) = roQ (rename \<rho> b) (rename \<rho> z)" "rename \<rho> (roP b) = roP (rename \<rho> b)"
  "rename \<rho> (roPp b) = roPp (rename \<rho> b)" "rename \<rho> (roC b z) = roC (rename \<rho> b) (rename \<rho> z)"
  "rename \<rho> (rok b) = rok (rename \<rho> b)" "rename \<rho> roPhi = roPhi"
  by (simp_all add: roR_def roFf_def roF_def roQf_def roQ_def roP_def roPp_def roC_def rok_def roPhi_def)

lemma ro_rel_sh[simp]:
  "shift (roR b x y) = roR (shift b) (shift x) (shift y)" "shift (roF b z) = roF (shift b) (shift z)"
  "shift (roQ b z) = roQ (shift b) (shift z)" "shift (roP b) = roP (shift b)" "shift (roPp b) = roPp (shift b)"
  "shift (roC b z) = roC (shift b) (shift z)" "shift (rok b) = rok (shift b)" "shift roPhi = roPhi"
  "shift (roQf b) = roQf (shift b)" "shift (roFf b) = roFf (shift b)"
  by (simp_all add: shift_def)

lemma roR_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile> y : Prop \<Longrightarrow> \<Gamma> \<turnstile> roR b x y : Prop"
  unfolding roR_def by (intro has_type.App[OF has_type.App[OF has_type.App[OF has_type.App[OF ro_R_ty rc_p_ty]]]])
lemma roFf_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> roFf b : Prop \<rightarrow>\<^sub>o Prop"
  unfolding roFf_def by (rule has_type.App[OF has_type.App[OF ro_F_ty rc_p_ty]])
lemma roF_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> z : Prop \<Longrightarrow> \<Gamma> \<turnstile> roF b z : Prop"
  unfolding roF_def by (rule has_type.App[OF roFf_ty])
lemma roQf_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> roQf b : rc_u"
  unfolding roQf_def by (rule has_type.App[OF has_type.App[OF ro_Q_ty rc_p_ty]])
lemma roQ_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> z : Prop \<Longrightarrow> \<Gamma> \<turnstile> roQ b z : Prop"
  unfolding roQ_def by (rule has_type.App[OF roQf_ty])
lemma roP_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> roP b : rc_u"
  unfolding roP_def by (rule has_type.App[OF has_type.App[OF ro_P_ty rc_p_ty]])
lemma roPp_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> roPp b : rc_u"
  unfolding roPp_def by (rule has_type.App[OF has_type.App[OF ro_Pp_ty rc_p_ty]])
lemma roC_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> z : Prop \<Longrightarrow> \<Gamma> \<turnstile> roC b z : Prop"
  unfolding roC_def by (intro has_type.Conj has_type.Neg roR_ty) simp_all
lemma rok_ty: "\<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> rok b : Prop"
  unfolding rok_def by (intro has_type.Conj rc_pure_ty roP_ty roPp_ty)
lemma roPhi_ty: "\<Gamma> \<turnstile> roPhi : rc_u" unfolding roPhi_def by (rule has_type.App[OF ro_Phi_ty rc_p_ty])

lemma ro_be4: assumes L: "\<Gamma> \<turnstile> Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 (Lam \<sigma>4 B))) : \<sigma>1 \<rightarrow>\<^sub>o (\<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o (\<sigma>4 \<rightarrow>\<^sub>o \<tau>)))"
  and a1: "\<Gamma> \<turnstile> a1 : \<sigma>1" and a2: "\<Gamma> \<turnstile> a2 : \<sigma>2" and a3: "\<Gamma> \<turnstile> a3 : \<sigma>3" and a4: "\<Gamma> \<turnstile> a4 : \<sigma>4"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (App (App (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 (Lam \<sigma>4 B)))) a1) a2) a3) a4)
    (subst0 a4 (subst (lift_subst (case_nat a3 Var)) (subst (lift_subst (lift_subst (case_nat a2 Var)))
      (subst (lift_subst (lift_subst (lift_subst (case_nat a1 Var)))) B))))"
proof -
  let ?L = "Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 (Lam \<sigma>4 B)))"
  let ?M = "Lam \<sigma>2 (Lam \<sigma>3 (Lam \<sigma>4 (subst (lift_subst (lift_subst (lift_subst (case_nat a1 Var)))) B)))"
  have s1: "beta_eta_equiv \<Gamma> (\<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o (\<sigma>4 \<rightarrow>\<^sub>o \<tau>))) (App ?L a1) ?M"
    using ro_be1[OF L a1] by (simp add: subst0_def)
  have tM: "\<Gamma> \<turnstile> ?M : \<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o (\<sigma>4 \<rightarrow>\<^sub>o \<tau>))" by (rule beta_eta_equiv_right_type[OF s1])
  have s2: "beta_eta_equiv \<Gamma> (\<sigma>4 \<rightarrow>\<^sub>o \<tau>) (App (App (App ?L a1) a2) a3) (App (App ?M a2) a3)"
    by (rule rc_be_app[OF rc_be_app[OF s1 refl a2] refl a3])
  have s3: "beta_eta_equiv \<Gamma> \<tau> (App (App (App ?M a2) a3) a4)
    (subst0 a4 (subst (lift_subst (case_nat a3 Var)) (subst (lift_subst (lift_subst (case_nat a2 Var)))
      (subst (lift_subst (lift_subst (lift_subst (case_nat a1 Var)))) B))))"
    by (rule ro_be3[OF tM a2 a3 a4])
  have s4: "beta_eta_equiv \<Gamma> \<tau> (App (App (App (App ?L a1) a2) a3) a4) (App (App (App ?M a2) a3) a4)"
    by (rule rc_be_app[OF s2 refl a4])
  show ?thesis by (rule beta_eta_equiv.Trans[OF s4 s3])
qed

subsection \<open>Unfolding\<close>

lemma roR_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop" and y: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (roR b x y \<longleftrightarrow>\<^sub>o Forall rc_u (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y))
    (Neg (\<box>\<^sub>o (Neg (Conj (shift b) (App (Var 0) (shift x)))))))))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (roR b x y) (Forall rc_u (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y))
    (Neg (\<box>\<^sub>o (Neg (Conj (shift b) (App (Var 0) (shift x)))))))))"
    using ro_be4[OF ro_R_ty[unfolded ro_R_def] rc_p_ty b x y] unfolding roR_def ro_R_def
    by (simp add: subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roF_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" and z: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (roF b z \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (Imp b (roC b z)))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (roF b z) (\<box>\<^sub>o (Imp b (roC b z)))"
    using ro_be3[OF ro_F_ty[unfolded ro_F_def] rc_p_ty b z] unfolding roF_def roFf_def ro_F_def
    by (simp add: roC_def roR_def subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roQ_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" and z: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (roQ b z \<longleftrightarrow>\<^sub>o Imp (roF b z) z)"
proof -
  have "beta_eta_equiv \<Gamma> Prop (roQ b z) (Imp (roF b z) z)"
    using ro_be3[OF ro_Q_ty[unfolded ro_Q_def] rc_p_ty b z] unfolding roQ_def roQf_def ro_Q_def
    by (simp add: roF_def roFf_def subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roP_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" and z: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App (roP b) z \<longleftrightarrow>\<^sub>o Conj (Neg z) (Neg (roF b z)))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App (roP b) z) (Conj (Neg z) (Neg (roF b z)))"
    using ro_be3[OF ro_P_ty[unfolded ro_P_def] rc_p_ty b z] unfolding roP_def ro_P_def
    by (simp add: roF_def roFf_def subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roPp_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" and z: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App (roPp b) z \<longleftrightarrow>\<^sub>o Conj z (Neg (roF b z)))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App (roPp b) z) (Conj z (Neg (roF b z)))"
    using ro_be3[OF ro_Pp_ty[unfolded ro_Pp_def] rc_p_ty b z] unfolding roPp_def ro_Pp_def
    by (simp add: roF_def roFf_def subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roPhi_iff: assumes b: "\<Gamma> \<turnstile> b : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App roPhi b \<longleftrightarrow>\<^sub>o Conj b (rok b))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App roPhi b) (Conj b (rok b))"
    using ro_be2[OF ro_Phi_ty[unfolded ro_Phi_def] rc_p_ty b] unfolding roPhi_def ro_Phi_def
    by (simp add: rok_def roP_def roPp_def subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

subsection \<open>Introducing and using R_b\<close>

lemma roR_elim: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop" and y: "\<Gamma> \<turnstile> y : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roR b x y) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (Conj b (App Y x)))))))"
proof -
  let ?A = "Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y)) (Neg (\<box>\<^sub>o (Neg (Conj (shift b) (App (Var 0) (shift x)))))))"
  note i = roR_iff[OF b x y]
  have f: "\<Gamma> \<turnstile> Forall rc_u ?A : Prop" using U_formula[OF i] by (auto elim: has_type.cases)
  have ty: "rc_u # \<Gamma> \<turnstile> ?A : Prop" using f by (auto elim: has_type.cases)
  have u: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall rc_u ?A) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (Conj b (App Y x)))))))"
    by (rule ro_ui[OF ty Y]) (simp add: subst0_def)
  show ?thesis by (rule u_rc_pc2[OF i u]) (insert U_formula[OF u] roR_ty[OF b x y], auto elim!: has_type.cases[of _ "Imp _ _"]
    intro!: has_type.Imp)
qed

lemma roR_intro: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop" and y: "\<Gamma> \<turnstile> y : Prop" and P: "\<Gamma> \<turnstile> P : Prop"
  and h: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y))
    (Neg (\<box>\<^sub>o (Neg (Conj (shift b) (App (Var 0) (shift x))))))))"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp P (roR b x y)"
proof -
  note i = roR_iff[OF b x y]
  have ty: "rc_u # \<Gamma> \<turnstile> Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y)) (Neg (\<box>\<^sub>o (Neg (Conj (shift b) (App (Var 0) (shift x))))))) : Prop"
    using U_formula[OF h] by (auto elim: has_type.cases)
  note g = U_proves.Gen[OF P ty h]
  show ?thesis by (rule u_rc_pc2[OF g i has_type.Imp[OF P roR_ty[OF b x y]]]) (unfold prop_eval.simps, blast)
qed

section \<open>3. Lemmas 3 to 9: the logical part of Lettie's proof, with a guard b\<close>

lemma ro_lemA: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roF b x) (\<box>\<^sub>o (roF b x))"
proof -
  let ?B = "Imp b (roC b x)"
  have tF: "\<Gamma> \<turnstile> roF b x : Prop" by (rule roF_ty[OF b x])
  have tB: "\<Gamma> \<turnstile> ?B : Prop" by (intro has_type.Imp b roC_ty x)
  note ib = roF_iff[OF b x]
  have h1: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o ?B) (roF b x)" by (rule u_rc_pc1[OF ib]) (insert tF typed_ObjBox[OF tB], (unfold prop_eval.simps)?, blast+)
  have h2: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (\<box>\<^sub>o ?B)) (\<box>\<^sub>o (roF b x))" by (rule u_rc_K[OF h1])
  have h3: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o ?B) (\<box>\<^sub>o (\<box>\<^sub>o ?B))" by (rule U_modal_4[OF tB, unfolded modal_4_def])
  show ?thesis by (rule u_rc_pc3[OF ib h3 h2]) (insert tF typed_ObjBox[OF tF], (unfold prop_eval.simps)?, blast+)
qed

lemma ro_lemB: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roF b x) (Eq Prop (roQ b x) x)"
proof -
  have tF: "\<Gamma> \<turnstile> roF b x : Prop" by (rule roF_ty[OF b x])
  have tQ: "\<Gamma> \<turnstile> roQ b x : Prop" by (rule roQ_ty[OF b x])
  have h1: "\<Gamma> \<turnstile>\<^sub>U Imp (roF b x) (roQ b x \<longleftrightarrow>\<^sub>o x)" by (rule u_rc_pc1[OF roQ_iff[OF b x]]) (insert tF tQ x, (unfold prop_eval.simps)?, blast+)
  have h2: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (roF b x)) (\<box>\<^sub>o (roQ b x \<longleftrightarrow>\<^sub>o x))" by (rule u_rc_K[OF h1])
  show ?thesis by (rule u_rc_pc3[OF ro_lemA[OF b x] h2 u_rc_box_iff_eq[OF tQ x]]) (insert tF tQ x, (unfold prop_eval.simps)?, blast+)
qed

lemma ro_lemC: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (roF b (Neg x) \<longleftrightarrow>\<^sub>o roF b x)"
proof -
  have tn: "\<Gamma> \<turnstile> Neg x : Prop" using x by auto
  have tnn: "\<Gamma> \<turnstile> Neg (Neg x) : Prop" using x by auto
  have sn: "Prop # \<Gamma> \<turnstile> shift (Neg x) : Prop" by (rule weaken_shift_type_ok[OF tn])
  have sb: "Prop # \<Gamma> \<turnstile> shift b : Prop" by (rule weaken_shift_type_ok[OF b])
  have e: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Neg (Neg x)) x" by (rule u_rc_eq_of_iff[OF tnn x U_taut]) (insert tnn x, (unfold prop_tautology_def prop_eval.simps)?, blast+)
  have C1: "Prop # \<Gamma> \<turnstile> roR (shift b) (shift (Neg x)) (Var 0) : Prop" by (rule roR_ty[OF sb sn]) simp
  have C2: "Prop # \<Gamma> \<turnstile> roR (shift b) (Var 0) (shift (Neg x)) : Prop" by (rule roR_ty[OF sb _ sn]) simp
  have c1: "\<Gamma> \<turnstile>\<^sub>U (roR b (Neg x) (Neg (Neg x)) \<longleftrightarrow>\<^sub>o roR b (Neg x) x)" using u_rc_congr[OF C1 tnn x e] by (simp add: subst0_def)
  have c2: "\<Gamma> \<turnstile>\<^sub>U (roR b (Neg (Neg x)) (Neg x) \<longleftrightarrow>\<^sub>o roR b x (Neg x))" using u_rc_congr[OF C2 tnn x e] by (simp add: subst0_def)
  have tB1: "\<Gamma> \<turnstile> roC b (Neg x) : Prop" by (rule roC_ty[OF b tn])
  have tB2: "\<Gamma> \<turnstile> roC b x : Prop" by (rule roC_ty[OF b x])
  have eB: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (roC b (Neg x)) (roC b x)"
    by (rule u_rc_eq_of_iff[OF tB1 tB2 u_rc_pc2[OF c1 c2]]) (insert tB1 tB2, (unfold roC_def prop_eval.simps)?, blast+)
  have CB: "Prop # \<Gamma> \<turnstile> \<box>\<^sub>o (Imp (shift b) (Var 0)) : Prop" by (intro typed_ObjBox has_type.Imp sb) simp
  have bx: "\<Gamma> \<turnstile>\<^sub>U (\<box>\<^sub>o (Imp b (roC b (Neg x))) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (Imp b (roC b x)))"
    using u_rc_congr[OF CB tB1 tB2 eB] by (simp add: subst0_def)
  show ?thesis by (rule u_rc_pc3[OF roF_iff[OF b tn] bx roF_iff[OF b x]]) (insert roF_ty[OF b tn] roF_ty[OF b x], (unfold prop_eval.simps)?, blast+)
qed

lemma ro_lemD: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (roQ b x)) (roF b (roQ b x))"
proof -
  have tQ: "\<Gamma> \<turnstile> roQ b x : Prop" by (rule roQ_ty[OF b x])
  have tFx: "\<Gamma> \<turnstile> roF b x : Prop" by (rule roF_ty[OF b x])
  have tFQ: "\<Gamma> \<turnstile> roF b (roQ b x) : Prop" by (rule roF_ty[OF b tQ])
  have d: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (roQ b x)) (roF b x)" by (rule u_rc_pc1[OF roQ_iff[OF b x]]) (insert tQ tFx, (unfold prop_eval.simps)?, blast+)
  have ll: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop x (roQ b x)) (Imp (roF b x) (roF b (roQ b x)))" unfolding roF_def by (rule u_rc_LL[OF x tQ roFf_ty[OF b]])
  show ?thesis by (rule u_rc_pc4[OF d ro_lemB[OF b x] U_eq_sym[OF tQ x] ll]) (insert tQ tFQ, (unfold prop_eval.simps)?, blast+)
qed

text \<open>Lemma 7: \<box>\<not>P_b(Q_b(x)).\<close>
lemma ro_cor: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o (Neg (App (roP b) (roQ b x)))"
proof -
  have tq: "\<Gamma> \<turnstile> roQ b x : Prop" by (rule roQ_ty[OF b x])
  have tP: "\<Gamma> \<turnstile> App (roP b) (roQ b x) : Prop" by (rule has_type.App[OF roP_ty[OF b] tq])
  have n: "\<Gamma> \<turnstile>\<^sub>U Neg (App (roP b) (roQ b x))"
    by (rule u_rc_pc2[OF ro_lemD[OF b x] roP_iff[OF b tq]]) (insert tq tP roF_ty[OF b tq], (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule U_nec[OF n])
qed

text \<open>The identity P'_b(z) = P_b(\<not>z).\<close>
lemma ro_ident: assumes b: "\<Gamma> \<turnstile> b : Prop" and z: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Eq Prop (App (roPp b) z) (App (roP b) (Neg z))"
proof -
  have tn: "\<Gamma> \<turnstile> Neg z : Prop" using z by blast
  have t1: "\<Gamma> \<turnstile> App (roPp b) z : Prop" and t2: "\<Gamma> \<turnstile> App (roP b) (Neg z) : Prop"
    by (rule has_type.App[OF roPp_ty[OF b] z], rule has_type.App[OF roP_ty[OF b] tn])
  have i: "\<Gamma> \<turnstile>\<^sub>U (App (roPp b) z \<longleftrightarrow>\<^sub>o App (roP b) (Neg z))"
    by (rule u_rc_pc3[OF roPp_iff[OF b z] roP_iff[OF b tn] ro_lemC[OF b z]]) (insert t1 t2, (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule u_rc_eq_of_iff[OF t1 t2 i])
qed

text \<open>Lemma 8 (the guarded step): (b \<and> \<kappa>(b)) \<longrightarrow> C_b(q), q = Q_b(x).\<close>
lemma ro_guarded: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Conj b (rok b)) (roC b (roQ b x))"
proof -
  let ?q = "roQ b x" let ?n = "Neg (roQ b x)"
  have tq: "\<Gamma> \<turnstile> ?q : Prop" by (rule roQ_ty[OF b x])
  have tn: "\<Gamma> \<turnstile> ?n : Prop" using tq by blast
  have tnn: "\<Gamma> \<turnstile> Neg ?n : Prop" using tn by blast
  have tP: "\<Gamma> \<turnstile> roP b : rc_u" and tPp: "\<Gamma> \<turnstile> roPp b : rc_u" by (rule roP_ty[OF b], rule roPp_ty[OF b])
  have tFq: "\<Gamma> \<turnstile> roF b ?q : Prop" by (rule roF_ty[OF b tq])
  have tC: "\<Gamma> \<turnstile> roC b ?q : Prop" by (rule roC_ty[OF b tq])
  have tPq: "\<Gamma> \<turnstile> App (roP b) ?q : Prop" and tPn: "\<Gamma> \<turnstile> App (roP b) ?n : Prop"
    by (rule has_type.App[OF tP tq], rule has_type.App[OF tP tn])
  have tPpq: "\<Gamma> \<turnstile> App (roPp b) ?q : Prop" and tPpn: "\<Gamma> \<turnstile> App (roPp b) ?n : Prop"
    by (rule has_type.App[OF tPp tq], rule has_type.App[OF tPp tn])
  note fq = roF_iff[OF b tq] and d = ro_lemD[OF b x] and T = U_modal_T[OF has_type.Imp[OF b tC], unfolded modal_T_def]
  text \<open>If b and not C_b(q): F_b(q) fails by factivity, so q holds by Lemma 6.\<close>
  have st1: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj b (Neg (roC b ?q))) (Conj ?q (Neg (roF b ?q)))"
    by (rule u_rc_pc3[OF fq T d]) (insert b tC tq tFq, (unfold prop_eval.simps)?, blast+)
  text \<open>Hence P_b(\<not>q) and P'_b(q).\<close>
  have s3: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj ?q (Neg (roF b ?q))) (App (roP b) ?n)"
    by (rule u_rc_pc2[OF roP_iff[OF b tn] ro_lemC[OF b tq]]) (insert tq tFq tPn, (unfold prop_eval.simps)?, blast+)
  have s4: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj ?q (Neg (roF b ?q))) (App (roPp b) ?q)"
    by (rule u_rc_pc1[OF roPp_iff[OF b tq]]) (insert tq tFq tPpq, (unfold prop_eval.simps)?, blast+)
  text \<open>Lemma 7 excludes \<diamond>(b \<and> P_b(q)).\<close>
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (App (roP b) ?q)) (Neg (Conj b (App (roP b) ?q)))"
    by (rule U_taut) (insert tPq b, unfold prop_tautology_def prop_eval.simps, blast)
  have bP: "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o (Neg (Conj b (App (roP b) ?q)))" by (rule U_proves.MP[OF ro_cor[OF b x] u_rc_K[OF k0]])
  text \<open>P'_b(\<not>q) = P_b(q): the identity at \<not>q, with \<not>\<not>q = q.\<close>
  have e1: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (App (roPp b) ?n) (App (roP b) (Neg ?n))" by (rule ro_ident[OF b tn])
  have enn: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Neg ?n) ?q" by (rule u_rc_eq_of_iff[OF tnn tq U_taut]) (insert tnn tq, (unfold prop_tautology_def prop_eval.simps)?, blast+)
  have CP: "Prop # \<Gamma> \<turnstile> App (shift (roP b)) (Var 0) : Prop" by (rule has_type.App[OF weaken_shift_type_ok[OF tP]]) simp
  have e2: "\<Gamma> \<turnstile>\<^sub>U (App (roP b) (Neg ?n) \<longleftrightarrow>\<^sub>o App (roP b) ?q)" using u_rc_congr[OF CP tnn tq enn] by (simp add: subst0_def)
  have tPnn: "\<Gamma> \<turnstile> App (roP b) (Neg ?n) : Prop" by (rule has_type.App[OF tP tnn])
  have e1i: "\<Gamma> \<turnstile>\<^sub>U (App (roPp b) ?n \<longleftrightarrow>\<^sub>o App (roP b) (Neg ?n))"
    using u_rc_congr[of \<Gamma> "Var 0", OF _ tPpn tPnn e1] by (simp add: subst0_def)
  have idq: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (App (roPp b) ?n) (App (roP b) ?q)"
    by (rule u_rc_eq_of_iff[OF tPpn tPq u_rc_pc2[OF e1i e2]]) (insert tPpn tPq, (unfold prop_eval.simps)?, blast+)
  have CD: "Prop # \<Gamma> \<turnstile> Neg (\<box>\<^sub>o (Neg (Conj (shift b) (Var 0)))) : Prop"
    by (intro has_type.Neg typed_ObjBox has_type.Conj weaken_shift_type_ok[OF b]) simp
  have dia: "\<Gamma> \<turnstile>\<^sub>U (Neg (\<box>\<^sub>o (Neg (Conj b (App (roPp b) ?n)))) \<longleftrightarrow>\<^sub>o Neg (\<box>\<^sub>o (Neg (Conj b (App (roP b) ?q)))))"
    using u_rc_congr[OF CD tPpn tPq idq] by (simp add: subst0_def)
  text \<open>The two instances of R_b, at the pure operators P_b and P'_b.\<close>
  note r1 = roR_elim[OF b tq tn tP] and r2 = roR_elim[OF b tn tq tPp]
  have tg: "\<Gamma> \<turnstile> Imp (Conj b (rok b)) (roC b ?q) : Prop" by (intro has_type.Imp has_type.Conj b rok_ty tC)
  show ?thesis by (rule ro_pc7[OF st1 s3 s4 bP dia r1 r2 tg]) (unfold rok_def roC_def prop_eval.simps, blast)
qed

text \<open>Lemma 9: \<box>(b \<longrightarrow> \<kappa>(b)) \<longrightarrow> F_b(Q_b(x)).\<close>
theorem ro_relative: assumes b: "\<Gamma> \<turnstile> b : Prop" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (Imp b (rok b))) (roF b (roQ b x))"
proof -
  let ?q = "roQ b x"
  have tq: "\<Gamma> \<turnstile> ?q : Prop" by (rule roQ_ty[OF b x])
  have tC: "\<Gamma> \<turnstile> roC b ?q : Prop" by (rule roC_ty[OF b tq])
  have tk: "\<Gamma> \<turnstile> rok b : Prop" by (rule rok_ty[OF b])
  have g1: "\<Gamma> \<turnstile>\<^sub>U Imp (Imp b (rok b)) (Imp b (roC b ?q))"
    by (rule u_rc_pc1[OF ro_guarded[OF b x]]) (insert b tk tC, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF g1] and fq = roF_iff[OF b tq]
  have tg: "\<Gamma> \<turnstile> Imp (\<box>\<^sub>o (Imp b (rok b))) (roF b ?q) : Prop" by (intro has_type.Imp typed_ObjBox b tk roF_ty tq)
  show ?thesis by (rule u_rc_pc2[OF k fq tg]) (unfold prop_eval.simps, blast)
qed

end
