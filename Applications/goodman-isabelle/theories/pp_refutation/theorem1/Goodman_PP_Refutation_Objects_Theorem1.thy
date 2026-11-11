theory Goodman_PP_Refutation_Objects_Theorem1
  imports "Goodman_Integration_PP_Refutation_Stages.Goodman_PP_Refutation_Lemma6"
begin

text \<open>
  TECHNICAL THEORY (not a numbered result of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  The objects of Theorem 1 and of its proof:

    (R)  \<open>\<forall>X\<^sup>u(Pure(X) \<rightarrow> (\<box>(Xr) \<rightarrow> \<forall>p Xp))\<close>                   \<open>gr_R gr_Pure r\<close>
    \<open>D\<^sub>+ = \<lambda>Y\<^sup>u.\<lambda>p.(gp \<or> Y(gp) \<or> Y(\<not>(gp)))\<close>                    \<open>gr_Dplus\<close>
    \<open>D\<^sub>- = \<lambda>Y\<^sup>u.\<lambda>p.(\<not>(gp) \<or> Y(gp) \<or> Y(\<not>(gp)))\<close>                 \<open>gr_Dminus\<close>
    \<open>X\<^sub>+ = \<lambda>p.(gp \<or> Y\<^sub>0(gp) \<or> Y\<^sub>0(\<not>(gp)))\<close>                     \<open>gr_Xplus Y0\<close>
    \<open>X\<^sub>- = \<lambda>p.(\<not>(gp) \<or> Y\<^sub>0(gp) \<or> Y\<^sub>0(\<not>(gp)))\<close>                  \<open>gr_Xminus Y0\<close>
    \<open>K\<^sub>\<top> = \<lambda>p.\<top>\<close>                                            \<open>gr_Ktop\<close>

  together with instances of the development's existing \<open>pp_fun_prime\<close>
  (the note's fun', same shape) and \<open>pp_unary_recombination\<close>.
\<close>

section \<open>Further derived rules\<close>

lemma grk_eq_iff_rule:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop a b"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (a \<longleftrightarrow>\<^sub>o b)"
  by (rule grk_MP[OF d grk_eq_iff[OF grk_EqD1[OF grk_ty[OF d]] grk_EqD2[OF grk_ty[OF d]]]])

lemma grk_eq_neg_rule:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop a b"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Neg a) (Neg b)"
proof (rule grk_iff_eq, rule grk_PC1[OF grk_eq_iff_rule[OF d]])
  show "\<Gamma> \<turnstile> (Neg a \<longleftrightarrow>\<^sub>o Neg b) : Prop"
    by (gr_typ grk_EqD1[OF grk_ty[OF d]] grk_EqD2[OF grk_ty[OF d]])
qed gr_taut

lemma grk_eq_app_iff_rule:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop a b"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y a \<longleftrightarrow>\<^sub>o App Y b)"
proof -
  have at: "\<Gamma> \<turnstile> a : Prop" by (rule grk_EqD1[OF grk_ty[OF d]])
  have bt: "\<Gamma> \<turnstile> b : Prop" by (rule grk_EqD2[OF grk_ty[OF d]])
  have f: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App Y a) (App Y b)"
    by (rule grk_MP[OF d grk_LL[OF at bt yt]])
  have g: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App Y b) (App Y a)"
    by (rule grk_MP[OF grk_eq_sym_rule[OF d] grk_LL[OF bt at yt]])
  show ?thesis by (rule grk_iff_intro[OF f g])
qed

lemma grk_neg_I:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A ObjFalse"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg A"
proof -
  have ty: "\<Gamma> \<turnstile> Neg A : Prop" by (gr_typ grk_imp_ty1[OF d])
  show ?thesis by (rule grk_PC2[OF d CEV_axiom_proves_ObjTrue ty]) gr_taut
qed

lemma grk_neg_E:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A ObjFalse"
proof -
  have nt: "\<Gamma> \<turnstile> Neg A : Prop" by (rule grk_ty[OF d])
  have at: "\<Gamma> \<turnstile> A : Prop" using nt by (auto elim: has_type.cases)
  have ty: "\<Gamma> \<turnstile> Imp A ObjFalse : Prop" by (gr_typ at)
  show ?thesis by (rule grk_PC1[OF d ty]) gr_taut
qed

lemma grk_not_exists:
  assumes d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Exists \<sigma> A)"
proof -
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A ObjFalse" by (rule grk_neg_E[OF d])
  then have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (shift ObjFalse)" by (simp add: grs)
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> A) ObjFalse"
    by (rule grk_inst_imp[OF typed_ObjFalse])
  then show ?thesis by (rule grk_neg_I)
qed

lemma gr_subst0_Const: "subst0 M (Const c \<tau>) = Const c \<tau>"
  by (simp add: subst0_def)

lemma gr_pp_fun_shift: "shift (pp_fun \<sigma> M) = pp_fun \<sigma> (shift M)"
  by (simp add: shift_def pp_fun_def pp_Fun_def)

section \<open>(R)\<close>

text \<open>\<open>gr_AllP X\<close> is \<open>\<forall>p Xp\<close>.\<close>

definition gr_AllP :: "oterm \<Rightarrow> oterm" where
  "gr_AllP X = Forall Prop (App (shift X) (Var 0))"

definition gr_R :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_R c r =
    Forall gr_u
      (Imp (App (shift c) (Var 0))
        (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0))))"

lemma gr_AllP_rename[grs]: "rename \<rho> (gr_AllP X) = gr_AllP (rename \<rho> X)"
  by (simp add: gr_AllP_def grk_rename_lift_shift)

lemma gr_AllP_subst[grs]: "subst t (gr_AllP X) = gr_AllP (subst t X)"
  by (simp add: gr_AllP_def subst_lift_shift)

lemma gr_AllP_shift[grs]: "shift (gr_AllP X) = gr_AllP (shift X)"
  using gr_AllP_rename[of Suc X] by (simp add: shift_def)

lemma gr_AllP_subst0[grs]: "subst0 M (gr_AllP X) = gr_AllP (subst0 M X)"
  using gr_AllP_subst[of "case_nat M Var" X] by (simp add: subst0_def)

lemma typed_gr_AllP[gr_ty]: "\<Gamma> \<turnstile> X : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_AllP X : Prop"
  unfolding gr_AllP_def by gr_typ

lemma gr_R_rename[grs]: "rename \<rho> (gr_R c r) = gr_R (rename \<rho> c) (rename \<rho> r)"
  by (simp add: gr_R_def grs grk_rename_lift_shift)

lemma gr_R_subst[grs]: "subst t (gr_R c r) = gr_R (subst t c) (subst t r)"
  by (simp add: gr_R_def grs subst_lift_shift)

lemma gr_R_shift[grs]: "shift (gr_R c r) = gr_R (shift c) (shift r)"
  using gr_R_rename[of Suc c r] by (simp add: shift_def)

lemma gr_R_subst0[grs]: "subst0 M (gr_R c r) = gr_R (subst0 M c) (subst0 M r)"
  using gr_R_subst[of "case_nat M Var" c r] by (simp add: subst0_def)

lemma typed_gr_R[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> r : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_R c r : Prop"
  unfolding gr_R_def by gr_typ

lemma gr_AllP_E:
  assumes xt: "\<Gamma> \<turnstile> X : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_AllP X) (App X p)"
proof -
  have bt: "Prop # \<Gamma> \<turnstile> App (shift X) (Var 0) : Prop" by (gr_typ xt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Forall Prop (App (shift X) (Var 0))) (subst0 p (App (shift X) (Var 0)))"
    by (rule grk_UI[OF bt pt])
  then show ?thesis by (simp add: gr_AllP_def grs)
qed

lemma gr_AllP_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift H) (App (shift X) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_AllP X)"
  unfolding gr_AllP_def by (rule grk_gen_imp[OF ht d])

text \<open>Instantiating (R) at an operator \<open>X\<close>.\<close>

lemma gr_R_E:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and rt: "\<Gamma> \<turnstile> r : Prop" and xt: "\<Gamma> \<turnstile> X : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_R c r) (Imp (App c X) (Imp (\<box>\<^sub>o (App X r)) (gr_AllP X)))"
proof -
  let ?body = "Imp (App (shift c) (Var 0))
      (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0)))"
  have bt: "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct rt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u ?body) (subst0 X ?body)"
    by (rule grk_UI[OF bt xt])
  then show ?thesis by (simp add: gr_R_def grs)
qed

lemma gr_R_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H)
        (Imp (App (shift c) (Var 0)) (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0))))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_R c r)"
  unfolding gr_R_def by (rule grk_gen_imp[OF ht d])

section \<open>\<open>D\<^sub>+\<close>, \<open>D\<^sub>-\<close>, \<open>X\<^sub>+\<close>, \<open>X\<^sub>-\<close>\<close>

text \<open>The matrices \<open>gp \<or> Y(gp) \<or> Y(\<not>(gp))\<close> and \<open>\<not>(gp) \<or> Y(gp) \<or> Y(\<not>(gp))\<close>.\<close>

definition gr_XplusB :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_XplusB Y p =
    Disj (App gr_g p) (Disj (App Y (App gr_g p)) (App Y (Neg (App gr_g p))))"

definition gr_XminusB :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_XminusB Y p =
    Disj (Neg (App gr_g p)) (Disj (App Y (App gr_g p)) (App Y (Neg (App gr_g p))))"

definition gr_Dplus :: oterm where
  "gr_Dplus = Lam gr_u (Lam Prop (gr_XplusB (Var (Suc 0)) (Var 0)))"

definition gr_Dminus :: oterm where
  "gr_Dminus = Lam gr_u (Lam Prop (gr_XminusB (Var (Suc 0)) (Var 0)))"

definition gr_Xplus :: "oterm \<Rightarrow> oterm" where
  "gr_Xplus Y0 = Lam Prop (gr_XplusB (shift Y0) (Var 0))"

definition gr_Xminus :: "oterm \<Rightarrow> oterm" where
  "gr_Xminus Y0 = Lam Prop (gr_XminusB (shift Y0) (Var 0))"

lemma gr_XplusB_rename[grs]:
  "rename \<rho> (gr_XplusB Y p) = gr_XplusB (rename \<rho> Y) (rename \<rho> p)"
  by (simp add: gr_XplusB_def grs)

lemma gr_XplusB_subst[grs]:
  "subst t (gr_XplusB Y p) = gr_XplusB (subst t Y) (subst t p)"
  by (simp add: gr_XplusB_def grs)

lemma gr_XplusB_subst0[grs]:
  "subst0 M (gr_XplusB Y p) = gr_XplusB (subst0 M Y) (subst0 M p)"
  using gr_XplusB_subst[of "case_nat M Var" Y p] by (simp add: subst0_def)

lemma gr_XminusB_rename[grs]:
  "rename \<rho> (gr_XminusB Y p) = gr_XminusB (rename \<rho> Y) (rename \<rho> p)"
  by (simp add: gr_XminusB_def grs)

lemma gr_XminusB_subst[grs]:
  "subst t (gr_XminusB Y p) = gr_XminusB (subst t Y) (subst t p)"
  by (simp add: gr_XminusB_def grs)

lemma gr_XminusB_subst0[grs]:
  "subst0 M (gr_XminusB Y p) = gr_XminusB (subst0 M Y) (subst0 M p)"
  using gr_XminusB_subst[of "case_nat M Var" Y p] by (simp add: subst0_def)

lemma typed_gr_XplusB[gr_ty]:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_XplusB Y p : Prop"
  unfolding gr_XplusB_def by gr_typ

lemma typed_gr_XminusB[gr_ty]:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_XminusB Y p : Prop"
  unfolding gr_XminusB_def by gr_typ

lemma gr_XplusB_eval[gr_eval]:
  "prop_eval v (gr_XplusB Y p) =
    (v (App gr_g p) \<or> v (App Y (App gr_g p)) \<or> v (App Y (Neg (App gr_g p))))"
  by (simp add: gr_XplusB_def)

lemma gr_XminusB_eval[gr_eval]:
  "prop_eval v (gr_XminusB Y p) =
    (\<not> v (App gr_g p) \<or> v (App Y (App gr_g p)) \<or> v (App Y (Neg (App gr_g p))))"
  by (simp add: gr_XminusB_def)

lemma typed_gr_Dplus[gr_ty]: "\<Gamma> \<turnstile> gr_Dplus : gr_u \<rightarrow>\<^sub>o gr_u"
  unfolding gr_Dplus_def by gr_typ

lemma typed_gr_Dminus[gr_ty]: "\<Gamma> \<turnstile> gr_Dminus : gr_u \<rightarrow>\<^sub>o gr_u"
  unfolding gr_Dminus_def by gr_typ

lemma gr_Dplus_consts: "consts_of gr_Dplus = {}"
  by (simp add: gr_Dplus_def gr_XplusB_def gr_g_consts)

lemma gr_Dminus_consts: "consts_of gr_Dminus = {}"
  by (simp add: gr_Dminus_def gr_XminusB_def gr_g_consts)

text \<open>"Here \<open>g\<close> expands to a closed logical term, so \<open>D\<^sub>+\<close> does too, with type \<open>u \<rightarrow> u\<close>."\<close>

theorem gr_Dplus_logical:
  "[] \<turnstile> gr_Dplus : gr_u \<rightarrow>\<^sub>o gr_u \<and> pp_logical_vocabulary gr_Dplus"
  by (simp add: typed_gr_Dplus gr_Dplus_consts pp_logical_vocabulary_def)

theorem gr_Dminus_logical:
  "[] \<turnstile> gr_Dminus : gr_u \<rightarrow>\<^sub>o gr_u \<and> pp_logical_vocabulary gr_Dminus"
  by (simp add: typed_gr_Dminus gr_Dminus_consts pp_logical_vocabulary_def)

lemma typed_gr_Xplus[gr_ty]: "\<Gamma> \<turnstile> Y0 : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_Xplus Y0 : gr_u"
  unfolding gr_Xplus_def by gr_typ

lemma typed_gr_Xminus[gr_ty]: "\<Gamma> \<turnstile> Y0 : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_Xminus Y0 : gr_u"
  unfolding gr_Xminus_def by gr_typ

text \<open>Unfolding \<open>X\<^sub>+p\<close> and \<open>X\<^sub>-p\<close> by beta.\<close>

lemma gr_Xplus_app:
  assumes yt: "\<Gamma> \<turnstile> Y0 : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xplus Y0) p \<longleftrightarrow>\<^sub>o gr_XplusB Y0 p)"
proof -
  have ty: "\<Gamma> \<turnstile> App (gr_Xplus Y0) p : Prop" by (gr_typ yt pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam Prop (gr_XplusB (shift Y0) (Var 0))) p \<longleftrightarrow>\<^sub>o
        subst0 p (gr_XplusB (shift Y0) (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_Xplus_def]])
  then show ?thesis by (simp add: gr_Xplus_def grs)
qed

lemma gr_Xminus_app:
  assumes yt: "\<Gamma> \<turnstile> Y0 : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xminus Y0) p \<longleftrightarrow>\<^sub>o gr_XminusB Y0 p)"
proof -
  have ty: "\<Gamma> \<turnstile> App (gr_Xminus Y0) p : Prop" by (gr_typ yt pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam Prop (gr_XminusB (shift Y0) (Var 0))) p \<longleftrightarrow>\<^sub>o
        subst0 p (gr_XminusB (shift Y0) (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_Xminus_def]])
  then show ?thesis by (simp add: gr_Xminus_def grs)
qed

text \<open>\<open>D\<^sub>+Y\<^sub>0 = X\<^sub>+\<close> and \<open>D\<^sub>-Y\<^sub>0 = X\<^sub>-\<close>, by beta ("applied to the pure \<open>Y\<^sub>0\<close>").\<close>

lemma gr_Dplus_app_eq:
  assumes yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq gr_u (App gr_Dplus Y0) (gr_Xplus Y0)"
proof -
  let ?body = "Lam Prop (gr_XplusB (Var (Suc 0)) (Var 0))"
  have r: "rename Suc Y0 = shift Y0" by (simp add: shift_def)
  have step: "compatible_step beta_contract (App (Lam gr_u ?body) Y0) (subst0 Y0 ?body)"
    by (rule compatible_step.root, rule beta_contract.beta)
  have e: "subst0 Y0 ?body = gr_Xplus Y0"
    by (simp add: subst0_def gr_Xplus_def grs r)
  have st: "compatible_step beta_contract (App gr_Dplus Y0) (gr_Xplus Y0)"
    using step by (simp only: e gr_Dplus_def)
  have at: "\<Gamma> \<turnstile> App gr_Dplus Y0 : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule has_type.App[OF typed_gr_Dplus yt])
  have bt: "\<Gamma> \<turnstile> gr_Xplus Y0 : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule typed_gr_Xplus[OF yt])
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq pp_unary_ty (App gr_Dplus Y0) (gr_Xplus Y0)"
    by (rule CEV_unary_eq_of_beta_step[OF at bt st])
  then show ?thesis unfolding pp_unary_ty_def by (rule CEV_axiom_proves.Base)
qed

lemma gr_Dminus_app_eq:
  assumes yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq gr_u (App gr_Dminus Y0) (gr_Xminus Y0)"
proof -
  let ?body = "Lam Prop (gr_XminusB (Var (Suc 0)) (Var 0))"
  have r: "rename Suc Y0 = shift Y0" by (simp add: shift_def)
  have step: "compatible_step beta_contract (App (Lam gr_u ?body) Y0) (subst0 Y0 ?body)"
    by (rule compatible_step.root, rule beta_contract.beta)
  have e: "subst0 Y0 ?body = gr_Xminus Y0"
    by (simp add: subst0_def gr_Xminus_def grs r)
  have st: "compatible_step beta_contract (App gr_Dminus Y0) (gr_Xminus Y0)"
    using step by (simp only: e gr_Dminus_def)
  have at: "\<Gamma> \<turnstile> App gr_Dminus Y0 : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule has_type.App[OF typed_gr_Dminus yt])
  have bt: "\<Gamma> \<turnstile> gr_Xminus Y0 : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule typed_gr_Xminus[OF yt])
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq pp_unary_ty (App gr_Dminus Y0) (gr_Xminus Y0)"
    by (rule CEV_unary_eq_of_beta_step[OF at bt st])
  then show ?thesis unfolding pp_unary_ty_def by (rule CEV_axiom_proves.Base)
qed

section \<open>\<open>K\<^sub>\<top> = \<lambda>p.\<top>\<close>\<close>

definition gr_Ktop :: oterm where
  "gr_Ktop = Lam Prop ObjTrue"

lemma gr_Ktop_rename[grs]: "rename \<rho> gr_Ktop = gr_Ktop"
  by (simp add: gr_Ktop_def grs)

lemma gr_Ktop_subst[grs]: "subst t gr_Ktop = gr_Ktop"
  by (simp add: gr_Ktop_def grs)

lemma gr_Ktop_shift[grs]: "shift gr_Ktop = gr_Ktop"
  by (simp add: shift_def grs)

lemma gr_Ktop_subst0[grs]: "subst0 M gr_Ktop = gr_Ktop"
  by (simp add: subst0_def grs)

lemma typed_gr_Ktop[gr_ty]: "\<Gamma> \<turnstile> gr_Ktop : gr_u"
  unfolding gr_Ktop_def by gr_typ

lemma gr_Ktop_consts: "consts_of gr_Ktop = {}"
  by (simp add: gr_Ktop_def ObjTrue_def)

lemma gr_Ktop_app:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Ktop p \<longleftrightarrow>\<^sub>o ObjTrue)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_Ktop p : Prop" by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam Prop ObjTrue) p \<longleftrightarrow>\<^sub>o subst0 p ObjTrue)"
    by (rule grk_beta1[OF ty[unfolded gr_Ktop_def]])
  then show ?thesis by (simp add: gr_Ktop_def grs)
qed

text \<open>\<open>K\<^sub>\<top>p = \<top>\<close>.\<close>

lemma gr_Ktop_app_eq:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_Ktop p) ObjTrue"
  by (rule grk_iff_eq[OF gr_Ktop_app[OF pt]])

text \<open>If \<open>X = K\<^sub>\<top>\<close> then \<open>Xp = \<top>\<close> (Leibniz's law at \<open>\<lambda>Z.(Zp = \<top>)\<close>).\<close>

lemma gr_Ktop_eq_box:
  assumes xt: "\<Gamma> \<turnstile> X : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u X gr_Ktop) (\<box>\<^sub>o (App X p))"
proof -
  let ?F = "Lam gr_u (\<box>\<^sub>o (App (Var 0) (shift p)))"
  have ft: "\<Gamma> \<turnstile> ?F : gr_u \<rightarrow>\<^sub>o Prop" by (gr_typ pt)
  have s: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u X gr_Ktop) (Eq gr_u gr_Ktop X)"
    by (rule grk_eq_sym[OF xt typed_gr_Ktop])
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq gr_u gr_Ktop X) (Imp (App ?F gr_Ktop) (App ?F X))"
    by (rule grk_LL[OF typed_gr_Ktop xt ft])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App ?F gr_Ktop \<longleftrightarrow>\<^sub>o subst0 gr_Ktop (\<box>\<^sub>o (App (Var 0) (shift p))))"
    by (rule grk_beta1[OF has_type.App[OF ft typed_gr_Ktop]])
  then have bK: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F gr_Ktop \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (App gr_Ktop p))"
    by (simp add: grs)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F X \<longleftrightarrow>\<^sub>o subst0 X (\<box>\<^sub>o (App (Var 0) (shift p))))"
    by (rule grk_beta1[OF has_type.App[OF ft xt]])
  then have bX: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F X \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (App X p))"
    by (simp add: grs)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_Ktop p) ObjTrue" by (rule gr_Ktop_app_eq[OF pt])
  then have kt: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (App gr_Ktop p)" by (simp only: ObjBox_def)
  have ty: "\<Gamma> \<turnstile> Imp (Eq gr_u X gr_Ktop) (\<box>\<^sub>o (App X p)) : Prop" by (gr_typ xt pt)
  show ?thesis by (rule grk_PC5[OF s ll bK bX kt ty]) gr_taut
qed

section \<open>Instances of fun' and of unary Recombination\<close>

text \<open>
  The note's \<open>fun'(r)\<close>,
     \<open>\<forall>X\<^sup>uY\<^sup>u((Pure(X) & Pure(Y)) \<rightarrow> (Xr = Yr \<rightarrow> X = Y))\<close>,
  is the development's \<open>pp_fun_prime r\<close> (same shape).  Its instance at
  operators \<open>X\<close>, \<open>Y\<close>, by the existing lemma \<open>CEV_axiom_from_fun_prime\<close> and the
  deduction theorem of the local-assumption calculus (no necessitation).
\<close>

lemma gr_fun_prime_inst:
  assumes rt: "\<Gamma> \<turnstile> r : Prop" and xt: "\<Gamma> \<turnstile> X : gr_u" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Imp (pp_pure gr_u X) (Imp (pp_pure gr_u Y)
      (Imp (Eq Prop (App X r) (App Y r)) (Eq gr_u X Y))))"
proof -
  let ?a1 = "pp_fun_prime r"
  let ?a2 = "pp_pure gr_u X"
  let ?a3 = "pp_pure gr_u Y"
  let ?a4 = "Eq Prop (App X r) (App Y r)"
  let ?S = "insert ?a4 (insert ?a3 (insert ?a2 {?a1}))"
  have t1: "\<Gamma> \<turnstile> ?a1 : Prop" by (rule typed_pp_fun_prime[OF rt])
  have t2: "\<Gamma> \<turnstile> ?a2 : Prop" by (gr_typ xt)
  have t3: "\<Gamma> \<turnstile> ?a3 : Prop" by (gr_typ yt)
  have t4: "\<Gamma> \<turnstile> ?a4 : Prop" by (gr_typ rt xt yt)
  have xt': "\<Gamma> \<turnstile> X : pp_unary_ty" using xt by (simp add: pp_unary_ty_def)
  have yt': "\<Gamma> \<turnstile> Y : pp_unary_ty" using yt by (simp add: pp_unary_ty_def)
  have d1: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?a1"
    by (rule CEV_axiom_from.Assumption) (simp_all add: t1)
  have d2: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty X"
    unfolding pp_unary_ty_def by (rule CEV_axiom_from.Assumption) (simp_all add: t2)
  have d3: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Y"
    unfolding pp_unary_ty_def by (rule CEV_axiom_from.Assumption) (simp_all add: t3)
  have d4: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?a4"
    by (rule CEV_axiom_from.Assumption) (simp_all add: t4)
  have "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty X Y"
    by (rule CEV_axiom_from_fun_prime[OF rt xt' yt' d1 d2 d3 d4])
  then have e: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq gr_u X Y"
    by (simp only: pp_unary_ty_def)
  have s4: "\<Gamma> ; T ; insert ?a3 (insert ?a2 {?a1}) \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?a4 (Eq gr_u X Y)"
    by (rule CEV_axiom_from_deduction[OF t4 e])
  have s3: "\<Gamma> ; T ; insert ?a2 {?a1} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?a3 (Imp ?a4 (Eq gr_u X Y))"
    by (rule CEV_axiom_from_deduction[OF t3 s4])
  have s2: "\<Gamma> ; T ; {?a1} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?a2 (Imp ?a3 (Imp ?a4 (Eq gr_u X Y)))"
    by (rule CEV_axiom_from_deduction[OF t2 s3])
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF t1 s2])
qed

text \<open>
  "Unary Recombination states
     \<open>\<forall>X r((Pure(X) & Fun(r)) \<rightarrow> (\<box>(Xr) \<rightarrow> \<forall>p Xp))\<close>."
  This is the development's \<open>pp_unary_recombination\<close>; its instance at \<open>X\<close>, \<open>r\<close>:
\<close>

lemma gr_unary_recombination_inst:
  assumes ur: "pp_unary_recombination \<in> T"
    and xt: "\<Gamma> \<turnstile> X : gr_u" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (pp_pure gr_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (gr_AllP X))"
proof -
  let ?B1 = "Imp (Conj (pp_pure gr_u (Var 1)) (pp_fun Prop (Var 0)))
      (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0))))"
  let ?B2 = "Imp (Conj (pp_pure gr_u (shift X)) (pp_fun Prop (Var 0)))
      (Imp (\<box>\<^sub>o (App (shift X) (Var 0))) (gr_AllP (shift X)))"
  have ut: "\<Gamma> \<turnstile> Forall gr_u (Forall Prop ?B1) : Prop"
    by (rule infer_type_sound)
      (simp add: pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have ax: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall gr_u (Forall Prop ?B1)"
    using CEV_axiom_proves.Axiom[OF ur, of \<Gamma>] ut by (simp only: pp_unary_recombination_def)
  have t1: "gr_u # \<Gamma> \<turnstile> Forall Prop ?B1 : Prop" by (rule grk_ForallD[OF ut])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u (Forall Prop ?B1)) (subst0 X (Forall Prop ?B1))"
    by (rule grk_UI[OF t1 xt])
  then have i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u (Forall Prop ?B1)) (Forall Prop ?B2)"
    by (simp add: grk_subst0_Forall grs pp_pure_def pp_fun_def pp_Pure_def pp_Fun_def
        gr_AllP_def shift_def numeral_2_eq_2)
  have t2: "Prop # \<Gamma> \<turnstile> ?B2 : Prop" by (gr_typ xt typed_pp_fun)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall Prop ?B2) (subst0 r ?B2)"
    by (rule grk_UI[OF t2 rt])
  then have i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall Prop ?B2)
      (Imp (Conj (pp_pure gr_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (gr_AllP X)))"
    by (simp add: grs pp_pure_def pp_fun_def pp_Pure_def pp_Fun_def gr_subst0_Const)
  show ?thesis by (rule grk_MP[OF grk_MP[OF ax i1] i2])
qed

end
