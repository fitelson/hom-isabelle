theory Goodman_PP_Refutation_Objects_Induction
  imports Goodman_PP_Refutation_Objects_Stage
begin

text \<open>
  TECHNICAL THEORY (not a numbered result of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  The formulas occurring in the statement and proof of Lemma 4:

    union condition for Stage:  "\<open>B\<close> is pure and every \<open>s\<close> with \<open>Bs\<close> has a
        stage \<open>Y \<subseteq> B\<close> with \<open>Ys\<close>"                   \<open>gr_SCov c B\<close> (the cover)
    condition 1:  \<open>\<Psi>(K\<^sub>\<bottom>)\<close>                              \<open>gr_Ind1 \<Psi>\<close>
    condition 2:  "If \<open>Y\<close> is a stage satisfying \<open>\<Psi>\<close>, then \<open>\<Psi>(\<Sigma>Y)\<close>"
                                                        \<open>gr_Ind2 c \<Psi>\<close>
    condition 3:  "If \<open>B\<close> is pure and each \<open>s\<close> with \<open>Bs\<close> has a stage
        \<open>Y \<subseteq> B\<close> with \<open>\<Psi>(Y)\<close> and \<open>Ys\<close>, then \<open>\<Psi>(B)\<close>"    \<open>gr_Ind3 c \<Psi>\<close>
    \<open>\<W> = \<lambda>Y\<^sup>u.(Stage(Y) & \<Psi>(Y))\<close>                      \<open>gr_W c \<Psi>\<close>

  \<open>\<Psi>\<close> is an arbitrary term of type \<open>u \<rightarrow> t\<close> in the ambient context, so
  "parameters are allowed in \<open>\<Psi>\<close>"; the shifts realize "bound variables are
  chosen fresh for them".
\<close>

section \<open>Stage witnesses and covers\<close>

text \<open>"a stage \<open>Y \<subseteq> B\<close> with \<open>Ys\<close>".\<close>

definition gr_swit :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_swit c B s Y = Conj (gr_Stage c Y) (Conj (gr_sub Y B) (App Y s))"

definition gr_SCov :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_SCov c B =
    gr_cov B (gr_swit (shift (shift c)) (shift (shift B)) (Var (Suc 0)) (Var 0))"

text \<open>"a stage \<open>Y \<subseteq> B\<close> with \<open>\<Psi>(Y)\<close> and \<open>Ys\<close>".\<close>

definition gr_iwit :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_iwit c \<Psi> B s Y =
    Conj (gr_Stage c Y) (Conj (gr_sub Y B) (Conj (App \<Psi> Y) (App Y s)))"

definition gr_ICov :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_ICov c \<Psi> B =
    gr_cov B (gr_iwit (shift (shift c)) (shift (shift \<Psi>)) (shift (shift B))
      (Var (Suc 0)) (Var 0))"

text \<open>The instance of the cover at one proposition \<open>s\<close>.\<close>

definition gr_IEx :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_IEx c \<Psi> B s =
    Exists gr_u (gr_iwit (shift c) (shift \<Psi>) (shift B) (shift s) (Var 0))"

lemma gr_swit_rename[grs]:
  "rename \<rho> (gr_swit c B s Y) =
    gr_swit (rename \<rho> c) (rename \<rho> B) (rename \<rho> s) (rename \<rho> Y)"
  by (simp add: gr_swit_def grs)

lemma gr_swit_subst[grs]:
  "subst t (gr_swit c B s Y) = gr_swit (subst t c) (subst t B) (subst t s) (subst t Y)"
  by (simp add: gr_swit_def grs)

lemma gr_swit_shift[grs]:
  "shift (gr_swit c B s Y) = gr_swit (shift c) (shift B) (shift s) (shift Y)"
  using gr_swit_rename[of Suc c B s Y] by (simp add: shift_def)

lemma gr_swit_subst0[grs]:
  "subst0 M (gr_swit c B s Y) =
    gr_swit (subst0 M c) (subst0 M B) (subst0 M s) (subst0 M Y)"
  using gr_swit_subst[of "case_nat M Var" c B s Y] by (simp add: subst0_def)

lemma typed_gr_swit[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> s : Prop \<Longrightarrow> \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow>
    \<Gamma> \<turnstile> gr_swit c B s Y : Prop"
  unfolding gr_swit_def by gr_typ

lemma gr_swit_eval[gr_eval]:
  "prop_eval v (gr_swit c B s Y) =
    (prop_eval v (gr_Stage c Y) \<and> prop_eval v (gr_sub Y B) \<and> v (App Y s))"
  by (simp add: gr_swit_def)

lemma gr_SCov_rename[grs]: "rename \<rho> (gr_SCov c B) = gr_SCov (rename \<rho> c) (rename \<rho> B)"
  by (simp add: gr_SCov_def gr_cov_rename grs grk_rename_lift_shift)

lemma gr_SCov_subst[grs]: "subst t (gr_SCov c B) = gr_SCov (subst t c) (subst t B)"
  by (simp add: gr_SCov_def gr_cov_subst grs subst_lift_shift)

lemma gr_SCov_shift[grs]: "shift (gr_SCov c B) = gr_SCov (shift c) (shift B)"
  using gr_SCov_rename[of Suc c B] by (simp add: shift_def)

lemma gr_SCov_subst0[grs]: "subst0 M (gr_SCov c B) = gr_SCov (subst0 M c) (subst0 M B)"
  using gr_SCov_subst[of "case_nat M Var" c B] by (simp add: subst0_def)

lemma typed_gr_SCov[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_SCov c B : Prop"
  unfolding gr_SCov_def by gr_typ

lemma gr_iwit_rename[grs]:
  "rename \<rho> (gr_iwit c \<Psi> B s Y) =
    gr_iwit (rename \<rho> c) (rename \<rho> \<Psi>) (rename \<rho> B) (rename \<rho> s) (rename \<rho> Y)"
  by (simp add: gr_iwit_def grs)

lemma gr_iwit_subst[grs]:
  "subst t (gr_iwit c \<Psi> B s Y) =
    gr_iwit (subst t c) (subst t \<Psi>) (subst t B) (subst t s) (subst t Y)"
  by (simp add: gr_iwit_def grs)

lemma gr_iwit_shift[grs]:
  "shift (gr_iwit c \<Psi> B s Y) =
    gr_iwit (shift c) (shift \<Psi>) (shift B) (shift s) (shift Y)"
  using gr_iwit_rename[of Suc c \<Psi> B s Y] by (simp add: shift_def)

lemma gr_iwit_subst0[grs]:
  "subst0 M (gr_iwit c \<Psi> B s Y) =
    gr_iwit (subst0 M c) (subst0 M \<Psi>) (subst0 M B) (subst0 M s) (subst0 M Y)"
  using gr_iwit_subst[of "case_nat M Var" c \<Psi> B s Y] by (simp add: subst0_def)

lemma typed_gr_iwit[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> s : Prop \<Longrightarrow>
    \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_iwit c \<Psi> B s Y : Prop"
  unfolding gr_iwit_def by gr_typ

lemma gr_iwit_eval[gr_eval]:
  "prop_eval v (gr_iwit c \<Psi> B s Y) =
    (prop_eval v (gr_Stage c Y) \<and> prop_eval v (gr_sub Y B) \<and> v (App \<Psi> Y) \<and> v (App Y s))"
  by (simp add: gr_iwit_def)

lemma gr_ICov_rename[grs]:
  "rename \<rho> (gr_ICov c \<Psi> B) = gr_ICov (rename \<rho> c) (rename \<rho> \<Psi>) (rename \<rho> B)"
  by (simp add: gr_ICov_def gr_cov_rename grs grk_rename_lift_shift)

lemma gr_ICov_subst[grs]:
  "subst t (gr_ICov c \<Psi> B) = gr_ICov (subst t c) (subst t \<Psi>) (subst t B)"
  by (simp add: gr_ICov_def gr_cov_subst grs subst_lift_shift)

lemma gr_ICov_shift[grs]:
  "shift (gr_ICov c \<Psi> B) = gr_ICov (shift c) (shift \<Psi>) (shift B)"
  using gr_ICov_rename[of Suc c \<Psi> B] by (simp add: shift_def)

lemma gr_ICov_subst0[grs]:
  "subst0 M (gr_ICov c \<Psi> B) = gr_ICov (subst0 M c) (subst0 M \<Psi>) (subst0 M B)"
  using gr_ICov_subst[of "case_nat M Var" c \<Psi> B] by (simp add: subst0_def)

lemma typed_gr_ICov[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_ICov c \<Psi> B : Prop"
  unfolding gr_ICov_def by gr_typ

lemma gr_IEx_rename[grs]:
  "rename \<rho> (gr_IEx c \<Psi> B s) =
    gr_IEx (rename \<rho> c) (rename \<rho> \<Psi>) (rename \<rho> B) (rename \<rho> s)"
  by (simp add: gr_IEx_def grs grk_rename_lift_shift)

lemma gr_IEx_subst[grs]:
  "subst t (gr_IEx c \<Psi> B s) = gr_IEx (subst t c) (subst t \<Psi>) (subst t B) (subst t s)"
  by (simp add: gr_IEx_def grs subst_lift_shift)

lemma gr_IEx_shift[grs]:
  "shift (gr_IEx c \<Psi> B s) = gr_IEx (shift c) (shift \<Psi>) (shift B) (shift s)"
  using gr_IEx_rename[of Suc c \<Psi> B s] by (simp add: shift_def)

lemma gr_IEx_subst0[grs]:
  "subst0 M (gr_IEx c \<Psi> B s) =
    gr_IEx (subst0 M c) (subst0 M \<Psi>) (subst0 M B) (subst0 M s)"
  using gr_IEx_subst[of "case_nat M Var" c \<Psi> B s] by (simp add: subst0_def)

lemma typed_gr_IEx[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> s : Prop \<Longrightarrow>
    \<Gamma> \<turnstile> gr_IEx c \<Psi> B s : Prop"
  unfolding gr_IEx_def by gr_typ

text \<open>"an instance \<open>Bs\<close> has a stage \<open>Y \<subseteq> B\<close> with \<open>Ys\<close> and \<open>\<Psi>(Y)\<close>".\<close>

lemma gr_ICov_E:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and bt: "\<Gamma> \<turnstile> B : gr_u"
    and st: "\<Gamma> \<turnstile> s : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ICov c \<Psi> B) (Imp (App B s) (gr_IEx c \<Psi> B s))"
proof -
  let ?W = "gr_iwit (shift (shift c)) (shift (shift \<Psi>)) (shift (shift B)) (Var (Suc 0)) (Var 0)"
  have wt: "gr_u # Prop # \<Gamma> \<turnstile> ?W : Prop" by (gr_typ ct pst bt)
  have r: "rename Suc s = shift s" by (simp add: shift_def)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_cov B ?W) (Imp (App B s) (Exists gr_u (subst (lift_subst (case_nat s Var)) ?W)))"
    by (rule gr_cov_inst[OF bt wt st])
  then show ?thesis by (simp add: gr_ICov_def gr_IEx_def grs subst_lift_shift r)
qed

lemma gr_IEx_E:
  assumes qt: "\<Gamma> \<turnstile> Q : Prop"
    and d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_iwit (shift c) (shift \<Psi>) (shift B) (shift s) (Var 0)) (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_IEx c \<Psi> B s) Q"
  unfolding gr_IEx_def by (rule grk_inst_imp[OF qt d])

section \<open>The three conditions on \<open>\<Psi>\<close>\<close>

definition gr_Ind1 :: "oterm \<Rightarrow> oterm" where
  "gr_Ind1 \<Psi> = App \<Psi> gr_Kbot"

definition gr_Ind2 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Ind2 c \<Psi> =
    Forall gr_u
      (Imp (Conj (gr_Stage (shift c) (Var 0)) (App (shift \<Psi>) (Var 0)))
        (App (shift \<Psi>) (App gr_Sigma (Var 0))))"

definition gr_Ind3 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Ind3 c \<Psi> =
    Forall gr_u
      (Imp (Conj (App (shift c) (Var 0)) (gr_ICov (shift c) (shift \<Psi>) (Var 0)))
        (App (shift \<Psi>) (Var 0)))"

lemma gr_Ind1_rename[grs]: "rename \<rho> (gr_Ind1 \<Psi>) = gr_Ind1 (rename \<rho> \<Psi>)"
  by (simp add: gr_Ind1_def grs)

lemma gr_Ind1_shift[grs]: "shift (gr_Ind1 \<Psi>) = gr_Ind1 (shift \<Psi>)"
  using gr_Ind1_rename[of Suc \<Psi>] by (simp add: shift_def)

lemma gr_Ind2_rename[grs]: "rename \<rho> (gr_Ind2 c \<Psi>) = gr_Ind2 (rename \<rho> c) (rename \<rho> \<Psi>)"
  by (simp add: gr_Ind2_def grs grk_rename_lift_shift)

lemma gr_Ind2_shift[grs]: "shift (gr_Ind2 c \<Psi>) = gr_Ind2 (shift c) (shift \<Psi>)"
  using gr_Ind2_rename[of Suc c \<Psi>] by (simp add: shift_def)

lemma gr_Ind3_rename[grs]: "rename \<rho> (gr_Ind3 c \<Psi>) = gr_Ind3 (rename \<rho> c) (rename \<rho> \<Psi>)"
  by (simp add: gr_Ind3_def grs grk_rename_lift_shift)

lemma gr_Ind3_shift[grs]: "shift (gr_Ind3 c \<Psi>) = gr_Ind3 (shift c) (shift \<Psi>)"
  using gr_Ind3_rename[of Suc c \<Psi>] by (simp add: shift_def)

lemma typed_gr_Ind1[gr_ty]: "\<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Ind1 \<Psi> : Prop"
  unfolding gr_Ind1_def by gr_typ

lemma typed_gr_Ind2[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Ind2 c \<Psi> : Prop"
  unfolding gr_Ind2_def by gr_typ

lemma typed_gr_Ind3[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Ind3 c \<Psi> : Prop"
  unfolding gr_Ind3_def by gr_typ

lemma gr_Ind1_eval[gr_eval]: "prop_eval v (gr_Ind1 \<Psi>) = v (App \<Psi> gr_Kbot)"
  by (simp add: gr_Ind1_def)

lemma gr_Ind2_E:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Ind2 c \<Psi>) (Imp (Conj (gr_Stage c Y) (App \<Psi> Y)) (App \<Psi> (App gr_Sigma Y)))"
proof -
  let ?body = "Imp (Conj (gr_Stage (shift c) (Var 0)) (App (shift \<Psi>) (Var 0)))
      (App (shift \<Psi>) (App gr_Sigma (Var 0)))"
  have bt: "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct pst)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u ?body) (subst0 Y ?body)"
    by (rule grk_UI[OF bt yt])
  then show ?thesis by (simp add: gr_Ind2_def grs)
qed

lemma gr_Ind2_I:
  assumes d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift c) (Var 0)) (App (shift \<Psi>) (Var 0)))
        (App (shift \<Psi>) (App gr_Sigma (Var 0)))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind2 c \<Psi>"
  unfolding gr_Ind2_def by (rule grk_gen[OF d])

lemma gr_Ind3_E:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and bt: "\<Gamma> \<turnstile> B : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Ind3 c \<Psi>) (Imp (Conj (App c B) (gr_ICov c \<Psi> B)) (App \<Psi> B))"
proof -
  let ?body = "Imp (Conj (App (shift c) (Var 0)) (gr_ICov (shift c) (shift \<Psi>) (Var 0)))
      (App (shift \<Psi>) (Var 0))"
  have bt': "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct pst)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u ?body) (subst0 B ?body)"
    by (rule grk_UI[OF bt' bt])
  then show ?thesis by (simp add: gr_Ind3_def grs)
qed

lemma gr_Ind3_I:
  assumes d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App (shift c) (Var 0)) (gr_ICov (shift c) (shift \<Psi>) (Var 0)))
        (App (shift \<Psi>) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind3 c \<Psi>"
  unfolding gr_Ind3_def by (rule grk_gen[OF d])

section \<open>\<open>\<W> = \<lambda>Y.(Stage(Y) & \<Psi>(Y))\<close>\<close>

definition gr_W :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_W c \<Psi> = Lam gr_u (Conj (gr_Stage (shift c) (Var 0)) (App (shift \<Psi>) (Var 0)))"

lemma gr_W_rename[grs]: "rename \<rho> (gr_W c \<Psi>) = gr_W (rename \<rho> c) (rename \<rho> \<Psi>)"
  by (simp add: gr_W_def grs grk_rename_lift_shift)

lemma gr_W_subst[grs]: "subst t (gr_W c \<Psi>) = gr_W (subst t c) (subst t \<Psi>)"
  by (simp add: gr_W_def grs subst_lift_shift)

lemma gr_W_shift[grs]: "shift (gr_W c \<Psi>) = gr_W (shift c) (shift \<Psi>)"
  using gr_W_rename[of Suc c \<Psi>] by (simp add: shift_def)

lemma gr_W_subst0[grs]: "subst0 M (gr_W c \<Psi>) = gr_W (subst0 M c) (subst0 M \<Psi>)"
  using gr_W_subst[of "case_nat M Var" c \<Psi>] by (simp add: subst0_def)

lemma typed_gr_W[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> \<Psi> : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_W c \<Psi> : gr_cls"
  unfolding gr_W_def by gr_typ

lemma gr_W_app:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_W c \<Psi>) Y \<longleftrightarrow>\<^sub>o Conj (gr_Stage c Y) (App \<Psi> Y))"
proof -
  let ?body = "Conj (gr_Stage (shift c) (Var 0)) (App (shift \<Psi>) (Var 0))"
  have ty: "\<Gamma> \<turnstile> App (gr_W c \<Psi>) Y : Prop" by (gr_typ ct pst yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam gr_u ?body) Y \<longleftrightarrow>\<^sub>o subst0 Y ?body)"
    by (rule grk_beta1[OF ty[unfolded gr_W_def]])
  then show ?thesis by (simp add: gr_W_def grs)
qed

end
