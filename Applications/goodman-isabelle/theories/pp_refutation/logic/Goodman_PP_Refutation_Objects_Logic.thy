theory Goodman_PP_Refutation_Objects_Logic
  imports "Goodman_Integration_PP_Refutation_Kit.Goodman_PP_Refutation_Kit"
begin

text \<open>
  TECHNICAL THEORY (not a numbered result of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  The objects of the first part of the note, "A logical fixed-point
  construction", with their typing, de Bruijn, beta and quantifier
  interfaces:

    (1)  \<open>\<Sigma> = \<lambda>Y\<^sup>u.\<lambda>p.(\<box>(p \<or> Yp \<or> Y(\<not>p)) \<or> \<box>(\<not>p \<or> Yp \<or> Y(\<not>p)))\<close>   \<open>gr_Sigma\<close>
    (2)  \<open>Pre(W) = \<box>(\<Sigma>W \<subseteq> W)\<close>                                  \<open>gr_Pre W\<close>
    (3)  \<open>L = \<lambda>p.\<forall>W\<^sup>u(Pre(W) \<rightarrow> Wp)\<close>                             \<open>gr_L\<close>
         \<open>V \<subseteq> W\<close> for \<open>\<forall>p(Vp \<rightarrow> Wp)\<close>                              \<open>gr_sub V W\<close>
         \<open>g = \<lambda>p.(p & Lp)\<close> (Lemma 3)                             \<open>gr_g\<close>
         \<open>q = r & Lr\<close> (the beta-normal form of \<open>g r\<close>)             \<open>gr_q r\<close>

  \<open>gr_u\<close> is the note's type \<open>u = t \<rightarrow> t\<close>.  \<open>(\<Sigma>Y)p\<close> is the term
  \<open>App (App gr_Sigma Y) p\<close>; \<open>gr_sg Y p\<close> is its beta-normal body, and
  \<open>gr_sgA\<close>, \<open>gr_sgB\<close> are the matrices of its two boxed disjuncts.
  \<open>Pre(W)\<close> is a meta-level abbreviation, as in the note.
\<close>

section \<open>The symmetrized \<open>\<Sigma>\<close>\<close>

definition gr_sgA :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_sgA Y p = Disj p (Disj (App Y p) (App Y (Neg p)))"

definition gr_sgB :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_sgB Y p = Disj (Neg p) (Disj (App Y p) (App Y (Neg p)))"

text \<open>\<open>gr_sg Y p\<close> is \<open>\<box>(p \<or> Yp \<or> Y\<not>p) \<or> \<box>(\<not>p \<or> Yp \<or> Y\<not>p)\<close>.\<close>

definition gr_sg :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_sg Y p = Disj (\<box>\<^sub>o (gr_sgA Y p)) (\<box>\<^sub>o (gr_sgB Y p))"

definition gr_Sigma :: oterm where
  "gr_Sigma = Lam gr_u (Lam Prop (gr_sg (Var (Suc 0)) (Var 0)))"

lemma gr_sgA_rename[grs]: "rename \<rho> (gr_sgA Y p) = gr_sgA (rename \<rho> Y) (rename \<rho> p)"
  by (simp add: gr_sgA_def)

lemma gr_sgB_rename[grs]: "rename \<rho> (gr_sgB Y p) = gr_sgB (rename \<rho> Y) (rename \<rho> p)"
  by (simp add: gr_sgB_def)

lemma gr_sgA_subst[grs]: "subst s (gr_sgA Y p) = gr_sgA (subst s Y) (subst s p)"
  by (simp add: gr_sgA_def)

lemma gr_sgB_subst[grs]: "subst s (gr_sgB Y p) = gr_sgB (subst s Y) (subst s p)"
  by (simp add: gr_sgB_def)

lemma gr_sg_rename[grs]: "rename \<rho> (gr_sg Y p) = gr_sg (rename \<rho> Y) (rename \<rho> p)"
  by (simp add: gr_sg_def grs)

lemma gr_sg_subst[grs]: "subst s (gr_sg Y p) = gr_sg (subst s Y) (subst s p)"
  by (simp add: gr_sg_def grs)

lemma gr_sg_shift[grs]: "shift (gr_sg Y p) = gr_sg (shift Y) (shift p)"
  using gr_sg_rename[of Suc Y p] by (simp add: shift_def)

lemma gr_sg_subst0[grs]: "subst0 M (gr_sg Y p) = gr_sg (subst0 M Y) (subst0 M p)"
  using gr_sg_subst[of "case_nat M Var" Y p] by (simp add: subst0_def)

lemma typed_gr_sgA[gr_ty]:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_sgA Y p : Prop"
  unfolding gr_sgA_def by gr_typ

lemma typed_gr_sgB[gr_ty]:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_sgB Y p : Prop"
  unfolding gr_sgB_def by gr_typ

lemma typed_gr_sg[gr_ty]:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_sg Y p : Prop"
  unfolding gr_sg_def by gr_typ

lemma gr_Sigma_rename[grs]: "rename \<rho> gr_Sigma = gr_Sigma"
  by (simp add: gr_Sigma_def grs)

lemma gr_Sigma_subst[grs]: "subst s gr_Sigma = gr_Sigma"
  by (simp add: gr_Sigma_def grs)

lemma gr_Sigma_shift[grs]: "shift gr_Sigma = gr_Sigma"
  by (simp add: shift_def grs)

lemma gr_Sigma_subst0[grs]: "subst0 M gr_Sigma = gr_Sigma"
  by (simp add: subst0_def grs)

lemma typed_gr_Sigma[gr_ty]: "\<Gamma> \<turnstile> gr_Sigma : gr_u \<rightarrow>\<^sub>o gr_u"
  unfolding gr_Sigma_def by gr_typ

lemma typed_gr_Sigma_app[gr_ty]:
  "\<Gamma> \<turnstile> W : gr_u \<Longrightarrow> \<Gamma> \<turnstile> App gr_Sigma W : gr_u"
  by (rule has_type.App[OF typed_gr_Sigma])

lemma gr_Sigma_consts: "consts_of gr_Sigma = {}"
  by (simp add: gr_Sigma_def gr_sg_def gr_sgA_def gr_sgB_def ObjBox_def ObjTrue_def)

theorem gr_Sigma_logical: "[] \<turnstile> gr_Sigma : gr_u \<rightarrow>\<^sub>o gr_u \<and> pp_logical_vocabulary gr_Sigma"
  by (simp add: typed_gr_Sigma gr_Sigma_consts pp_logical_vocabulary_def)

text \<open>Beta: \<open>\<Sigma> Y p\<close> unfolds to its body.\<close>

lemma gr_Sigma_app:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (App gr_Sigma Y) p \<longleftrightarrow>\<^sub>o gr_sg Y p)"
proof -
  have ty: "\<Gamma> \<turnstile> App (App gr_Sigma Y) p : Prop" by (gr_typ yt pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (App (Lam gr_u (Lam Prop (gr_sg (Var (Suc 0)) (Var 0)))) Y) p \<longleftrightarrow>\<^sub>o
        subst0 p (subst (lift_subst (case_nat Y Var)) (gr_sg (Var (Suc 0)) (Var 0))))"
    by (rule grk_beta2[OF ty[unfolded gr_Sigma_def]])
  then show ?thesis by (simp add: gr_Sigma_def grs)
qed

section \<open>Inclusion of operators\<close>

text \<open>\<open>gr_sub V W\<close> is \<open>\<forall>p(Vp \<rightarrow> Wp)\<close>.\<close>

definition gr_sub :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_sub V W = Forall Prop (Imp (App (shift V) (Var 0)) (App (shift W) (Var 0)))"

lemma gr_sub_rename[grs]: "rename \<rho> (gr_sub V W) = gr_sub (rename \<rho> V) (rename \<rho> W)"
  by (simp add: gr_sub_def grk_rename_lift_shift)

lemma gr_sub_subst[grs]: "subst s (gr_sub V W) = gr_sub (subst s V) (subst s W)"
  by (simp add: gr_sub_def subst_lift_shift)

lemma gr_sub_shift[grs]: "shift (gr_sub V W) = gr_sub (shift V) (shift W)"
  using gr_sub_rename[of Suc V W] by (simp add: shift_def)

lemma gr_sub_subst0[grs]: "subst0 M (gr_sub V W) = gr_sub (subst0 M V) (subst0 M W)"
  using gr_sub_subst[of "case_nat M Var" V W] by (simp add: subst0_def)

lemma typed_gr_sub[gr_ty]:
  "\<Gamma> \<turnstile> V : gr_u \<Longrightarrow> \<Gamma> \<turnstile> W : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_sub V W : Prop"
  unfolding gr_sub_def by gr_typ

lemma gr_sub_E:
  assumes vt: "\<Gamma> \<turnstile> V : gr_u" and wt: "\<Gamma> \<turnstile> W : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_sub V W) (Imp (App V p) (App W p))"
proof -
  have bt: "Prop # \<Gamma> \<turnstile> Imp (App (shift V) (Var 0)) (App (shift W) (Var 0)) : Prop"
    by (gr_typ vt wt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Forall Prop (Imp (App (shift V) (Var 0)) (App (shift W) (Var 0))))
        (subst0 p (Imp (App (shift V) (Var 0)) (App (shift W) (Var 0))))"
    by (rule grk_UI[OF bt pt])
  then show ?thesis by (simp add: gr_sub_def grs)
qed

lemma gr_sub_I:
  assumes d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App (shift V) (Var 0)) (App (shift W) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sub V W"
  unfolding gr_sub_def by (rule grk_gen[OF d])

lemma gr_sub_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (App (shift V) (Var 0)) (App (shift W) (Var 0)))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_sub V W)"
  unfolding gr_sub_def by (rule grk_gen_imp[OF ht d])

section \<open>\<open>Pre\<close> and the least fixed point \<open>L\<close>\<close>

text \<open>\<open>gr_Pre W\<close> is \<open>\<box>\<forall>p(\<Sigma>W(p) \<rightarrow> Wp)\<close>, with the literal term \<open>\<Sigma>W\<close>.\<close>

definition gr_Pre :: "oterm \<Rightarrow> oterm" where
  "gr_Pre W = \<box>\<^sub>o (gr_sub (App gr_Sigma W) W)"

lemma gr_Pre_rename[grs]: "rename \<rho> (gr_Pre W) = gr_Pre (rename \<rho> W)"
  by (simp add: gr_Pre_def grs)

lemma gr_Pre_subst[grs]: "subst s (gr_Pre W) = gr_Pre (subst s W)"
  by (simp add: gr_Pre_def grs)

lemma gr_Pre_shift[grs]: "shift (gr_Pre W) = gr_Pre (shift W)"
  using gr_Pre_rename[of Suc W] by (simp add: shift_def)

lemma gr_Pre_subst0[grs]: "subst0 M (gr_Pre W) = gr_Pre (subst0 M W)"
  using gr_Pre_subst[of "case_nat M Var" W] by (simp add: subst0_def)

lemma typed_gr_Pre[gr_ty]: "\<Gamma> \<turnstile> W : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_Pre W : Prop"
  unfolding gr_Pre_def by gr_typ

text \<open>\<open>gr_Lbody p\<close> is \<open>\<forall>W(Pre(W) \<rightarrow> Wp)\<close>; \<open>gr_L\<close> is \<open>\<lambda>p. \<forall>W(Pre(W) \<rightarrow> Wp)\<close>.\<close>

definition gr_Lbody :: "oterm \<Rightarrow> oterm" where
  "gr_Lbody p = Forall gr_u (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p)))"

definition gr_L :: oterm where
  "gr_L = Lam Prop (gr_Lbody (Var 0))"

lemma gr_Lbody_rename[grs]: "rename \<rho> (gr_Lbody p) = gr_Lbody (rename \<rho> p)"
  by (simp add: gr_Lbody_def grs grk_rename_lift_shift)

lemma gr_Lbody_subst[grs]: "subst s (gr_Lbody p) = gr_Lbody (subst s p)"
  by (simp add: gr_Lbody_def grs subst_lift_shift)

lemma gr_Lbody_shift[grs]: "shift (gr_Lbody p) = gr_Lbody (shift p)"
  using gr_Lbody_rename[of Suc p] by (simp add: shift_def)

lemma gr_Lbody_subst0[grs]: "subst0 M (gr_Lbody p) = gr_Lbody (subst0 M p)"
  using gr_Lbody_subst[of "case_nat M Var" p] by (simp add: subst0_def)

lemma typed_gr_Lbody[gr_ty]: "\<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_Lbody p : Prop"
  unfolding gr_Lbody_def by gr_typ

lemma gr_L_rename[grs]: "rename \<rho> gr_L = gr_L"
  by (simp add: gr_L_def grs)

lemma gr_L_subst[grs]: "subst s gr_L = gr_L"
  by (simp add: gr_L_def grs)

lemma gr_L_shift[grs]: "shift gr_L = gr_L"
  by (simp add: shift_def grs)

lemma gr_L_subst0[grs]: "subst0 M gr_L = gr_L"
  by (simp add: subst0_def grs)

lemma typed_gr_L[gr_ty]: "\<Gamma> \<turnstile> gr_L : gr_u"
  unfolding gr_L_def by gr_typ

lemma gr_L_consts: "consts_of gr_L = {}"
  by (simp add: gr_L_def gr_Lbody_def gr_Pre_def gr_sub_def gr_Sigma_consts
      ObjBox_def ObjTrue_def shift_def)

theorem gr_L_logical: "[] \<turnstile> gr_L : gr_u \<and> pp_logical_vocabulary gr_L"
  by (simp add: typed_gr_L gr_L_consts pp_logical_vocabulary_def)

lemma gr_L_app:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_L p \<longleftrightarrow>\<^sub>o gr_Lbody p)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_L p : Prop" by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam Prop (gr_Lbody (Var 0))) p \<longleftrightarrow>\<^sub>o subst0 p (gr_Lbody (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_L_def]])
  then show ?thesis by (simp add: gr_L_def grs)
qed

lemma gr_Lbody_E:
  assumes pt: "\<Gamma> \<turnstile> p : Prop" and wt: "\<Gamma> \<turnstile> W : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Lbody p) (Imp (gr_Pre W) (App W p))"
proof -
  have bt: "gr_u # \<Gamma> \<turnstile> Imp (gr_Pre (Var 0)) (App (Var 0) (shift p)) : Prop"
    by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Forall gr_u (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p))))
        (subst0 W (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p))))"
    by (rule grk_UI[OF bt wt])
  then show ?thesis by (simp add: gr_Lbody_def grs)
qed

lemma gr_Lbody_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p)))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_Lbody p)"
  unfolding gr_Lbody_def by (rule grk_gen_imp[OF ht d])

section \<open>\<open>g\<close> and the proposition \<open>q = r \<and> Lr\<close>\<close>

definition gr_q :: "oterm \<Rightarrow> oterm" where
  "gr_q r = Conj r (App gr_L r)"

definition gr_g :: oterm where
  "gr_g = Lam Prop (gr_q (Var 0))"

lemma gr_q_rename[grs]: "rename \<rho> (gr_q r) = gr_q (rename \<rho> r)"
  by (simp add: gr_q_def grs)

lemma gr_q_subst[grs]: "subst s (gr_q r) = gr_q (subst s r)"
  by (simp add: gr_q_def grs)

lemma gr_q_shift[grs]: "shift (gr_q r) = gr_q (shift r)"
  using gr_q_rename[of Suc r] by (simp add: shift_def)

lemma gr_q_subst0[grs]: "subst0 M (gr_q r) = gr_q (subst0 M r)"
  using gr_q_subst[of "case_nat M Var" r] by (simp add: subst0_def)

lemma typed_gr_q[gr_ty]: "\<Gamma> \<turnstile> r : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_q r : Prop"
  unfolding gr_q_def by gr_typ

text \<open>One-layer truth-functional unfoldings, for propositional steps.\<close>

lemma gr_q_eval[gr_eval]:
  "prop_eval v (gr_q r) = (prop_eval v r \<and> v (App gr_L r))"
  by (simp add: gr_q_def)

lemma gr_sgA_eval[gr_eval]:
  "prop_eval v (gr_sgA Y p) = (prop_eval v p \<or> v (App Y p) \<or> v (App Y (Neg p)))"
  by (simp add: gr_sgA_def)

lemma gr_sgB_eval[gr_eval]:
  "prop_eval v (gr_sgB Y p) = (\<not> prop_eval v p \<or> v (App Y p) \<or> v (App Y (Neg p)))"
  by (simp add: gr_sgB_def)

lemma gr_sg_eval[gr_eval]:
  "prop_eval v (gr_sg Y p) =
    (prop_eval v (\<box>\<^sub>o (gr_sgA Y p)) \<or> prop_eval v (\<box>\<^sub>o (gr_sgB Y p)))"
  by (simp add: gr_sg_def)

lemma gr_g_rename[grs]: "rename \<rho> gr_g = gr_g"
  by (simp add: gr_g_def grs)

lemma gr_g_subst[grs]: "subst s gr_g = gr_g"
  by (simp add: gr_g_def grs)

lemma gr_g_shift[grs]: "shift gr_g = gr_g"
  by (simp add: shift_def grs)

lemma gr_g_subst0[grs]: "subst0 M gr_g = gr_g"
  by (simp add: subst0_def grs)

lemma typed_gr_g[gr_ty]: "\<Gamma> \<turnstile> gr_g : gr_u"
  unfolding gr_g_def by gr_typ

lemma gr_g_consts: "consts_of gr_g = {}"
  by (simp add: gr_g_def gr_q_def gr_L_consts)

theorem gr_g_logical: "[] \<turnstile> gr_g : gr_u \<and> pp_logical_vocabulary gr_g"
  by (simp add: typed_gr_g gr_g_consts pp_logical_vocabulary_def)

lemma gr_g_app:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_g p \<longleftrightarrow>\<^sub>o gr_q p)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_g p : Prop" by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam Prop (gr_q (Var 0))) p \<longleftrightarrow>\<^sub>o subst0 p (gr_q (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_g_def]])
  then show ?thesis by (simp add: gr_g_def grs)
qed

end
