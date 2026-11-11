theory Goodman_PP_Refutation_Objects_Lemma5
  imports Goodman_PP_Refutation_Lemma4
begin

text \<open>
  TECHNICAL THEORY (not a numbered result of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  The formulas and property terms of Lemma 5:

    (14) \<open>\<forall>p(Y(\<not>p) \<leftrightarrow> Yp)\<close>                                   \<open>gr_SymF Y\<close>
    the property \<open>\<lambda>Y.\<forall>p(Y(\<not>p) \<leftrightarrow> Yp)\<close>                        \<open>gr_Sym\<close>
    \<open>\<forall>s(Bs \<rightarrow> B(\<not>s))\<close> (one half of the union case)            \<open>gr_NegCl B\<close>
    (15) "there is a stage \<open>Y\<^sub>0\<close> such that \<open>\<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p\<close>"   \<open>gr_PredEx c p\<close>
    \<open>\<Psi> = \<lambda>Y\<^sup>u.(Yp \<rightarrow> \<exists>Y\<^sub>0\<^sup>u(Stage(Y\<^sub>0) & \<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p))\<close>      \<open>gr_PredProp c p\<close>
\<close>

lemma gr_shift_Var: "shift (Var n) = Var (Suc n)"
  by (simp add: shift_def)

section \<open>Symmetry\<close>

definition gr_SymF :: "oterm \<Rightarrow> oterm" where
  "gr_SymF Y = Forall Prop (App (shift Y) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift Y) (Var 0))"

definition gr_Sym :: oterm where
  "gr_Sym = Lam gr_u (gr_SymF (Var 0))"

definition gr_NegCl :: "oterm \<Rightarrow> oterm" where
  "gr_NegCl B = Forall Prop (Imp (App (shift B) (Var 0)) (App (shift B) (Neg (Var 0))))"

lemma gr_SymF_rename[grs]: "rename \<rho> (gr_SymF Y) = gr_SymF (rename \<rho> Y)"
  by (simp add: gr_SymF_def grk_rename_lift_shift)

lemma gr_SymF_subst[grs]: "subst t (gr_SymF Y) = gr_SymF (subst t Y)"
  by (simp add: gr_SymF_def subst_lift_shift)

lemma gr_SymF_shift[grs]: "shift (gr_SymF Y) = gr_SymF (shift Y)"
  using gr_SymF_rename[of Suc Y] by (simp add: shift_def)

lemma gr_SymF_subst0[grs]: "subst0 M (gr_SymF Y) = gr_SymF (subst0 M Y)"
  using gr_SymF_subst[of "case_nat M Var" Y] by (simp add: subst0_def)

lemma typed_gr_SymF[gr_ty]: "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_SymF Y : Prop"
  unfolding gr_SymF_def by gr_typ

lemma gr_Sym_rename[grs]: "rename \<rho> gr_Sym = gr_Sym"
  by (simp add: gr_Sym_def grs)

lemma gr_Sym_subst[grs]: "subst t gr_Sym = gr_Sym"
  by (simp add: gr_Sym_def grs)

lemma gr_Sym_shift[grs]: "shift gr_Sym = gr_Sym"
  by (simp add: shift_def grs)

lemma gr_Sym_subst0[grs]: "subst0 M gr_Sym = gr_Sym"
  by (simp add: subst0_def grs)

lemma typed_gr_Sym[gr_ty]: "\<Gamma> \<turnstile> gr_Sym : gr_cls"
  unfolding gr_Sym_def by gr_typ

lemma gr_NegCl_rename[grs]: "rename \<rho> (gr_NegCl B) = gr_NegCl (rename \<rho> B)"
  by (simp add: gr_NegCl_def grk_rename_lift_shift)

lemma gr_NegCl_shift[grs]: "shift (gr_NegCl B) = gr_NegCl (shift B)"
  using gr_NegCl_rename[of Suc B] by (simp add: shift_def)

lemma typed_gr_NegCl[gr_ty]: "\<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_NegCl B : Prop"
  unfolding gr_NegCl_def by gr_typ

lemma gr_SymF_E:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_SymF Y) (App Y (Neg p) \<longleftrightarrow>\<^sub>o App Y p)"
proof -
  let ?body = "(App (shift Y) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift Y) (Var 0))"
  have bt: "Prop # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall Prop ?body) (subst0 p ?body)"
    by (rule grk_UI[OF bt pt])
  then show ?thesis by (simp add: gr_SymF_def grs)
qed

lemma gr_SymF_I:
  assumes d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (shift Y) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift Y) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_SymF Y"
  unfolding gr_SymF_def by (rule grk_gen[OF d])

lemma gr_SymF_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (App (shift Y) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift Y) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_SymF Y)"
  unfolding gr_SymF_def by (rule grk_gen_imp[OF ht d])

lemma gr_Sym_app:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Sym Y \<longleftrightarrow>\<^sub>o gr_SymF Y)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_Sym Y : Prop" by (gr_typ yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam gr_u (gr_SymF (Var 0))) Y \<longleftrightarrow>\<^sub>o subst0 Y (gr_SymF (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_Sym_def]])
  then show ?thesis by (simp add: gr_Sym_def grs)
qed

lemma gr_NegCl_E:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u" and st: "\<Gamma> \<turnstile> s : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_NegCl B) (Imp (App B s) (App B (Neg s)))"
proof -
  let ?body = "Imp (App (shift B) (Var 0)) (App (shift B) (Neg (Var 0)))"
  have bt': "Prop # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ bt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall Prop ?body) (subst0 s ?body)"
    by (rule grk_UI[OF bt' st])
  then show ?thesis by (simp add: gr_NegCl_def grs)
qed

section \<open>Predecessors\<close>

definition gr_PredEx :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_PredEx c p =
    Exists gr_u
      (Conj (gr_Stage (shift c) (Var 0))
        (Conj (Neg (App (Var 0) (shift p))) (App (App gr_Sigma (Var 0)) (shift p))))"

definition gr_PredProp :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_PredProp c p =
    Lam gr_u (Imp (App (Var 0) (shift p)) (gr_PredEx (shift c) (shift p)))"

lemma gr_PredEx_rename[grs]:
  "rename \<rho> (gr_PredEx c p) = gr_PredEx (rename \<rho> c) (rename \<rho> p)"
  by (simp add: gr_PredEx_def grs grk_rename_lift_shift)

lemma gr_PredEx_subst[grs]:
  "subst t (gr_PredEx c p) = gr_PredEx (subst t c) (subst t p)"
  by (simp add: gr_PredEx_def grs subst_lift_shift)

lemma gr_PredEx_shift[grs]: "shift (gr_PredEx c p) = gr_PredEx (shift c) (shift p)"
  using gr_PredEx_rename[of Suc c p] by (simp add: shift_def)

lemma gr_PredEx_subst0[grs]:
  "subst0 M (gr_PredEx c p) = gr_PredEx (subst0 M c) (subst0 M p)"
  using gr_PredEx_subst[of "case_nat M Var" c p] by (simp add: subst0_def)

lemma typed_gr_PredEx[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_PredEx c p : Prop"
  unfolding gr_PredEx_def by gr_typ

lemma gr_PredProp_rename[grs]:
  "rename \<rho> (gr_PredProp c p) = gr_PredProp (rename \<rho> c) (rename \<rho> p)"
  by (simp add: gr_PredProp_def grs grk_rename_lift_shift)

lemma gr_PredProp_subst[grs]:
  "subst t (gr_PredProp c p) = gr_PredProp (subst t c) (subst t p)"
  by (simp add: gr_PredProp_def grs subst_lift_shift)

lemma gr_PredProp_shift[grs]:
  "shift (gr_PredProp c p) = gr_PredProp (shift c) (shift p)"
  using gr_PredProp_rename[of Suc c p] by (simp add: shift_def)

lemma gr_PredProp_subst0[grs]:
  "subst0 M (gr_PredProp c p) = gr_PredProp (subst0 M c) (subst0 M p)"
  using gr_PredProp_subst[of "case_nat M Var" c p] by (simp add: subst0_def)

lemma typed_gr_PredProp[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_PredProp c p : gr_cls"
  unfolding gr_PredProp_def by gr_typ

text \<open>A stage \<open>Y\<^sub>0\<close> with \<open>\<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p\<close> witnesses the existential.\<close>

lemma gr_PredEx_I:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y0 : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (gr_Stage c Y0) (Conj (Neg (App Y0 p)) (App (App gr_Sigma Y0) p)))
      (gr_PredEx c p)"
proof -
  let ?body = "Conj (gr_Stage (shift c) (Var 0))
      (Conj (Neg (App (Var 0) (shift p))) (App (App gr_Sigma (Var 0)) (shift p)))"
  have bt: "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (subst0 Y0 ?body) (Exists gr_u ?body)"
    by (rule grk_EG[OF bt yt])
  then show ?thesis by (simp add: gr_PredEx_def grs)
qed

text \<open>Using the existential: "choose" such a \<open>Y\<^sub>0\<close> (the variable \<open>Var 0\<close>).\<close>

lemma gr_PredEx_E:
  assumes qt: "\<Gamma> \<turnstile> Q : Prop"
    and d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift c) (Var 0))
          (Conj (Neg (App (Var 0) (shift p))) (App (App gr_Sigma (Var 0)) (shift p))))
        (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_PredEx c p) Q"
  unfolding gr_PredEx_def by (rule grk_inst_imp[OF qt d])

lemma gr_PredProp_app:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and pt: "\<Gamma> \<turnstile> p : Prop" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App (gr_PredProp c p) Y \<longleftrightarrow>\<^sub>o Imp (App Y p) (gr_PredEx c p))"
proof -
  let ?body = "Imp (App (Var 0) (shift p)) (gr_PredEx (shift c) (shift p))"
  have ty: "\<Gamma> \<turnstile> App (gr_PredProp c p) Y : Prop" by (gr_typ ct pt yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam gr_u ?body) Y \<longleftrightarrow>\<^sub>o subst0 Y ?body)"
    by (rule grk_beta1[OF ty[unfolded gr_PredProp_def]])
  then show ?thesis by (simp add: gr_PredProp_def grs)
qed

end
