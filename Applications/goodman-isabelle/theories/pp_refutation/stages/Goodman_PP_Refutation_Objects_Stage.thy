theory Goodman_PP_Refutation_Objects_Stage
  imports "Goodman_Integration_PP_Refutation_Logic.Goodman_PP_Refutation_Lemma3"
begin

text \<open>
  TECHNICAL THEORY (not a numbered result of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  The theory \<open>\<T>\<close> and the objects of the note's section "The pure stages":

    \<open>T\<^sub>0\<close>   = Classicism + Purity schema + Application closure   \<open>gr_T0\<close>
    \<open>\<T>\<close>    = \<open>T\<^sub>0\<close> + (PP_u) \<open>Pure\<^sub>u\<^sub>\<rightarrow>\<^sub>t(Pure\<^sub>u)\<close>                        \<open>gr_Th\<close>
    \<open>K\<^sub>\<bottom> = \<lambda>p.\<bottom>\<close>                                              \<open>gr_Kbot\<close>
    \<open>Cl(\<Z>)\<close>, the conjunction of the three closure conditions   \<open>gr_Cl gr_Pure Z\<close>
    (12) \<open>Stage(Y) = Pure(Y) & \<forall>\<Z>(Cl(\<Z>) \<rightarrow> \<Z>(Y))\<close>               \<open>gr_Stage gr_Pure Y\<close>
    (13) \<open>P = \<lambda>p.\<exists>Y(Stage(Y) & Yp)\<close>                             \<open>gr_P\<close>
    \<open>M = \<lambda>c.\<lambda>p.\<exists>Y(cY & \<forall>\<Z>(Cl\<^sub>c(\<Z>) \<rightarrow> \<Z>(Y)) & Yp)\<close> (Lemma 6)     \<open>gr_M\<close>

  As in the proof of Lemma 6, the closure formula is parametrized by a term
  \<open>c : u \<rightarrow> t\<close> standing for \<open>Pure\<^sub>u\<close> (\<open>Cl\<^sub>c\<close> is \<open>gr_Cl c\<close>); the note's \<open>Cl\<close>,
  \<open>Stage\<close> are the instances at \<open>gr_Pure = Pure\<^sub>u\<close>.  \<open>gr_cls\<close> is the type
  \<open>u \<rightarrow> t\<close> of properties of operators.
\<close>

section \<open>The theory \<open>\<T>\<close>\<close>

text \<open>
  CORRESPONDENCE, stated once.  "The background theory \<open>T\<^sub>0\<close> includes
  Classicism, the Purity schema and Application closure.  ...  Let \<open>\<T>\<close> be
  the axiom extension of \<open>T\<^sub>0\<close> by (PP_u)."  Classicism is the base calculus of
  \<open>\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A\<close>; the stock \<open>T\<close> carries the added axioms.  A theorem of
  \<open>T\<^sub>0\<close> (of \<open>\<T>\<close>) is a statement proved below under the hypothesis
  \<open>gr_T0 \<subseteq> T\<close> (\<open>gr_Th \<subseteq> T\<close>).  A "logical theorem" has no such hypothesis.
\<close>

definition gr_T0 :: "oterm set" where
  "gr_T0 = pp_purity_schema \<union> pp_application_closure_schema"

definition gr_Th :: "oterm set" where
  "gr_Th = gr_T0 \<union> {pp_target_PP}"

abbreviation gr_Pure :: oterm where
  "gr_Pure \<equiv> pp_Pure gr_u"

lemma gr_T0_sub_Th: "gr_T0 \<subseteq> gr_Th"
  by (auto simp: gr_Th_def)

lemma gr_Th_T0: "gr_Th \<subseteq> T \<Longrightarrow> gr_T0 \<subseteq> T"
  by (auto simp: gr_Th_def)

text \<open>The Purity schema: every closed logical term is pure.\<close>

lemma gr_T0_purity:
  assumes st: "gr_T0 \<subseteq> T" and m0: "[] \<turnstile> M : \<sigma>" and cf: "consts_of M = {}"
    and mt: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> M"
proof -
  have "pp_pure \<sigma> M \<in> pp_purity_schema"
    unfolding pp_purity_schema_def pp_logical_vocabulary_def using m0 cf by blast
  then have m: "pp_pure \<sigma> M \<in> T" using st unfolding gr_T0_def by blast
  show ?thesis by (rule CEV_axiom_proves.Axiom[OF m typed_pp_pure[OF mt]])
qed

text \<open>Application closure: \<open>Pure(F) & Pure(a) \<rightarrow> Pure(Fa)\<close>.\<close>

lemma gr_T0_application:
  assumes st: "gr_T0 \<subseteq> T" and ft: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and xt: "\<Gamma> \<turnstile> X : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> X)) (pp_pure \<tau> (App F X))"
proof -
  have "pp_application_closure \<sigma> \<tau> \<in> T"
    using st unfolding gr_T0_def pp_application_closure_schema_def by blast
  then show ?thesis using ft xt by (rule pp_axiom_application_closed_imp)
qed

text \<open>(PP_u): \<open>Pure\<^sub>u\<^sub>\<rightarrow>\<^sub>t(Pure\<^sub>u)\<close>.\<close>

lemma gr_Th_PP:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_cls gr_Pure"
proof -
  have "pp_target_PP \<in> T" using st unfolding gr_Th_def by blast
  then have "pp_pure gr_cls gr_Pure \<in> T"
    by (simp add: pp_target_PP_def pp_purity_of_pure_def)
  then show ?thesis
    by (rule CEV_axiom_proves.Axiom) (rule typed_pp_pure[OF typed_pp_Pure])
qed

lemma gr_Pure_rename[grs]: "rename \<rho> (pp_Pure \<sigma>) = pp_Pure \<sigma>"
  by (simp add: pp_Pure_def)

lemma gr_Pure_subst[grs]: "subst s (pp_Pure \<sigma>) = pp_Pure \<sigma>"
  by (simp add: pp_Pure_def)

lemma gr_Pure_shift[grs]: "shift (pp_Pure \<sigma>) = pp_Pure \<sigma>"
  by (simp add: shift_def pp_Pure_def)

lemma gr_Pure_subst0[grs]: "subst0 M (pp_Pure \<sigma>) = pp_Pure \<sigma>"
  by (simp add: subst0_def pp_Pure_def)

section \<open>\<open>K\<^sub>\<bottom> = \<lambda>p.\<bottom>\<close>\<close>

definition gr_Kbot :: oterm where
  "gr_Kbot = Lam Prop ObjFalse"

lemma gr_Kbot_rename[grs]: "rename \<rho> gr_Kbot = gr_Kbot"
  by (simp add: gr_Kbot_def grs)

lemma gr_Kbot_subst[grs]: "subst s gr_Kbot = gr_Kbot"
  by (simp add: gr_Kbot_def grs)

lemma gr_Kbot_shift[grs]: "shift gr_Kbot = gr_Kbot"
  by (simp add: shift_def grs)

lemma gr_Kbot_subst0[grs]: "subst0 M gr_Kbot = gr_Kbot"
  by (simp add: subst0_def grs)

lemma typed_gr_Kbot[gr_ty]: "\<Gamma> \<turnstile> gr_Kbot : gr_u"
  unfolding gr_Kbot_def by gr_typ

lemma gr_Kbot_consts: "consts_of gr_Kbot = {}"
  by (simp add: gr_Kbot_def ObjFalse_def ObjTrue_def)

text \<open>\<open>K\<^sub>\<bottom>p = \<bottom>\<close>, by beta.\<close>

lemma gr_Kbot_app:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Kbot p \<longleftrightarrow>\<^sub>o ObjFalse)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_Kbot p : Prop" by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam Prop ObjFalse) p \<longleftrightarrow>\<^sub>o subst0 p ObjFalse)"
    by (rule grk_beta1[OF ty[unfolded gr_Kbot_def]])
  then show ?thesis by (simp add: gr_Kbot_def grs)
qed

lemma gr_Kbot_app_eq:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_Kbot p) ObjFalse"
  by (rule grk_iff_eq[OF gr_Kbot_app[OF pt]])

lemma gr_Kbot_empty:
  assumes pt: "\<Gamma> \<turnstile> p : Prop" and ct: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Kbot p) C"
proof -
  have ty: "\<Gamma> \<turnstile> Imp (App gr_Kbot p) C : Prop" by (gr_typ pt ct)
  show ?thesis
    by (rule grk_PC2[OF gr_Kbot_app[OF pt] CEV_axiom_proves_ObjTrue ty]) gr_taut
qed

section \<open>Witnesses and covers\<close>

text \<open>
  \<open>gr_wit c Z B s Y\<close> is the matrix \<open>Pure(Y) & \<Z>(Y) & Y \<subseteq> B & Ys\<close> of the
  union condition; \<open>gr_cov B W\<close> is \<open>\<forall>s(Bs \<rightarrow> \<exists>Y. W)\<close> for a matrix \<open>W\<close> given
  in the context extended by \<open>s\<close> (index 1) and \<open>Y\<close> (index 0).
\<close>

definition gr_wit :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_wit c Z B s Y = Conj (App c Y) (Conj (App Z Y) (Conj (gr_sub Y B) (App Y s)))"

definition gr_cov :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_cov B W = Forall Prop (Imp (App (shift B) (Var 0)) (Exists gr_u W))"

text \<open>\<open>\<forall>s(Bs \<rightarrow> \<exists>Y(Pure(Y) & \<Z>(Y) & Y \<subseteq> B & Ys))\<close>.\<close>

definition gr_ClCov :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_ClCov c Z B =
    gr_cov B (gr_wit (shift (shift c)) (shift (shift Z)) (shift (shift B)) (Var (Suc 0)) (Var 0))"

lemma gr_wit_rename[grs]:
  "rename \<rho> (gr_wit c Z B s Y) =
    gr_wit (rename \<rho> c) (rename \<rho> Z) (rename \<rho> B) (rename \<rho> s) (rename \<rho> Y)"
  by (simp add: gr_wit_def grs)

lemma gr_wit_subst[grs]:
  "subst t (gr_wit c Z B s Y) =
    gr_wit (subst t c) (subst t Z) (subst t B) (subst t s) (subst t Y)"
  by (simp add: gr_wit_def grs)

lemma gr_wit_shift[grs]:
  "shift (gr_wit c Z B s Y) = gr_wit (shift c) (shift Z) (shift B) (shift s) (shift Y)"
  using gr_wit_rename[of Suc c Z B s Y] by (simp add: shift_def)

lemma gr_wit_subst0[grs]:
  "subst0 M (gr_wit c Z B s Y) =
    gr_wit (subst0 M c) (subst0 M Z) (subst0 M B) (subst0 M s) (subst0 M Y)"
  using gr_wit_subst[of "case_nat M Var" c Z B s Y] by (simp add: subst0_def)

lemma typed_gr_wit[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> s : Prop \<Longrightarrow>
    \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_wit c Z B s Y : Prop"
  unfolding gr_wit_def by gr_typ

lemma gr_wit_eval[gr_eval]:
  "prop_eval v (gr_wit c Z B s Y) =
    (v (App c Y) \<and> v (App Z Y) \<and> prop_eval v (gr_sub Y B) \<and> v (App Y s))"
  by (simp add: gr_wit_def)

lemma gr_cov_rename:
  "rename \<rho> (gr_cov B W) = gr_cov (rename \<rho> B) (rename (lift_ren (lift_ren \<rho>)) W)"
  by (simp add: gr_cov_def grk_rename_lift_shift)

lemma gr_cov_subst:
  "subst t (gr_cov B W) = gr_cov (subst t B) (subst (lift_subst (lift_subst t)) W)"
  by (simp add: gr_cov_def subst_lift_shift)

lemma typed_gr_cov[gr_ty]:
  "\<Gamma> \<turnstile> B : gr_u \<Longrightarrow> gr_u # Prop # \<Gamma> \<turnstile> W : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_cov B W : Prop"
  unfolding gr_cov_def by gr_typ

lemma gr_ClCov_rename[grs]:
  "rename \<rho> (gr_ClCov c Z B) = gr_ClCov (rename \<rho> c) (rename \<rho> Z) (rename \<rho> B)"
  by (simp add: gr_ClCov_def gr_cov_rename grs grk_rename_lift_shift)

lemma gr_ClCov_subst[grs]:
  "subst t (gr_ClCov c Z B) = gr_ClCov (subst t c) (subst t Z) (subst t B)"
  by (simp add: gr_ClCov_def gr_cov_subst grs subst_lift_shift)

lemma gr_ClCov_shift[grs]:
  "shift (gr_ClCov c Z B) = gr_ClCov (shift c) (shift Z) (shift B)"
  using gr_ClCov_rename[of Suc c Z B] by (simp add: shift_def)

lemma gr_ClCov_subst0[grs]:
  "subst0 M (gr_ClCov c Z B) = gr_ClCov (subst0 M c) (subst0 M Z) (subst0 M B)"
  using gr_ClCov_subst[of "case_nat M Var" c Z B] by (simp add: subst0_def)

lemma typed_gr_ClCov[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> B : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_ClCov c Z B : Prop"
  unfolding gr_ClCov_def by gr_typ

text \<open>Introduction of a cover.\<close>

lemma gr_cov_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (App (shift B) (Var 0)) (Exists gr_u W))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_cov B W)"
  unfolding gr_cov_def by (rule grk_gen_imp[OF ht d])

lemma gr_cov_I:
  assumes d: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App (shift B) (Var 0)) (Exists gr_u W)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_cov B W"
  unfolding gr_cov_def by (rule grk_gen[OF d])

text \<open>Covers are monotone in the witness matrix.\<close>

lemma gr_cov_mono_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop" and bt: "\<Gamma> \<turnstile> B : gr_u"
    and d: "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (shift H)) (Imp W1 W2)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (Imp (gr_cov B W1) (gr_cov B W2))"
proof -
  let ?Bs = "App (shift B) (Var 0)"
  have wt: "gr_u # Prop # \<Gamma> \<turnstile> Imp W1 W2 : Prop" by (rule grk_imp_ty2[OF d])
  have w1: "gr_u # Prop # \<Gamma> \<turnstile> W1 : Prop" by (rule grk_ImpD1[OF wt])
  have w2: "gr_u # Prop # \<Gamma> \<turnstile> W2 : Prop" by (rule grk_ImpD2[OF wt])
  have ht1: "Prop # \<Gamma> \<turnstile> shift H : Prop" by (gr_typ ht)
  have ex: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (Exists gr_u W1) (Exists gr_u W2))"
    by (rule grk_exists_mono_imp[OF ht1 d])
  have ty: "Prop # \<Gamma> \<turnstile> Imp (shift H)
      (Imp (Imp ?Bs (Exists gr_u W1)) (Imp ?Bs (Exists gr_u W2))) : Prop"
    by (gr_typ ht bt w1 w2)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (Imp ?Bs (Exists gr_u W1)) (Imp ?Bs (Exists gr_u W2)))"
    by (rule grk_PC1[OF ex ty]) gr_taut
  then show ?thesis unfolding gr_cov_def by (rule grk_forall_mono_imp[OF ht])
qed

lemma gr_cov_mono:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u"
    and d: "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp W1 W2"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_cov B W1) (gr_cov B W2)"
proof -
  have "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (shift ObjTrue)) (Imp W1 W2)"
    using CEV_axiom_imp_of_right[OF typed_ObjTrue d] by simp
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Imp (gr_cov B W1) (gr_cov B W2))"
    by (rule gr_cov_mono_imp[OF typed_ObjTrue bt])
  then show ?thesis by (rule grk_MP[OF CEV_axiom_proves_ObjTrue])
qed

text \<open>From a cover, a universal statement about the members of \<open>B\<close>.\<close>

lemma gr_cov_E_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop" and bt: "\<Gamma> \<turnstile> B : gr_u" and ct: "Prop # \<Gamma> \<turnstile> C : Prop"
    and d: "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (shift H)) (Imp W (shift C))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp H (Imp (gr_cov B W) (Forall Prop (Imp (App (shift B) (Var 0)) C)))"
proof -
  let ?Bs = "App (shift B) (Var 0)"
  have wt: "gr_u # Prop # \<Gamma> \<turnstile> W : Prop" by (rule grk_ImpD1[OF grk_imp_ty2[OF d]])
  have ht1: "Prop # \<Gamma> \<turnstile> shift H : Prop" by (gr_typ ht)
  have ex: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift H) (Imp (Exists gr_u W) C)"
    by (rule grk_exists_E_imp[OF ht1 ct d])
  have ty: "Prop # \<Gamma> \<turnstile> Imp (shift H) (Imp (Imp ?Bs (Exists gr_u W)) (Imp ?Bs C)) : Prop"
    by (gr_typ ht bt wt ct)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (Imp ?Bs (Exists gr_u W)) (Imp ?Bs C))"
    by (rule grk_PC1[OF ex ty]) gr_taut
  then show ?thesis unfolding gr_cov_def by (rule grk_forall_mono_imp[OF ht])
qed

lemma gr_cov_E:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u" and ct: "Prop # \<Gamma> \<turnstile> C : Prop"
    and d: "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp W (shift C)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_cov B W) (Forall Prop (Imp (App (shift B) (Var 0)) C))"
proof -
  have "gr_u # Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (shift ObjTrue)) (Imp W (shift C))"
    using CEV_axiom_imp_of_right[OF typed_ObjTrue d] by simp
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Imp (gr_cov B W) (Forall Prop (Imp (App (shift B) (Var 0)) C)))"
    by (rule gr_cov_E_imp[OF typed_ObjTrue bt ct])
  then show ?thesis by (rule grk_MP[OF CEV_axiom_proves_ObjTrue])
qed

text \<open>Instantiation of a cover at a proposition \<open>s\<close>.\<close>

lemma gr_cov_inst:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u" and wt: "gr_u # Prop # \<Gamma> \<turnstile> W : Prop" and st: "\<Gamma> \<turnstile> s : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_cov B W)
      (Imp (App B s) (Exists gr_u (subst (lift_subst (case_nat s Var)) W)))"
proof -
  let ?body = "Imp (App (shift B) (Var 0)) (Exists gr_u W)"
  have bt': "Prop # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ bt wt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall Prop ?body) (subst0 s ?body)"
    by (rule grk_UI[OF bt' st])
  then show ?thesis by (simp add: gr_cov_def grs grk_subst0_Exists)
qed

section \<open>The closure conditions and \<open>Cl\<close>\<close>

text \<open>
  "A property \<open>\<Z>\<close> of operators is called closed when it satisfies the
  following conditions.
    1. \<open>\<Z>(K\<^sub>\<bottom>)\<close>.
    2. For every pure \<open>Y\<close>, if \<open>\<Z>(Y)\<close>, then \<open>\<Z>(\<Sigma>Y)\<close>.
    3. For every pure \<open>B\<close>, if each proposition \<open>s\<close> with \<open>Bs\<close> has a pure
       operator \<open>Y\<close> satisfying \<open>\<Z>(Y)\<close>, \<open>Y \<subseteq> B\<close>, and \<open>Ys\<close>, then \<open>\<Z>(B)\<close>.
   ... Its formal expression is
     \<open>\<forall>B((Pure(B) & \<forall>s(Bs \<rightarrow> \<exists>Y(Pure(Y) & \<Z>(Y) & Y \<subseteq> B & Ys))) \<rightarrow> \<Z>(B))\<close>.
   Let \<open>Cl(\<Z>)\<close> be the conjunction of the three conditions."
\<close>

definition gr_Cl1 :: "oterm \<Rightarrow> oterm" where
  "gr_Cl1 Z = App Z gr_Kbot"

definition gr_Cl2 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Cl2 c Z =
    Forall gr_u
      (Imp (App (shift c) (Var 0))
        (Imp (App (shift Z) (Var 0)) (App (shift Z) (App gr_Sigma (Var 0)))))"

definition gr_Cl3 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Cl3 c Z =
    Forall gr_u
      (Imp (Conj (App (shift c) (Var 0)) (gr_ClCov (shift c) (shift Z) (Var 0)))
        (App (shift Z) (Var 0)))"

definition gr_Cl :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Cl c Z = Conj (gr_Cl1 Z) (Conj (gr_Cl2 c Z) (gr_Cl3 c Z))"

lemma gr_Cl2_rename[grs]: "rename \<rho> (gr_Cl2 c Z) = gr_Cl2 (rename \<rho> c) (rename \<rho> Z)"
  by (simp add: gr_Cl2_def grs grk_rename_lift_shift)

lemma gr_Cl2_subst[grs]: "subst t (gr_Cl2 c Z) = gr_Cl2 (subst t c) (subst t Z)"
  by (simp add: gr_Cl2_def grs subst_lift_shift)

lemma gr_Cl3_rename[grs]: "rename \<rho> (gr_Cl3 c Z) = gr_Cl3 (rename \<rho> c) (rename \<rho> Z)"
  by (simp add: gr_Cl3_def grs grk_rename_lift_shift)

lemma gr_Cl3_subst[grs]: "subst t (gr_Cl3 c Z) = gr_Cl3 (subst t c) (subst t Z)"
  by (simp add: gr_Cl3_def grs subst_lift_shift)

lemma gr_Cl_rename[grs]: "rename \<rho> (gr_Cl c Z) = gr_Cl (rename \<rho> c) (rename \<rho> Z)"
  by (simp add: gr_Cl_def gr_Cl1_def grs)

lemma gr_Cl_subst[grs]: "subst t (gr_Cl c Z) = gr_Cl (subst t c) (subst t Z)"
  by (simp add: gr_Cl_def gr_Cl1_def grs)

lemma gr_Cl_shift[grs]: "shift (gr_Cl c Z) = gr_Cl (shift c) (shift Z)"
  using gr_Cl_rename[of Suc c Z] by (simp add: shift_def)

lemma gr_Cl_subst0[grs]: "subst0 M (gr_Cl c Z) = gr_Cl (subst0 M c) (subst0 M Z)"
  using gr_Cl_subst[of "case_nat M Var" c Z] by (simp add: subst0_def)

lemma typed_gr_Cl1[gr_ty]: "\<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Cl1 Z : Prop"
  unfolding gr_Cl1_def by gr_typ

lemma typed_gr_Cl2[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Cl2 c Z : Prop"
  unfolding gr_Cl2_def by gr_typ

lemma typed_gr_Cl3[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Cl3 c Z : Prop"
  unfolding gr_Cl3_def by gr_typ

lemma typed_gr_Cl[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_Cl c Z : Prop"
  unfolding gr_Cl_def by gr_typ

lemma gr_Cl1_eval[gr_eval]: "prop_eval v (gr_Cl1 Z) = v (App Z gr_Kbot)"
  by (simp add: gr_Cl1_def)

lemma gr_Cl_eval[gr_eval]:
  "prop_eval v (gr_Cl c Z) =
    (prop_eval v (gr_Cl1 Z) \<and> prop_eval v (gr_Cl2 c Z) \<and> prop_eval v (gr_Cl3 c Z))"
  by (simp add: gr_Cl_def)

text \<open>The three conditions, extracted from \<open>Cl\<close>.\<close>

lemma gr_Cl_1:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and zt: "\<Gamma> \<turnstile> Z : gr_cls"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Cl c Z) (App Z gr_Kbot)"
  by (rule grk_taut) (gr_typ ct zt, gr_taut)

lemma gr_Cl_2:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and zt: "\<Gamma> \<turnstile> Z : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Cl c Z) (Imp (App c Y) (Imp (App Z Y) (App Z (App gr_Sigma Y))))"
proof -
  let ?body = "Imp (App (shift c) (Var 0))
      (Imp (App (shift Z) (Var 0)) (App (shift Z) (App gr_Sigma (Var 0))))"
  have bt: "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct zt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u ?body) (subst0 Y ?body)"
    by (rule grk_UI[OF bt yt])
  then have ui: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Cl2 c Z) (Imp (App c Y) (Imp (App Z Y) (App Z (App gr_Sigma Y))))"
    by (simp add: gr_Cl2_def grs)
  have ty: "\<Gamma> \<turnstile> Imp (gr_Cl c Z)
      (Imp (App c Y) (Imp (App Z Y) (App Z (App gr_Sigma Y)))) : Prop"
    by (gr_typ ct zt yt)
  show ?thesis by (rule grk_PC1[OF ui ty]) gr_taut
qed

lemma gr_Cl_3:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and zt: "\<Gamma> \<turnstile> Z : gr_cls" and bt: "\<Gamma> \<turnstile> B : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Cl c Z) (Imp (Conj (App c B) (gr_ClCov c Z B)) (App Z B))"
proof -
  let ?body = "Imp (Conj (App (shift c) (Var 0)) (gr_ClCov (shift c) (shift Z) (Var 0)))
      (App (shift Z) (Var 0))"
  have bt': "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct zt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_u ?body) (subst0 B ?body)"
    by (rule grk_UI[OF bt' bt])
  then have ui: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Cl3 c Z) (Imp (Conj (App c B) (gr_ClCov c Z B)) (App Z B))"
    by (simp add: gr_Cl3_def grs)
  have ty: "\<Gamma> \<turnstile> Imp (gr_Cl c Z) (Imp (Conj (App c B) (gr_ClCov c Z B)) (App Z B)) : Prop"
    by (gr_typ ct zt bt)
  show ?thesis by (rule grk_PC1[OF ui ty]) gr_taut
qed

text \<open>Establishing \<open>Cl(\<Z>)\<close> from its three conditions.\<close>

lemma gr_Cl_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop" and ct: "\<Gamma> \<turnstile> c : gr_cls" and zt: "\<Gamma> \<turnstile> Z : gr_cls"
    and c1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (App Z gr_Kbot)"
    and c2: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H)
        (Imp (App (shift c) (Var 0))
          (Imp (App (shift Z) (Var 0)) (App (shift Z) (App gr_Sigma (Var 0)))))"
    and c3: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H)
        (Imp (Conj (App (shift c) (Var 0)) (gr_ClCov (shift c) (shift Z) (Var 0)))
          (App (shift Z) (Var 0)))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_Cl c Z)"
proof -
  have g2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_Cl2 c Z)"
    unfolding gr_Cl2_def by (rule grk_gen_imp[OF ht c2])
  have g3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_Cl3 c Z)"
    unfolding gr_Cl3_def by (rule grk_gen_imp[OF ht c3])
  have ty: "\<Gamma> \<turnstile> Imp H (gr_Cl c Z) : Prop" by (gr_typ ht ct zt)
  show ?thesis by (rule grk_PC3[OF c1 g2 g3 ty]) gr_taut
qed

lemma gr_Cl_I:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and zt: "\<Gamma> \<turnstile> Z : gr_cls"
    and c1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App Z gr_Kbot"
    and c2: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (shift c) (Var 0))
        (Imp (App (shift Z) (Var 0)) (App (shift Z) (App gr_Sigma (Var 0))))"
    and c3: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App (shift c) (Var 0)) (gr_ClCov (shift c) (shift Z) (Var 0)))
        (App (shift Z) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Cl c Z"
proof -
  have g2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Cl2 c Z"
    unfolding gr_Cl2_def by (rule grk_gen[OF c2])
  have g3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Cl3 c Z"
    unfolding gr_Cl3_def by (rule grk_gen[OF c3])
  have ty: "\<Gamma> \<turnstile> gr_Cl c Z : Prop" by (gr_typ ct zt)
  show ?thesis by (rule grk_PC3[OF c1 g2 g3 ty]) gr_taut
qed

section \<open>(12) \<open>Stage\<close>\<close>

text \<open>\<open>Stage(Y) = Pure(Y) & \<forall>\<Z>(Cl(\<Z>) \<rightarrow> \<Z>(Y))\<close>; \<open>gr_StageAll\<close> is the second conjunct.\<close>

definition gr_StageAll :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_StageAll c Y =
    Forall gr_cls (Imp (gr_Cl (shift c) (Var 0)) (App (Var 0) (shift Y)))"

definition gr_Stage :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Stage c Y = Conj (App c Y) (gr_StageAll c Y)"

lemma gr_StageAll_rename[grs]:
  "rename \<rho> (gr_StageAll c Y) = gr_StageAll (rename \<rho> c) (rename \<rho> Y)"
  by (simp add: gr_StageAll_def grs grk_rename_lift_shift)

lemma gr_StageAll_subst[grs]:
  "subst t (gr_StageAll c Y) = gr_StageAll (subst t c) (subst t Y)"
  by (simp add: gr_StageAll_def grs subst_lift_shift)

lemma gr_Stage_rename[grs]:
  "rename \<rho> (gr_Stage c Y) = gr_Stage (rename \<rho> c) (rename \<rho> Y)"
  by (simp add: gr_Stage_def grs)

lemma gr_Stage_subst[grs]:
  "subst t (gr_Stage c Y) = gr_Stage (subst t c) (subst t Y)"
  by (simp add: gr_Stage_def grs)

lemma gr_Stage_shift[grs]: "shift (gr_Stage c Y) = gr_Stage (shift c) (shift Y)"
  using gr_Stage_rename[of Suc c Y] by (simp add: shift_def)

lemma gr_Stage_subst0[grs]:
  "subst0 M (gr_Stage c Y) = gr_Stage (subst0 M c) (subst0 M Y)"
  using gr_Stage_subst[of "case_nat M Var" c Y] by (simp add: subst0_def)

lemma typed_gr_StageAll[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_StageAll c Y : Prop"
  unfolding gr_StageAll_def by gr_typ

lemma typed_gr_Stage[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> gr_Stage c Y : Prop"
  unfolding gr_Stage_def by gr_typ

lemma gr_Stage_eval[gr_eval]:
  "prop_eval v (gr_Stage c Y) = (v (App c Y) \<and> prop_eval v (gr_StageAll c Y))"
  by (simp add: gr_Stage_def)

text \<open>"The first conjunct in (12) makes every stage pure."\<close>

lemma gr_Stage_pure:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage c Y) (App c Y)"
  by (rule grk_taut) (gr_typ ct yt, gr_taut)

text \<open>Instantiating (12) at a property term \<open>Z\<close>.\<close>

lemma gr_Stage_E:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u" and zt: "\<Gamma> \<turnstile> Z : gr_cls"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage c Y) (Imp (gr_Cl c Z) (App Z Y))"
proof -
  let ?body = "Imp (gr_Cl (shift c) (Var 0)) (App (Var 0) (shift Y))"
  have bt: "gr_cls # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall gr_cls ?body) (subst0 Z ?body)"
    by (rule grk_UI[OF bt zt])
  then have ui: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_StageAll c Y) (Imp (gr_Cl c Z) (App Z Y))"
    by (simp add: gr_StageAll_def grs)
  have ty: "\<Gamma> \<turnstile> Imp (gr_Stage c Y) (Imp (gr_Cl c Z) (App Z Y)) : Prop"
    by (gr_typ ct yt zt)
  show ?thesis by (rule grk_PC1[OF ui ty]) gr_taut
qed

text \<open>Proving that something is a stage ("generalizing \<open>\<Z>\<close>").\<close>

lemma gr_Stage_I_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop" and ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
    and pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (App c Y)"
    and all: "gr_cls # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift H) (Imp (gr_Cl (shift c) (Var 0)) (App (Var 0) (shift Y)))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_Stage c Y)"
proof -
  have g: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (gr_StageAll c Y)"
    unfolding gr_StageAll_def by (rule grk_gen_imp[OF ht all])
  have ty: "\<Gamma> \<turnstile> Imp H (gr_Stage c Y) : Prop" by (gr_typ ht ct yt)
  show ?thesis by (rule grk_PC2[OF pure g ty]) gr_taut
qed

text \<open>\<open>Stage\<close> as a term of type \<open>u \<rightarrow> t\<close> ("The property Stage").\<close>

definition gr_StageP :: "oterm \<Rightarrow> oterm" where
  "gr_StageP c = Lam gr_u (gr_Stage (shift c) (Var 0))"

lemma gr_StageP_rename[grs]: "rename \<rho> (gr_StageP c) = gr_StageP (rename \<rho> c)"
  by (simp add: gr_StageP_def grs grk_rename_lift_shift)

lemma gr_StageP_subst[grs]: "subst t (gr_StageP c) = gr_StageP (subst t c)"
  by (simp add: gr_StageP_def grs subst_lift_shift)

lemma gr_StageP_shift[grs]: "shift (gr_StageP c) = gr_StageP (shift c)"
  using gr_StageP_rename[of Suc c] by (simp add: shift_def)

lemma gr_StageP_subst0[grs]: "subst0 M (gr_StageP c) = gr_StageP (subst0 M c)"
  using gr_StageP_subst[of "case_nat M Var" c] by (simp add: subst0_def)

lemma typed_gr_StageP[gr_ty]: "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> gr_StageP c : gr_cls"
  unfolding gr_StageP_def by gr_typ

lemma gr_StageP_app:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_StageP c) Y \<longleftrightarrow>\<^sub>o gr_Stage c Y)"
proof -
  have ty: "\<Gamma> \<turnstile> App (gr_StageP c) Y : Prop" by (gr_typ ct yt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam gr_u (gr_Stage (shift c) (Var 0))) Y \<longleftrightarrow>\<^sub>o
        subst0 Y (gr_Stage (shift c) (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_StageP_def]])
  then show ?thesis by (simp add: gr_StageP_def grs)
qed

section \<open>(13) \<open>P\<close>, and the builder \<open>M\<close> of Lemma 6\<close>

text \<open>\<open>gr_Pbody c p\<close> is \<open>\<exists>Y(Stage\<^sub>c(Y) & Yp)\<close>.\<close>

definition gr_Pbody :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "gr_Pbody c p =
    Exists gr_u (Conj (gr_Stage (shift c) (Var 0)) (App (Var 0) (shift p)))"

text \<open>(13): \<open>P = \<lambda>p.\<exists>Y(Stage(Y) & Yp)\<close>.\<close>

definition gr_P :: oterm where
  "gr_P = Lam Prop (gr_Pbody gr_Pure (Var 0))"

text \<open>\<open>M = \<lambda>c\<^sup>u\<^sup>\<rightarrow>\<^sup>t.\<lambda>p.\<exists>Y\<^sup>u(cY & \<forall>\<Z>(Cl\<^sub>c(\<Z>) \<rightarrow> \<Z>(Y)) & Yp)\<close>.\<close>

definition gr_M :: oterm where
  "gr_M = Lam gr_cls (Lam Prop (gr_Pbody (Var (Suc 0)) (Var 0)))"

lemma gr_Pbody_rename[grs]:
  "rename \<rho> (gr_Pbody c p) = gr_Pbody (rename \<rho> c) (rename \<rho> p)"
  by (simp add: gr_Pbody_def grs grk_rename_lift_shift)

lemma gr_Pbody_subst[grs]:
  "subst t (gr_Pbody c p) = gr_Pbody (subst t c) (subst t p)"
  by (simp add: gr_Pbody_def grs subst_lift_shift)

lemma gr_Pbody_shift[grs]: "shift (gr_Pbody c p) = gr_Pbody (shift c) (shift p)"
  using gr_Pbody_rename[of Suc c p] by (simp add: shift_def)

lemma gr_Pbody_subst0[grs]:
  "subst0 N (gr_Pbody c p) = gr_Pbody (subst0 N c) (subst0 N p)"
  using gr_Pbody_subst[of "case_nat N Var" c p] by (simp add: subst0_def)

lemma typed_gr_Pbody[gr_ty]:
  "\<Gamma> \<turnstile> c : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> gr_Pbody c p : Prop"
  unfolding gr_Pbody_def by gr_typ

lemma gr_P_rename[grs]: "rename \<rho> gr_P = gr_P"
  by (simp add: gr_P_def grs)

lemma gr_P_subst[grs]: "subst t gr_P = gr_P"
  by (simp add: gr_P_def grs)

lemma gr_P_shift[grs]: "shift gr_P = gr_P"
  by (simp add: shift_def grs)

lemma gr_P_subst0[grs]: "subst0 N gr_P = gr_P"
  by (simp add: subst0_def grs)

lemma typed_gr_P[gr_ty]: "\<Gamma> \<turnstile> gr_P : gr_u"
  unfolding gr_P_def by gr_typ

lemma typed_gr_M[gr_ty]: "\<Gamma> \<turnstile> gr_M : gr_cls \<rightarrow>\<^sub>o gr_u"
  unfolding gr_M_def by gr_typ

lemmas gr_stage_defs =
  gr_Kbot_def gr_wit_def gr_cov_def gr_ClCov_def gr_Cl1_def gr_Cl2_def gr_Cl3_def gr_Cl_def
  gr_StageAll_def gr_Stage_def gr_Pbody_def

lemma gr_M_consts: "consts_of gr_M = {}"
  by (simp add: gr_M_def gr_stage_defs gr_sub_def gr_Sigma_consts
      ObjFalse_def ObjTrue_def shift_def)

text \<open>"is closed and logical, of type \<open>(u \<rightarrow> t) \<rightarrow> u\<close>".\<close>

theorem gr_M_logical:
  "[] \<turnstile> gr_M : gr_cls \<rightarrow>\<^sub>o gr_u \<and> pp_logical_vocabulary gr_M"
  by (simp add: typed_gr_M gr_M_consts pp_logical_vocabulary_def)

text \<open>Unfolding \<open>Pp\<close> by beta.\<close>

lemma gr_P_app:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_P p \<longleftrightarrow>\<^sub>o gr_Pbody gr_Pure p)"
proof -
  have ty: "\<Gamma> \<turnstile> App gr_P p : Prop" by (gr_typ pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (Lam Prop (gr_Pbody gr_Pure (Var 0))) p \<longleftrightarrow>\<^sub>o
        subst0 p (gr_Pbody gr_Pure (Var 0)))"
    by (rule grk_beta1[OF ty[unfolded gr_P_def]])
  then show ?thesis by (simp add: gr_P_def grs)
qed

lemma gr_Pbody_I:
  assumes ct: "\<Gamma> \<turnstile> c : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj (gr_Stage c Y) (App Y p)) (gr_Pbody c p)"
proof -
  let ?body = "Conj (gr_Stage (shift c) (Var 0)) (App (Var 0) (shift p))"
  have bt: "gr_u # \<Gamma> \<turnstile> ?body : Prop" by (gr_typ ct pt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (subst0 Y ?body) (Exists gr_u ?body)"
    by (rule grk_EG[OF bt yt])
  then show ?thesis by (simp add: gr_Pbody_def grs)
qed

lemma gr_Pbody_E:
  assumes qt: "\<Gamma> \<turnstile> Q : Prop"
    and d: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift c) (Var 0)) (App (Var 0) (shift p))) (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pbody c p) Q"
  unfolding gr_Pbody_def by (rule grk_inst_imp[OF qt d])

text \<open>"By beta-conversion, \<open>M(Pure\<^sub>u) = P\<close>": the contraction step.\<close>

lemma gr_M_beta_step: "compatible_step beta_contract (App gr_M gr_Pure) gr_P"
proof -
  let ?body = "Lam Prop (gr_Pbody (Var (Suc 0)) (Var 0))"
  have step: "compatible_step beta_contract (App (Lam gr_cls ?body) gr_Pure)
      (subst0 gr_Pure ?body)"
    by (rule compatible_step.root, rule beta_contract.beta)
  have e: "subst0 gr_Pure ?body = gr_P"
    by (simp add: subst0_def gr_P_def grs)
  show ?thesis using step by (simp only: e gr_M_def)
qed

end
