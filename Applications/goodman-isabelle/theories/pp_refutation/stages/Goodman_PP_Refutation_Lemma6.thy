theory Goodman_PP_Refutation_Lemma6
  imports Goodman_PP_Refutation_Lemma5
begin

text \<open>
  LEMMA 6 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "The theory \<open>\<T>\<close> proves that \<open>P\<close> is pure, \<open>P\<close> is a stage, and \<open>L \<subseteq> P\<close>."

  with, from its proof, (16) \<open>\<Sigma>P \<subseteq> P\<close> and its necessitation.  Stock: \<open>\<T>\<close>
  (hypothesis \<open>gr_Th \<subseteq> T\<close>).  This is the only place where (PP_u) is used, and
  the only place where Necessitation is applied to a theorem whose proof uses
  the stock.
\<close>

section \<open>\<open>P\<close> is pure\<close>

text \<open>
  "The term defining \<open>P\<close> uses the single nonlogical constant \<open>Pure\<^sub>u\<close>. ...
  The term \<open>M\<close> is closed and logical, of type \<open>(u \<rightarrow> t) \<rightarrow> u\<close>
  (\<open>gr_M_logical\<close>).  By beta-conversion, \<open>M(Pure\<^sub>u) = P\<close>."
\<close>

theorem gr_Lemma6_M_Pure_eq_P:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq gr_u (App gr_M gr_Pure) gr_P"
proof -
  have at: "\<Gamma> \<turnstile> App gr_M gr_Pure : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule has_type.App[OF typed_gr_M typed_pp_Pure])
  have bt: "\<Gamma> \<turnstile> gr_P : pp_unary_ty"
    unfolding pp_unary_ty_def by (rule typed_gr_P)
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq pp_unary_ty (App gr_M gr_Pure) gr_P"
    by (rule CEV_unary_eq_of_beta_step[OF at bt gr_M_beta_step])
  then show ?thesis unfolding pp_unary_ty_def by (rule CEV_axiom_proves.Base)
qed

text \<open>"Logical purity gives \<open>Pure(M)\<close>".\<close>

theorem gr_Lemma6_Pure_M:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (gr_cls \<rightarrow>\<^sub>o gr_u) gr_M"
  by (rule gr_T0_purity[OF gr_Th_T0[OF st] typed_gr_M gr_M_consts typed_gr_M])

text \<open>
  "... while (PP_u) gives \<open>Pure\<^sub>u\<^sub>\<rightarrow>\<^sub>t(Pure\<^sub>u)\<close>.  Application closure at input type
  \<open>u \<rightarrow> t\<close> and output type \<open>u\<close> therefore gives \<open>Pure(P)\<close>."
\<close>

theorem gr_Lemma6_Pure_P:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_u gr_P"
proof -
  let ?MP = "App gr_M gr_Pure"
  have mpt: "\<Gamma> \<turnstile> ?MP : gr_u" by (rule has_type.App[OF typed_gr_M typed_pp_Pure])
  have pm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (gr_cls \<rightarrow>\<^sub>o gr_u) gr_M"
    by (rule gr_Lemma6_Pure_M[OF st])
  have pp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_cls gr_Pure" by (rule gr_Th_PP[OF st])
  have ac: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_pure (gr_cls \<rightarrow>\<^sub>o gr_u) gr_M) (pp_pure gr_cls gr_Pure))
        (pp_pure gr_u ?MP)"
    by (rule gr_T0_application[OF gr_Th_T0[OF st] typed_gr_M typed_pp_Pure])
  have pmp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_u ?MP"
    by (rule grk_MP[OF CEV_axiom_conj_intro[OF pm pp] ac])
  text \<open>Transport along the identity \<open>M(Pure\<^sub>u) = P\<close>.\<close>
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq gr_u ?MP gr_P) (Imp (App gr_Pure ?MP) (App gr_Pure gr_P))"
    by (rule grk_LL[OF mpt typed_gr_P typed_pp_Pure])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure ?MP) (App gr_Pure gr_P)"
    by (rule grk_MP[OF gr_Lemma6_M_Pure_eq_P ll])
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_pure gr_u ?MP) (pp_pure gr_u gr_P)"
    by (simp only: pp_pure_def)
  then show ?thesis by (rule grk_MP[OF pmp])
qed

section \<open>\<open>P\<close> is a stage\<close>

text \<open>
  "Equation (13) gives \<open>Y \<subseteq> P\<close> for every stage \<open>Y\<close>."  (Stated after (13);
  logic only.)
\<close>

lemma gr_Lemma6_Stage_in_P:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (Imp (App Y p) (App gr_P p))"
proof -
  have i: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage gr_Pure Y) (App Y p)) (gr_Pbody gr_Pure p)"
    by (rule gr_Pbody_I) (gr_typ yt pt)+
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_P p \<longleftrightarrow>\<^sub>o gr_Pbody gr_Pure p)"
    by (rule gr_P_app[OF pt])
  have ty: "\<Gamma> \<turnstile> Imp (gr_Stage gr_Pure Y) (Imp (App Y p) (App gr_P p)) : Prop"
    by (gr_typ yt pt)
  show ?thesis by (rule grk_PC2[OF i a ty]) gr_taut
qed

theorem gr_Lemma6_Stage_sub_P:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (gr_sub Y gr_P)"
proof (rule gr_sub_I_imp)
  show "\<Gamma> \<turnstile> gr_Stage gr_Pure Y : Prop" by (gr_typ yt)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Stage gr_Pure (shift Y)) (Imp (App (shift Y) (Var 0)) (App gr_P (Var 0)))"
    by (rule gr_Lemma6_Stage_in_P) (gr_typ yt)+
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (gr_Stage gr_Pure Y)) (Imp (App (shift Y) (Var 0)) (App (shift gr_P) (Var 0)))"
    by (simp add: grs)
qed

text \<open>
  "For each \<open>p\<close> with \<open>Pp\<close>, definition (13) supplies a stage \<open>Y\<close> with \<open>Yp\<close>,
  and \<open>Y \<subseteq> P\<close> holds by the same definition."
\<close>

theorem gr_Lemma6_SCov_P: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_SCov gr_Pure gr_P"
proof -
  let ?\<Delta> = "Prop # \<Gamma>"
  let ?s = "Var 0"
  let ?\<Delta>2 = "gr_u # ?\<Delta>"
  let ?Y = "Var 0"
  let ?s2 = "Var (Suc 0)"
  let ?W = "gr_swit (shift (shift gr_Pure)) (shift (shift gr_P)) (Var (Suc 0)) (Var 0)"
  have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_P ?s \<longleftrightarrow>\<^sub>o gr_Pbody gr_Pure ?s)"
    by (rule gr_P_app) gr_typ
  have sub: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure ?Y) (gr_sub ?Y gr_P)"
    by (rule gr_Lemma6_Stage_sub_P) gr_typ
  have ty1: "?\<Delta>2 \<turnstile> Imp (Conj (gr_Stage gr_Pure ?Y) (App ?Y ?s2))
      (gr_swit gr_Pure gr_P ?s2 ?Y) : Prop"
    by gr_typ
  have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage gr_Pure ?Y) (App ?Y ?s2)) (gr_swit gr_Pure gr_P ?s2 ?Y)"
    by (rule grk_PC1[OF sub ty1]) gr_taut
  then have pw: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift gr_Pure) (Var 0)) (App (Var 0) (shift ?s))) ?W"
    by (simp add: grs gr_shift_Var)
  have ex: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pbody gr_Pure ?s) (Exists gr_u ?W)"
    unfolding gr_Pbody_def by (rule grk_exists_mono[OF pw])
  have ty: "?\<Delta> \<turnstile> Imp (App gr_P ?s) (Exists gr_u ?W) : Prop" by gr_typ
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_P ?s) (Exists gr_u ?W)"
    by (rule grk_PC2[OF a ex ty]) gr_taut
  then have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App (shift gr_P) (Var 0)) (Exists gr_u ?W)"
    by (simp add: grs)
  then show ?thesis unfolding gr_SCov_def by (rule gr_cov_I)
qed

text \<open>
  "Since \<open>P\<close> is pure, the union condition for \<open>Stage\<close> applies to \<open>P\<close> and
  proves \<open>Stage(P)\<close>."
\<close>

theorem gr_Lemma6_Stage_P:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Stage gr_Pure gr_P"
proof -
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_u gr_P" by (rule gr_Lemma6_Pure_P[OF st])
  then have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_Pure gr_P" by (simp only: pp_pure_def)
  have un: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App gr_Pure gr_P) (gr_SCov gr_Pure gr_P)) (gr_Stage gr_Pure gr_P)"
    by (rule gr_Lemma4_Stage_union[OF typed_gr_P])
  show ?thesis by (rule grk_MP[OF CEV_axiom_conj_intro[OF pure gr_Lemma6_SCov_P] un])
qed

section \<open>(16), its necessitation, and \<open>L \<subseteq> P\<close>\<close>

text \<open>"Successor closure gives \<open>Stage(\<Sigma>P)\<close>, and hence (16) \<open>\<Sigma>P \<subseteq> P\<close>."\<close>

theorem gr_Lemma6_Stage_SigmaP:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Stage gr_Pure (App gr_Sigma gr_P)"
  by (rule grk_MP[OF gr_Lemma6_Stage_P[OF st]
        gr_Lemma4_Stage_Sigma[OF gr_Th_T0[OF st] typed_gr_P]])

theorem gr_Lemma6_16:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sub (App gr_Sigma gr_P) gr_P"
  by (rule grk_MP[OF gr_Lemma6_Stage_SigmaP[OF st] gr_Lemma6_Stage_sub_P]) gr_typ

text \<open>
  "This is a closed theorem of the axiom extension \<open>\<T>\<close>.  Its proof has used
  the Purity schema, Application closure, and (PP_u), with all temporary
  assumptions discharged."  Closedness of the formula:
\<close>

lemma gr_Lemma6_16_closed: "[] \<turnstile> gr_sub (App gr_Sigma gr_P) gr_P : Prop"
  by gr_typ

text \<open>"Necessitation therefore gives \<open>\<box>(\<Sigma>P \<subseteq> P)\<close>."\<close>

theorem gr_Lemma6_box_16:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (gr_sub (App gr_Sigma gr_P) gr_P)"
  by (rule grk_nec[OF gr_Lemma6_16[OF st]])

text \<open>"Thus \<open>Pre(P)\<close> holds, by (2)."\<close>

theorem gr_Lemma6_Pre_P:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Pre gr_P"
  unfolding gr_Pre_def by (rule gr_Lemma6_box_16[OF st])

text \<open>
  "Instantiating the quantifier in (3) at \<open>W = P\<close> now gives \<open>L \<subseteq> P\<close>."
\<close>

theorem gr_Lemma6_L_sub_P:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sub gr_L gr_P"
  by (rule grk_MP[OF gr_Lemma6_Pre_P[OF st] gr_Lemma2_inst[OF typed_gr_P]])

text \<open>Its instance at a proposition, in the form used in the proof of Theorem 1.\<close>

theorem gr_Lemma6_L_in_P:
  assumes st: "gr_Th \<subseteq> T" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_L p) (App gr_P p)"
  by (rule grk_MP[OF gr_Lemma6_L_sub_P[OF st] gr_sub_E]) (gr_typ pt)+

end
