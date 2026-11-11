theory Goodman_PP_Refutation_Lemma5
  imports Goodman_PP_Refutation_Objects_Lemma5
begin

text \<open>
  LEMMA 5 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "Every stage \<open>Y\<close> satisfies
       (14)  \<open>\<forall>p(Y(\<not>p) \<leftrightarrow> Yp)\<close>.
     If a stage \<open>Y\<close> satisfies \<open>Yp\<close>, then there is a stage \<open>Y\<^sub>0\<close> such that
       (15)  \<open>\<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p\<close>."

  Stock: \<open>T\<^sub>0\<close> (hypothesis \<open>gr_T0 \<subseteq> T\<close>), needed only through Lemma 4.
  Nothing is necessitated in this theory.
\<close>

section \<open>(14)\<close>

text \<open>
  "For symmetry, apply Lemma 4 to the property \<open>\<lambda>Y.\<forall>p(Y(\<not>p) \<leftrightarrow> Yp)\<close>."
  That property is \<open>gr_Sym\<close>.
\<close>

text \<open>"The base case follows from \<open>K\<^sub>\<bottom>p = \<bottom>\<close>."\<close>

lemma gr_Lemma5_sym_base: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind1 gr_Sym"
proof -
  have a: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Kbot (Neg (Var 0)) \<longleftrightarrow>\<^sub>o ObjFalse)"
    by (rule gr_Kbot_app) gr_typ
  have b: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Kbot (Var 0) \<longleftrightarrow>\<^sub>o ObjFalse)"
    by (rule gr_Kbot_app) gr_typ
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Kbot (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App gr_Kbot (Var 0))"
    by (rule grk_iff_trans[OF a grk_iff_sym[OF b]])
  then have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (shift gr_Kbot) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift gr_Kbot) (Var 0))"
    by (simp add: grs)
  then have s: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_SymF gr_Kbot" by (rule gr_SymF_I)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_Sym gr_Kbot"
    by (rule grk_iff_mp_rev[OF gr_Sym_app s]) gr_typ
  then show ?thesis by (simp only: gr_Ind1_def)
qed

text \<open>"Every successor is symmetric by (4)."\<close>

lemma gr_Lemma5_sym_Sigma:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_SymF (App gr_Sigma Y)"
proof (rule gr_SymF_I)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (App gr_Sigma (shift Y)) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (App gr_Sigma (shift Y)) (Var 0))"
    by (rule gr_Lemma1_4) (gr_typ yt)+
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (shift (App gr_Sigma Y)) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift (App gr_Sigma Y)) (Var 0))"
    by (simp add: grs)
qed

lemma gr_Lemma5_sym_step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind2 gr_Pure gr_Sym"
proof (rule gr_Ind2_I)
  let ?\<Delta> = "gr_u # \<Gamma>"
  let ?Y = "Var 0"
  have s: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_SymF (App gr_Sigma ?Y)"
    by (rule gr_Lemma5_sym_Sigma) gr_typ
  have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_Sym (App gr_Sigma ?Y)"
    by (rule grk_iff_mp_rev[OF gr_Sym_app s]) gr_typ
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage gr_Pure ?Y) (App gr_Sym ?Y)) (App gr_Sym (App gr_Sigma ?Y))"
    by (rule CEV_axiom_imp_of_right[OF _ a]) gr_typ
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift gr_Pure) (Var 0)) (App (shift gr_Sym) (Var 0)))
        (App (shift gr_Sym) (App gr_Sigma (Var 0)))"
    by (simp add: grs)
qed

text \<open>
  "For the union condition, if \<open>Bs\<close>, choose a symmetric stage \<open>Y \<subseteq> B\<close> with
  \<open>Ys\<close>.  Then \<open>Y(\<not>s)\<close>, so \<open>B(\<not>s)\<close>."
\<close>

lemma gr_Lemma5_sym_union_half:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ICov gr_Pure gr_Sym B) (gr_NegCl B)"
proof -
  let ?\<Delta>2 = "gr_u # Prop # \<Gamma>"
  let ?B2 = "shift (shift B)"
  let ?Y = "Var 0"
  let ?s = "Var (Suc 0)"
  have a: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Sym ?Y \<longleftrightarrow>\<^sub>o gr_SymF ?Y)"
    by (rule gr_Sym_app) gr_typ
  have e: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_SymF ?Y) (App ?Y (Neg ?s) \<longleftrightarrow>\<^sub>o App ?Y ?s)"
    by (rule gr_SymF_E) gr_typ+
  have sb: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_sub ?Y ?B2) (Imp (App ?Y (Neg ?s)) (App ?B2 (Neg ?s)))"
    by (rule gr_sub_E) (gr_typ bt)+
  have ty: "?\<Delta>2 \<turnstile> Imp (gr_iwit gr_Pure gr_Sym ?B2 ?s ?Y) (App ?B2 (Neg ?s)) : Prop"
    by (gr_typ bt)
  have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_iwit gr_Pure gr_Sym ?B2 ?s ?Y) (App ?B2 (Neg ?s))"
    by (rule grk_PC3[OF a e sb ty]) gr_taut
  then have pw: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_iwit (shift (shift gr_Pure)) (shift (shift gr_Sym)) ?B2 (Var (Suc 0)) (Var 0))
        (shift (App (shift B) (Neg (Var 0))))"
    by (simp add: grs gr_shift_Var)
  have ct: "Prop # \<Gamma> \<turnstile> App (shift B) (Neg (Var 0)) : Prop" by (gr_typ bt)
  show ?thesis
    unfolding gr_ICov_def gr_NegCl_def by (rule gr_cov_E[OF bt ct pw])
qed

text \<open>
  "Applying the same argument to \<open>\<not>s\<close> and using double negation gives the
  converse."
\<close>

lemma gr_Lemma5_NegCl_sym:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_NegCl B) (gr_SymF B)"
proof (rule gr_SymF_I_imp)
  show "\<Gamma> \<turnstile> gr_NegCl B : Prop" by (gr_typ bt)
  let ?\<Delta> = "Prop # \<Gamma>"
  let ?B = "shift B"
  let ?s = "Var 0"
  have e1: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_NegCl ?B) (Imp (App ?B ?s) (App ?B (Neg ?s)))"
    by (rule gr_NegCl_E) (gr_typ bt)+
  have e2: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_NegCl ?B) (Imp (App ?B (Neg ?s)) (App ?B (Neg (Neg ?s))))"
    by (rule gr_NegCl_E) (gr_typ bt)+
  have dn: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Neg (Neg ?s)) ?s"
    by (rule grk_DN) gr_typ
  have ll: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop (Neg (Neg ?s)) ?s) (Imp (App ?B (Neg (Neg ?s))) (App ?B ?s))"
    by (rule grk_LL) (gr_typ bt)+
  have ty: "?\<Delta> \<turnstile> Imp (gr_NegCl ?B) (App ?B (Neg ?s) \<longleftrightarrow>\<^sub>o App ?B ?s) : Prop"
    by (gr_typ bt)
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_NegCl ?B) (App ?B (Neg ?s) \<longleftrightarrow>\<^sub>o App ?B ?s)"
    by (rule grk_PC4[OF e1 e2 dn ll ty]) gr_taut
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (gr_NegCl B)) (App (shift B) (Neg (Var 0)) \<longleftrightarrow>\<^sub>o App (shift B) (Var 0))"
    by (simp add: grs)
qed

lemma gr_Lemma5_sym_limit: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind3 gr_Pure gr_Sym"
proof (rule gr_Ind3_I)
  let ?\<Delta> = "gr_u # \<Gamma>"
  let ?B = "Var 0"
  have h: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ICov gr_Pure gr_Sym ?B) (gr_NegCl ?B)"
    by (rule gr_Lemma5_sym_union_half) gr_typ
  have n: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_NegCl ?B) (gr_SymF ?B)"
    by (rule gr_Lemma5_NegCl_sym) gr_typ
  have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Sym ?B \<longleftrightarrow>\<^sub>o gr_SymF ?B)"
    by (rule gr_Sym_app) gr_typ
  have ty: "?\<Delta> \<turnstile> Imp (Conj (App gr_Pure ?B) (gr_ICov gr_Pure gr_Sym ?B))
      (App gr_Sym ?B) : Prop"
    by gr_typ
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App gr_Pure ?B) (gr_ICov gr_Pure gr_Sym ?B)) (App gr_Sym ?B)"
    by (rule grk_PC3[OF h n a ty]) gr_taut
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App (shift gr_Pure) (Var 0)) (gr_ICov (shift gr_Pure) (shift gr_Sym) (Var 0)))
        (App (shift gr_Sym) (Var 0))"
    by (simp add: grs)
qed

text \<open>(14): every stage \<open>Y\<close> satisfies \<open>\<forall>p(Y(\<not>p) \<leftrightarrow> Yp)\<close>.\<close>

theorem gr_Lemma5_14:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (gr_SymF Y)"
proof -
  have i: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (App gr_Sym Y)"
    by (rule gr_Lemma4_induct_rule[OF st typed_gr_Sym yt
          gr_Lemma5_sym_base gr_Lemma5_sym_step gr_Lemma5_sym_limit])
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_Sym Y \<longleftrightarrow>\<^sub>o gr_SymF Y)" by (rule gr_Sym_app[OF yt])
  have ty: "\<Gamma> \<turnstile> Imp (gr_Stage gr_Pure Y) (gr_SymF Y) : Prop" by (gr_typ yt)
  show ?thesis by (rule grk_PC2[OF i a ty]) gr_taut
qed

text \<open>Its instance at a proposition \<open>p\<close>:  \<open>Stage(Y) \<rightarrow> (Y(\<not>p) \<leftrightarrow> Yp)\<close>.\<close>

theorem gr_Lemma5_14_at:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (App Y (Neg p) \<longleftrightarrow>\<^sub>o App Y p)"
  by (rule grk_imp_trans[OF gr_Lemma5_14[OF st yt] gr_SymF_E[OF yt pt]])

section \<open>(15)\<close>

text \<open>
  "For the second assertion fix \<open>p\<close> and apply Lemma 4 to
     \<open>\<Psi> = \<lambda>Y\<^sup>u.(Yp \<rightarrow> \<exists>Y\<^sub>0\<^sup>u(Stage(Y\<^sub>0) & \<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p))\<close>."
  That property, with the parameter \<open>p\<close>, is \<open>gr_PredProp gr_Pure p\<close>.
\<close>

text \<open>"The base case is vacuous."\<close>

lemma gr_Lemma5_pred_base:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind1 (gr_PredProp gr_Pure p)"
proof -
  let ?P = "gr_PredProp gr_Pure p"
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App ?P gr_Kbot \<longleftrightarrow>\<^sub>o Imp (App gr_Kbot p) (gr_PredEx gr_Pure p))"
    by (rule gr_PredProp_app) (gr_typ pt)+
  have v: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Kbot p) (gr_PredEx gr_Pure p)"
    by (rule gr_Kbot_empty) (gr_typ pt)+
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App ?P gr_Kbot" by (rule grk_iff_mp_rev[OF a v])
  then show ?thesis by (simp only: gr_Ind1_def)
qed

text \<open>
  "In the successor case suppose that \<open>(\<Sigma>Y)p\<close>.  If \<open>Yp\<close>, the induction
  hypothesis supplies \<open>Y\<^sub>0\<close>.  If \<open>\<not>Yp\<close>, take \<open>Y\<^sub>0 = Y\<close>."
\<close>

lemma gr_Lemma5_pred_step:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind2 gr_Pure (gr_PredProp gr_Pure p)"
proof (rule gr_Ind2_I)
  let ?\<Delta> = "gr_u # \<Gamma>"
  let ?p = "shift p"
  let ?Y = "Var 0"
  let ?P = "gr_PredProp gr_Pure ?p"
  let ?SY = "App gr_Sigma ?Y"
  have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?P ?Y \<longleftrightarrow>\<^sub>o Imp (App ?Y ?p) (gr_PredEx gr_Pure ?p))"
    by (rule gr_PredProp_app) (gr_typ pt)+
  have b: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?P ?SY \<longleftrightarrow>\<^sub>o Imp (App ?SY ?p) (gr_PredEx gr_Pure ?p))"
    by (rule gr_PredProp_app) (gr_typ pt)+
  text \<open>The witness \<open>Y\<^sub>0 = Y\<close>.\<close>
  have eg: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage gr_Pure ?Y) (Conj (Neg (App ?Y ?p)) (App ?SY ?p)))
        (gr_PredEx gr_Pure ?p)"
    by (rule gr_PredEx_I) (gr_typ pt)+
  have ty: "?\<Delta> \<turnstile> Imp (Conj (gr_Stage gr_Pure ?Y) (App ?P ?Y)) (App ?P ?SY) : Prop"
    by (gr_typ pt)
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj (gr_Stage gr_Pure ?Y) (App ?P ?Y)) (App ?P ?SY)"
    by (rule grk_PC3[OF a b eg ty]) gr_taut
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Stage (shift gr_Pure) (Var 0)) (App (shift (gr_PredProp gr_Pure p)) (Var 0)))
        (App (shift (gr_PredProp gr_Pure p)) (App gr_Sigma (Var 0)))"
    by (simp add: grs)
qed

text \<open>
  "For the union condition, an instance \<open>Bp\<close> has a stage \<open>Y \<subseteq> B\<close> with \<open>Yp\<close>
  and \<open>\<Psi>(Y)\<close>.  The latter supplies the desired \<open>Y\<^sub>0\<close>."
\<close>

lemma gr_Lemma5_pred_limit:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind3 gr_Pure (gr_PredProp gr_Pure p)"
proof (rule gr_Ind3_I)
  let ?\<Delta> = "gr_u # \<Gamma>"
  let ?p = "shift p"
  let ?B = "Var 0"
  let ?P = "gr_PredProp gr_Pure ?p"
  have ce: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_ICov gr_Pure ?P ?B) (Imp (App ?B ?p) (gr_IEx gr_Pure ?P ?B ?p))"
    by (rule gr_ICov_E) (gr_typ pt)+
  have ex: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_IEx gr_Pure ?P ?B ?p) (gr_PredEx gr_Pure ?p)"
  proof (rule gr_IEx_E)
    show "?\<Delta> \<turnstile> gr_PredEx gr_Pure ?p : Prop" by (gr_typ pt)
    let ?\<Delta>2 = "gr_u # ?\<Delta>"
    let ?p2 = "shift ?p"
    let ?B2 = "shift ?B"
    let ?Y = "Var 0"
    let ?P2 = "gr_PredProp gr_Pure ?p2"
    have a: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        (App ?P2 ?Y \<longleftrightarrow>\<^sub>o Imp (App ?Y ?p2) (gr_PredEx gr_Pure ?p2))"
      by (rule gr_PredProp_app) (gr_typ pt)+
    have ty: "?\<Delta>2 \<turnstile> Imp (gr_iwit gr_Pure ?P2 ?B2 ?p2 ?Y) (gr_PredEx gr_Pure ?p2) : Prop"
      by (gr_typ pt)
    have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_iwit gr_Pure ?P2 ?B2 ?p2 ?Y) (gr_PredEx gr_Pure ?p2)"
      by (rule grk_PC1[OF a ty]) gr_taut
    then show "gr_u # ?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_iwit (shift gr_Pure) (shift ?P) (shift ?B) (shift ?p) (Var 0))
          (shift (gr_PredEx gr_Pure ?p))"
      by (simp add: grs)
  qed
  have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?P ?B \<longleftrightarrow>\<^sub>o Imp (App ?B ?p) (gr_PredEx gr_Pure ?p))"
    by (rule gr_PredProp_app) (gr_typ pt)+
  have ty: "?\<Delta> \<turnstile> Imp (Conj (App gr_Pure ?B) (gr_ICov gr_Pure ?P ?B)) (App ?P ?B) : Prop"
    by (gr_typ pt)
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App gr_Pure ?B) (gr_ICov gr_Pure ?P ?B)) (App ?P ?B)"
    by (rule grk_PC3[OF ce ex a ty]) gr_taut
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App (shift gr_Pure) (Var 0))
          (gr_ICov (shift gr_Pure) (shift (gr_PredProp gr_Pure p)) (Var 0)))
        (App (shift (gr_PredProp gr_Pure p)) (Var 0))"
    by (simp add: grs)
qed

text \<open>
  (15): "If a stage \<open>Y\<close> satisfies \<open>Yp\<close>, then there is a stage \<open>Y\<^sub>0\<close> such that
  \<open>\<not>Y\<^sub>0p & (\<Sigma>Y\<^sub>0)p\<close>."   ("Generalizing \<open>p\<close> proves the assertion": \<open>p\<close> is an
  arbitrary term here.)
\<close>

theorem gr_Lemma5_15:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Stage gr_Pure Y) (Imp (App Y p) (gr_PredEx gr_Pure p))"
proof -
  let ?P = "gr_PredProp gr_Pure p"
  have pst: "\<Gamma> \<turnstile> ?P : gr_cls" by (gr_typ pt)
  have i: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (App ?P Y)"
    by (rule gr_Lemma4_induct_rule[OF st pst yt gr_Lemma5_pred_base[OF pt]
          gr_Lemma5_pred_step[OF pt] gr_Lemma5_pred_limit[OF pt]])
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?P Y \<longleftrightarrow>\<^sub>o Imp (App Y p) (gr_PredEx gr_Pure p))"
    by (rule gr_PredProp_app) (gr_typ pt yt)+
  have ty: "\<Gamma> \<turnstile> Imp (gr_Stage gr_Pure Y) (Imp (App Y p) (gr_PredEx gr_Pure p)) : Prop"
    by (gr_typ yt pt)
  show ?thesis by (rule grk_PC2[OF i a ty]) gr_taut
qed

end
