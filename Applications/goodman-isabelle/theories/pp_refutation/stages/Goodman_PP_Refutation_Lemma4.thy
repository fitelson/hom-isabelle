theory Goodman_PP_Refutation_Lemma4
  imports Goodman_PP_Refutation_Objects_Induction
begin

text \<open>
  LEMMA 4 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "The property \<open>Stage\<close> is closed.  If a property \<open>\<Psi>\<close> of type \<open>u \<rightarrow> t\<close>
     satisfies the following three conditions, then every stage satisfies \<open>\<Psi>\<close>.
       1. \<open>\<Psi>(K\<^sub>\<bottom>)\<close>.
       2. If \<open>Y\<close> is a stage satisfying \<open>\<Psi>\<close>, then \<open>\<Psi>(\<Sigma>Y)\<close>.
       3. If \<open>B\<close> is pure and each \<open>s\<close> with \<open>Bs\<close> has a stage \<open>Y \<subseteq> B\<close> with
          \<open>\<Psi>(Y)\<close> and \<open>Ys\<close>, then \<open>\<Psi>(B)\<close>.
     Parameters are allowed in \<open>\<Psi>\<close>.  Bound variables are chosen fresh for them."

  Stock: \<open>T\<^sub>0\<close> (hypothesis \<open>gr_T0 \<subseteq> T\<close>); the union condition for Stage needs
  no stock at all.  Nothing is necessitated in this theory.
\<close>

section \<open>\<open>K\<^sub>\<bottom>\<close> is a stage\<close>

text \<open>
  "The operator \<open>K\<^sub>\<bottom>\<close> is pure by the Purity schema and satisfies every closed
  property by its first condition.  Hence it is a stage."
\<close>

theorem gr_Lemma4_Stage_Kbot:
  assumes st: "gr_T0 \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Stage gr_Pure gr_Kbot"
proof -
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_u gr_Kbot"
    by (rule gr_T0_purity[OF st typed_gr_Kbot gr_Kbot_consts typed_gr_Kbot])
  then have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_Pure gr_Kbot" by (simp only: pp_pure_def)
  have "gr_cls # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Cl gr_Pure (Var 0)) (App (Var 0) gr_Kbot)"
    by (rule gr_Cl_1) gr_typ+
  then have "gr_cls # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Cl (shift gr_Pure) (Var 0)) (App (Var 0) (shift gr_Kbot))"
    by (simp add: grs)
  then have all: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_StageAll gr_Pure gr_Kbot"
    unfolding gr_StageAll_def by (rule grk_gen)
  have ty: "\<Gamma> \<turnstile> gr_Stage gr_Pure gr_Kbot : Prop" by gr_typ
  show ?thesis by (rule grk_PC2[OF pure all ty]) gr_taut
qed

section \<open>The successor of a stage is a stage\<close>

text \<open>
  "If \<open>Y\<close> is a stage, then \<open>\<Sigma>Y\<close> is pure by logical purity of \<open>\<Sigma>\<close> and
  Application closure.  Every closed property contains \<open>Y\<close> and hence \<open>\<Sigma>Y\<close>,
  making \<open>\<Sigma>Y\<close> a stage."
\<close>

lemma gr_Lemma4_Pure_Sigma:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure Y) (App gr_Pure (App gr_Sigma Y))"
proof -
  have ps: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Sigma"
    by (rule gr_T0_purity[OF st typed_gr_Sigma gr_Sigma_consts typed_gr_Sigma])
  have ac: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Sigma) (pp_pure gr_u Y))
        (pp_pure gr_u (App gr_Sigma Y))"
    by (rule gr_T0_application[OF st typed_gr_Sigma yt])
  have ty: "\<Gamma> \<turnstile> Imp (App gr_Pure Y) (App gr_Pure (App gr_Sigma Y)) : Prop"
    by (gr_typ yt)
  show ?thesis by (rule grk_PC2[OF ps ac ty]) gr_taut
qed

theorem gr_Lemma4_Stage_Sigma:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (gr_Stage gr_Pure (App gr_Sigma Y))"
proof -
  let ?H = "gr_Stage gr_Pure Y"
  have ht: "\<Gamma> \<turnstile> ?H : Prop" by (gr_typ yt)
  have syt: "\<Gamma> \<turnstile> App gr_Sigma Y : gr_u" by (gr_typ yt)
  have sp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (App gr_Pure Y)"
    by (rule gr_Stage_pure) (gr_typ yt)+
  have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (App gr_Pure (App gr_Sigma Y))"
    by (rule grk_imp_trans[OF sp gr_Lemma4_Pure_Sigma[OF st yt]])
  have all: "gr_cls # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Imp (gr_Cl (shift gr_Pure) (Var 0)) (App (Var 0) (shift (App gr_Sigma Y))))"
  proof -
    let ?\<Delta> = "gr_cls # \<Gamma>"
    let ?Y = "shift Y"
    let ?Z = "Var 0"
    have e: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure ?Y) (Imp (gr_Cl gr_Pure ?Z) (App ?Z ?Y))"
      by (rule gr_Stage_E) (gr_typ yt)+
    have p: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure ?Y) (App gr_Pure ?Y)"
      by (rule gr_Stage_pure) (gr_typ yt)+
    have c: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Cl gr_Pure ?Z)
        (Imp (App gr_Pure ?Y) (Imp (App ?Z ?Y) (App ?Z (App gr_Sigma ?Y))))"
      by (rule gr_Cl_2) (gr_typ yt)+
    have ty: "?\<Delta> \<turnstile> Imp (gr_Stage gr_Pure ?Y)
        (Imp (gr_Cl gr_Pure ?Z) (App ?Z (App gr_Sigma ?Y))) : Prop"
      by (gr_typ yt)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Stage gr_Pure ?Y) (Imp (gr_Cl gr_Pure ?Z) (App ?Z (App gr_Sigma ?Y)))"
      by (rule grk_PC3[OF e p c ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  show ?thesis by (rule gr_Stage_I_imp[OF ht typed_pp_Pure syt pure all])
qed

section \<open>The union condition for \<open>Stage\<close>\<close>

text \<open>
  "For the union condition, suppose that \<open>B\<close> is pure and every \<open>s\<close> with \<open>Bs\<close>
  has a stage \<open>Y \<subseteq> B\<close> with \<open>Ys\<close>.  Fix a closed property \<open>\<Z>\<close>.  Each such \<open>Y\<close>
  is pure and satisfies \<open>\<Z>\<close>, by (12).  The third condition for \<open>\<Z>\<close> gives
  \<open>\<Z>(B)\<close>.  Generalizing \<open>\<Z>\<close> proves that \<open>B\<close> is a stage."
\<close>

text \<open>"Each such \<open>Y\<close> is pure and satisfies \<open>\<Z>\<close>, by (12)."\<close>

lemma gr_Lemma4_swit_wit:
  assumes zt: "\<Gamma> \<turnstile> Z : gr_cls" and bt: "\<Gamma> \<turnstile> B : gr_u" and st: "\<Gamma> \<turnstile> s : Prop"
    and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Cl gr_Pure Z) (Imp (gr_swit gr_Pure B s Y) (gr_wit gr_Pure Z B s Y))"
proof -
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (Imp (gr_Cl gr_Pure Z) (App Z Y))"
    by (rule gr_Stage_E) (gr_typ zt yt)+
  have ty: "\<Gamma> \<turnstile> Imp (gr_Cl gr_Pure Z)
      (Imp (gr_swit gr_Pure B s Y) (gr_wit gr_Pure Z B s Y)) : Prop"
    by (gr_typ zt bt st yt)
  show ?thesis by (rule grk_PC1[OF e ty]) gr_taut
qed

theorem gr_Lemma4_Stage_union:
  assumes bt: "\<Gamma> \<turnstile> B : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (App gr_Pure B) (gr_SCov gr_Pure B)) (gr_Stage gr_Pure B)"
proof -
  let ?H = "Conj (App gr_Pure B) (gr_SCov gr_Pure B)"
  have ht: "\<Gamma> \<turnstile> ?H : Prop" by (gr_typ bt)
  have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (App gr_Pure B)"
    by (rule grk_taut) (gr_typ bt, gr_taut)
  have all: "gr_cls # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Imp (gr_Cl (shift gr_Pure) (Var 0)) (App (Var 0) (shift B)))"
  proof -
    text \<open>Fix a closed property \<open>\<Z>\<close> (the variable \<open>Var 0\<close>).\<close>
    let ?\<Delta> = "gr_cls # \<Gamma>"
    let ?B = "shift B"
    let ?Z = "Var 0"
    let ?Z2 = "shift (shift ?Z)"
    let ?B2 = "shift (shift ?B)"
    have "gr_u # Prop # ?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Cl gr_Pure ?Z2)
          (Imp (gr_swit gr_Pure ?B2 (Var (Suc 0)) (Var 0))
            (gr_wit gr_Pure ?Z2 ?B2 (Var (Suc 0)) (Var 0)))"
      by (rule gr_Lemma4_swit_wit) (gr_typ bt)+
    then have pw: "gr_u # Prop # ?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (shift (shift (gr_Cl gr_Pure ?Z)))
          (Imp (gr_swit (shift (shift gr_Pure)) ?B2 (Var (Suc 0)) (Var 0))
            (gr_wit (shift (shift gr_Pure)) ?Z2 ?B2 (Var (Suc 0)) (Var 0)))"
      by (simp add: grs)
    have clt: "?\<Delta> \<turnstile> gr_Cl gr_Pure ?Z : Prop" by gr_typ
    have bt1: "?\<Delta> \<turnstile> ?B : gr_u" by (gr_typ bt)
    have cv: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Cl gr_Pure ?Z) (Imp (gr_SCov gr_Pure ?B) (gr_ClCov gr_Pure ?Z ?B))"
      unfolding gr_SCov_def gr_ClCov_def by (rule gr_cov_mono_imp[OF clt bt1 pw])
    text \<open>The third condition for \<open>\<Z>\<close> gives \<open>\<Z>(B)\<close>.\<close>
    have c3: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Cl gr_Pure ?Z)
        (Imp (Conj (App gr_Pure ?B) (gr_ClCov gr_Pure ?Z ?B)) (App ?Z ?B))"
      by (rule gr_Cl_3) (gr_typ bt)+
    have ty: "?\<Delta> \<turnstile> Imp (Conj (App gr_Pure ?B) (gr_SCov gr_Pure ?B))
        (Imp (gr_Cl gr_Pure ?Z) (App ?Z ?B)) : Prop"
      by (gr_typ bt)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (App gr_Pure ?B) (gr_SCov gr_Pure ?B)) (Imp (gr_Cl gr_Pure ?Z) (App ?Z ?B))"
      by (rule grk_PC2[OF c3 cv ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  text \<open>Generalizing \<open>\<Z>\<close> proves that \<open>B\<close> is a stage.\<close>
  show ?thesis by (rule gr_Stage_I_imp[OF ht typed_pp_Pure bt pure all])
qed

section \<open>\<open>Stage\<close> is closed\<close>

text \<open>
  "Thus \<open>Stage\<close> is closed."  The property \<open>Stage\<close> is the term
  \<open>gr_StageP gr_Pure\<close> of type \<open>u \<rightarrow> t\<close>.
\<close>

theorem gr_Lemma4_Stage_closed:
  assumes st: "gr_T0 \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Cl gr_Pure (gr_StageP gr_Pure)"
proof -
  let ?S = "gr_StageP gr_Pure"
  have spt: "\<Gamma> \<turnstile> ?S : gr_cls" by gr_typ
  text \<open>First condition.\<close>
  have c1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App ?S gr_Kbot"
    by (rule grk_iff_mp_rev[OF gr_StageP_app gr_Lemma4_Stage_Kbot[OF st]]) gr_typ+
  text \<open>Second condition.\<close>
  have c2: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (shift gr_Pure) (Var 0))
        (Imp (App (shift ?S) (Var 0)) (App (shift ?S) (App gr_Sigma (Var 0))))"
  proof -
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?Y = "Var 0"
    have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S ?Y \<longleftrightarrow>\<^sub>o gr_Stage gr_Pure ?Y)"
      by (rule gr_StageP_app) gr_typ+
    have b: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        (App ?S (App gr_Sigma ?Y) \<longleftrightarrow>\<^sub>o gr_Stage gr_Pure (App gr_Sigma ?Y))"
      by (rule gr_StageP_app) gr_typ+
    have s: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Stage gr_Pure ?Y) (gr_Stage gr_Pure (App gr_Sigma ?Y))"
      by (rule gr_Lemma4_Stage_Sigma[OF st]) gr_typ
    have ty: "?\<Delta> \<turnstile> Imp (App gr_Pure ?Y)
        (Imp (App ?S ?Y) (App ?S (App gr_Sigma ?Y))) : Prop"
      by gr_typ
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (App gr_Pure ?Y) (Imp (App ?S ?Y) (App ?S (App gr_Sigma ?Y)))"
      by (rule grk_PC3[OF a b s ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  text \<open>Third condition: the union condition for \<open>Stage\<close>.\<close>
  have c3: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (App (shift gr_Pure) (Var 0)) (gr_ClCov (shift gr_Pure) (shift ?S) (Var 0)))
        (App (shift ?S) (Var 0))"
  proof -
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?B = "Var 0"
    let ?B2 = "shift (shift ?B)"
    let ?\<Delta>2 = "gr_u # Prop # ?\<Delta>"
    have w: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S (Var 0) \<longleftrightarrow>\<^sub>o gr_Stage gr_Pure (Var 0))"
      by (rule gr_StageP_app) gr_typ+
    have ty1: "?\<Delta>2 \<turnstile> Imp (gr_wit gr_Pure ?S ?B2 (Var (Suc 0)) (Var 0))
        (gr_swit gr_Pure ?B2 (Var (Suc 0)) (Var 0)) : Prop"
      by gr_typ
    have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit gr_Pure ?S ?B2 (Var (Suc 0)) (Var 0))
          (gr_swit gr_Pure ?B2 (Var (Suc 0)) (Var 0))"
      by (rule grk_PC1[OF w ty1]) gr_taut
    then have pw: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit (shift (shift gr_Pure)) (shift (shift ?S)) ?B2 (Var (Suc 0)) (Var 0))
          (gr_swit (shift (shift gr_Pure)) ?B2 (Var (Suc 0)) (Var 0))"
      by (simp add: grs)
    have bt: "?\<Delta> \<turnstile> ?B : gr_u" by gr_typ
    have cv: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ClCov gr_Pure ?S ?B) (gr_SCov gr_Pure ?B)"
      unfolding gr_ClCov_def gr_SCov_def by (rule gr_cov_mono[OF bt pw])
    have un: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (App gr_Pure ?B) (gr_SCov gr_Pure ?B)) (gr_Stage gr_Pure ?B)"
      by (rule gr_Lemma4_Stage_union[OF bt])
    have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S ?B \<longleftrightarrow>\<^sub>o gr_Stage gr_Pure ?B)"
      by (rule gr_StageP_app) gr_typ+
    have ty: "?\<Delta> \<turnstile> Imp (Conj (App gr_Pure ?B) (gr_ClCov gr_Pure ?S ?B)) (App ?S ?B) : Prop"
      by gr_typ
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (App gr_Pure ?B) (gr_ClCov gr_Pure ?S ?B)) (App ?S ?B)"
      by (rule grk_PC3[OF cv un a ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  show ?thesis by (rule gr_Cl_I[OF typed_pp_Pure spt c1 c2 c3])
qed

section \<open>The induction principle\<close>

text \<open>
  "Now suppose that \<open>\<Psi>\<close> satisfies the displayed conditions and put
  \<open>\<W> = \<lambda>Y\<^sup>u.(Stage(Y) & \<Psi>(Y))\<close>.  The first and second closure conditions for
  \<open>\<W>\<close> follow from those for \<open>Stage\<close> and the corresponding conditions on \<open>\<Psi>\<close>.
  For the third, the witnesses in \<open>\<W>\<close> are stages satisfying \<open>\<Psi>\<close>, so the union
  condition for \<open>Stage\<close> gives \<open>Stage(B)\<close> and the third condition on \<open>\<Psi>\<close> gives
  \<open>\<Psi>(B)\<close>.  Thus \<open>Cl(\<W>)\<close>."
\<close>

theorem gr_Lemma4_Cl_W:
  assumes st: "gr_T0 \<subseteq> T" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (gr_Ind1 \<Psi>) (Conj (gr_Ind2 gr_Pure \<Psi>) (gr_Ind3 gr_Pure \<Psi>)))
      (gr_Cl gr_Pure (gr_W gr_Pure \<Psi>))"
proof -
  let ?H = "Conj (gr_Ind1 \<Psi>) (Conj (gr_Ind2 gr_Pure \<Psi>) (gr_Ind3 gr_Pure \<Psi>))"
  let ?W = "gr_W gr_Pure \<Psi>"
  have ht: "\<Gamma> \<turnstile> ?H : Prop" by (gr_typ pst)
  have wt: "\<Gamma> \<turnstile> ?W : gr_cls" by (gr_typ pst)
  text \<open>First condition for \<open>\<W>\<close>.\<close>
  have c1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (App ?W gr_Kbot)"
  proof -
    have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        (App ?W gr_Kbot \<longleftrightarrow>\<^sub>o Conj (gr_Stage gr_Pure gr_Kbot) (App \<Psi> gr_Kbot))"
      by (rule gr_W_app) (gr_typ pst)+
    have ty: "\<Gamma> \<turnstile> Imp ?H (App ?W gr_Kbot) : Prop" by (gr_typ pst)
    show ?thesis by (rule grk_PC2[OF a gr_Lemma4_Stage_Kbot[OF st] ty]) gr_taut
  qed
  text \<open>Second condition for \<open>\<W>\<close>.\<close>
  have c2: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H)
        (Imp (App (shift gr_Pure) (Var 0))
          (Imp (App (shift ?W) (Var 0)) (App (shift ?W) (App gr_Sigma (Var 0)))))"
  proof -
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?P = "shift \<Psi>"
    let ?Y = "Var 0"
    let ?W' = "gr_W gr_Pure ?P"
    have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?W' ?Y \<longleftrightarrow>\<^sub>o Conj (gr_Stage gr_Pure ?Y) (App ?P ?Y))"
      by (rule gr_W_app) (gr_typ pst)+
    have b: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?W' (App gr_Sigma ?Y) \<longleftrightarrow>\<^sub>o
        Conj (gr_Stage gr_Pure (App gr_Sigma ?Y)) (App ?P (App gr_Sigma ?Y)))"
      by (rule gr_W_app) (gr_typ pst)+
    have s: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Stage gr_Pure ?Y) (gr_Stage gr_Pure (App gr_Sigma ?Y))"
      by (rule gr_Lemma4_Stage_Sigma[OF st]) gr_typ
    have e: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Ind2 gr_Pure ?P)
        (Imp (Conj (gr_Stage gr_Pure ?Y) (App ?P ?Y)) (App ?P (App gr_Sigma ?Y)))"
      by (rule gr_Ind2_E) (gr_typ pst)+
    have ty: "?\<Delta> \<turnstile>
        Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
          (Imp (App gr_Pure ?Y) (Imp (App ?W' ?Y) (App ?W' (App gr_Sigma ?Y)))) : Prop"
      by (gr_typ pst)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
          (Imp (App gr_Pure ?Y) (Imp (App ?W' ?Y) (App ?W' (App gr_Sigma ?Y))))"
      by (rule grk_PC4[OF a b s e ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  text \<open>Third condition for \<open>\<W>\<close>.\<close>
  have c3: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H)
        (Imp (Conj (App (shift gr_Pure) (Var 0)) (gr_ClCov (shift gr_Pure) (shift ?W) (Var 0)))
          (App (shift ?W) (Var 0)))"
  proof -
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?P = "shift \<Psi>"
    let ?B = "Var 0"
    let ?W' = "gr_W gr_Pure ?P"
    let ?\<Delta>2 = "gr_u # Prop # ?\<Delta>"
    let ?P2 = "shift (shift ?P)"
    let ?B2 = "shift (shift ?B)"
    let ?W2 = "gr_W gr_Pure ?P2"
    text \<open>The witnesses in \<open>\<W>\<close> are stages satisfying \<open>\<Psi>\<close>.\<close>
    have w: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        (App ?W2 (Var 0) \<longleftrightarrow>\<^sub>o Conj (gr_Stage gr_Pure (Var 0)) (App ?P2 (Var 0)))"
      by (rule gr_W_app) (gr_typ pst)+
    have ty1: "?\<Delta>2 \<turnstile> Imp (gr_wit gr_Pure ?W2 ?B2 (Var (Suc 0)) (Var 0))
        (gr_swit gr_Pure ?B2 (Var (Suc 0)) (Var 0)) : Prop"
      by (gr_typ pst)
    have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit gr_Pure ?W2 ?B2 (Var (Suc 0)) (Var 0))
          (gr_swit gr_Pure ?B2 (Var (Suc 0)) (Var 0))"
      by (rule grk_PC1[OF w ty1]) gr_taut
    then have pw1: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit (shift (shift gr_Pure)) (shift (shift ?W')) ?B2 (Var (Suc 0)) (Var 0))
          (gr_swit (shift (shift gr_Pure)) ?B2 (Var (Suc 0)) (Var 0))"
      by (simp add: grs)
    have ty2: "?\<Delta>2 \<turnstile> Imp (gr_wit gr_Pure ?W2 ?B2 (Var (Suc 0)) (Var 0))
        (gr_iwit gr_Pure ?P2 ?B2 (Var (Suc 0)) (Var 0)) : Prop"
      by (gr_typ pst)
    have "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit gr_Pure ?W2 ?B2 (Var (Suc 0)) (Var 0))
          (gr_iwit gr_Pure ?P2 ?B2 (Var (Suc 0)) (Var 0))"
      by (rule grk_PC1[OF w ty2]) gr_taut
    then have pw2: "?\<Delta>2 ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_wit (shift (shift gr_Pure)) (shift (shift ?W')) ?B2 (Var (Suc 0)) (Var 0))
          (gr_iwit (shift (shift gr_Pure)) ?P2 ?B2 (Var (Suc 0)) (Var 0))"
      by (simp add: grs)
    have bt: "?\<Delta> \<turnstile> ?B : gr_u" by gr_typ
    have m1: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ClCov gr_Pure ?W' ?B) (gr_SCov gr_Pure ?B)"
      unfolding gr_ClCov_def gr_SCov_def by (rule gr_cov_mono[OF bt pw1])
    have m2: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_ClCov gr_Pure ?W' ?B) (gr_ICov gr_Pure ?P ?B)"
      unfolding gr_ClCov_def gr_ICov_def by (rule gr_cov_mono[OF bt pw2])
    text \<open>The union condition for \<open>Stage\<close> gives \<open>Stage(B)\<close>.\<close>
    have un: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (App gr_Pure ?B) (gr_SCov gr_Pure ?B)) (gr_Stage gr_Pure ?B)"
      by (rule gr_Lemma4_Stage_union[OF bt])
    text \<open>The third condition on \<open>\<Psi>\<close> gives \<open>\<Psi>(B)\<close>.\<close>
    have e: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Ind3 gr_Pure ?P)
        (Imp (Conj (App gr_Pure ?B) (gr_ICov gr_Pure ?P ?B)) (App ?P ?B))"
      by (rule gr_Ind3_E) (gr_typ pst)+
    have a: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?W' ?B \<longleftrightarrow>\<^sub>o Conj (gr_Stage gr_Pure ?B) (App ?P ?B))"
      by (rule gr_W_app) (gr_typ pst)+
    have ty: "?\<Delta> \<turnstile>
        Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
          (Imp (Conj (App gr_Pure ?B) (gr_ClCov gr_Pure ?W' ?B)) (App ?W' ?B)) : Prop"
      by (gr_typ pst)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
          (Imp (Conj (App gr_Pure ?B) (gr_ClCov gr_Pure ?W' ?B)) (App ?W' ?B))"
      by (rule grk_PC5[OF m1 m2 un e a ty]) gr_taut
    then show ?thesis by (simp add: grs)
  qed
  show ?thesis by (rule gr_Cl_I_imp[OF ht typed_pp_Pure wt c1 c2 c3])
qed

text \<open>
  "Instantiating (12) at this typed \<open>\<lambda>\<close>-term shows that every stage satisfies
  \<open>\<Psi>\<close>."  The induction principle, for an arbitrary property term \<open>\<Psi>\<close> and an
  arbitrary operator term \<open>Y\<close> in context:

     \<open>\<Psi>(K\<^sub>\<bottom>) \<rightarrow> (condition 2) \<rightarrow> (condition 3) \<rightarrow> (Stage(Y) \<rightarrow> \<Psi>(Y))\<close>.
\<close>

theorem gr_Lemma4_induction:
  assumes st: "gr_T0 \<subseteq> T" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_Ind1 \<Psi>) (Imp (gr_Ind2 gr_Pure \<Psi>) (Imp (gr_Ind3 gr_Pure \<Psi>)
      (Imp (gr_Stage gr_Pure Y) (App \<Psi> Y))))"
proof -
  let ?W = "gr_W gr_Pure \<Psi>"
  have cl: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Ind1 \<Psi>) (Conj (gr_Ind2 gr_Pure \<Psi>) (gr_Ind3 gr_Pure \<Psi>)))
        (gr_Cl gr_Pure ?W)"
    by (rule gr_Lemma4_Cl_W[OF st pst])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (Imp (gr_Cl gr_Pure ?W) (App ?W Y))"
    by (rule gr_Stage_E) (gr_typ pst yt)+
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?W Y \<longleftrightarrow>\<^sub>o Conj (gr_Stage gr_Pure Y) (App \<Psi> Y))"
    by (rule gr_W_app) (gr_typ pst yt)+
  have ty: "\<Gamma> \<turnstile> Imp (gr_Ind1 \<Psi>) (Imp (gr_Ind2 gr_Pure \<Psi>) (Imp (gr_Ind3 gr_Pure \<Psi>)
      (Imp (gr_Stage gr_Pure Y) (App \<Psi> Y)))) : Prop"
    by (gr_typ pst yt)
  show ?thesis by (rule grk_PC3[OF cl e a ty]) gr_taut
qed

text \<open>The same with the conclusion "every stage satisfies \<open>\<Psi>\<close>" quantified.\<close>

theorem gr_Lemma4_induction_forall:
  assumes st: "gr_T0 \<subseteq> T" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (gr_Ind1 \<Psi>) (Conj (gr_Ind2 gr_Pure \<Psi>) (gr_Ind3 gr_Pure \<Psi>)))
      (Forall gr_u (Imp (gr_Stage gr_Pure (Var 0)) (App (shift \<Psi>) (Var 0))))"
proof (rule grk_gen_imp)
  let ?H = "Conj (gr_Ind1 \<Psi>) (Conj (gr_Ind2 gr_Pure \<Psi>) (gr_Ind3 gr_Pure \<Psi>))"
  show "\<Gamma> \<turnstile> ?H : Prop" by (gr_typ pst)
  let ?P = "shift \<Psi>"
  have i: "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Ind1 ?P) (Imp (gr_Ind2 gr_Pure ?P) (Imp (gr_Ind3 gr_Pure ?P)
        (Imp (gr_Stage gr_Pure (Var 0)) (App ?P (Var 0)))))"
    by (rule gr_Lemma4_induction[OF st]) (gr_typ pst)+
  have ty: "gr_u # \<Gamma> \<turnstile>
      Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
        (Imp (gr_Stage gr_Pure (Var 0)) (App ?P (Var 0))) : Prop"
    by (gr_typ pst)
  have "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (gr_Ind1 ?P) (Conj (gr_Ind2 gr_Pure ?P) (gr_Ind3 gr_Pure ?P)))
        (Imp (gr_Stage gr_Pure (Var 0)) (App ?P (Var 0)))"
    by (rule grk_PC1[OF i ty]) gr_taut
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Imp (gr_Stage gr_Pure (Var 0)) (App (shift \<Psi>) (Var 0)))"
    by (simp add: grs)
qed

text \<open>Rule form, convenient when the three conditions are theorems.\<close>

lemma gr_Lemma4_induct_rule:
  assumes st: "gr_T0 \<subseteq> T" and pst: "\<Gamma> \<turnstile> \<Psi> : gr_cls" and yt: "\<Gamma> \<turnstile> Y : gr_u"
    and i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind1 \<Psi>"
    and i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind2 gr_Pure \<Psi>"
    and i3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Ind3 gr_Pure \<Psi>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y) (App \<Psi> Y)"
  by (rule grk_MP[OF i3 grk_MP[OF i2 grk_MP[OF i1 gr_Lemma4_induction[OF st pst yt]]]])

end
