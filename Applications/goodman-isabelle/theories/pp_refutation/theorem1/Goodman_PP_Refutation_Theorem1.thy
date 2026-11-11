theory Goodman_PP_Refutation_Theorem1
  imports Goodman_PP_Refutation_Objects_Theorem1
begin

text \<open>
  THEOREM 1 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "The theory \<open>\<T>\<close> proves that no proposition \<open>r\<close> satisfies
       (R)  \<open>\<forall>X\<^sup>u(Pure(X) \<rightarrow> (\<box>(Xr) \<rightarrow> \<forall>p Xp))\<close>.
     Hence \<open>\<T> \<turnstile> \<not>\<exists>r fun'(r)\<close>, and
       \<open>\<T>\<close> + unary Recombination \<open>\<turnstile> \<not>\<exists>r Fun(r)\<close>."

  Stock: \<open>\<T>\<close> (hypothesis \<open>gr_Th \<subseteq> T\<close>); for the last consequence also
  \<open>pp_unary_recombination \<in> T\<close>.  Throughout, \<open>q\<close> is \<open>gr_q r\<close>.  (R) is a
  temporary hypothesis: every statement below carries it as the antecedent of
  an implication, and Necessitation is never applied to anything depending on
  it (boxes are obtained only from hypothesis-free equivalences).
\<close>

section \<open>Purity of \<open>X\<^sub>+\<close> and \<open>X\<^sub>-\<close>\<close>

text \<open>
  "Its purity follows from the Purity schema and Application closure, using
  the closed logical term \<open>D\<^sub>+\<close> applied to the pure \<open>Y\<^sub>0\<close>."
\<close>

theorem gr_Theorem1_Pure_Xplus:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure Y0) (App gr_Pure (gr_Xplus Y0))"
proof -
  let ?DY = "App gr_Dplus Y0"
  have dyt: "\<Gamma> \<turnstile> ?DY : gr_u" by (rule has_type.App[OF typed_gr_Dplus yt])
  have pd: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Dplus"
    by (rule gr_T0_purity[OF st typed_gr_Dplus gr_Dplus_consts typed_gr_Dplus])
  have ac: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Dplus) (pp_pure gr_u Y0)) (pp_pure gr_u ?DY)"
    by (rule gr_T0_application[OF st typed_gr_Dplus yt])
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u ?DY (gr_Xplus Y0))
      (Imp (App gr_Pure ?DY) (App gr_Pure (gr_Xplus Y0)))"
    by (rule grk_LL[OF dyt typed_gr_Xplus[OF yt] typed_pp_Pure])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq gr_u ?DY (gr_Xplus Y0)" by (rule gr_Dplus_app_eq[OF yt])
  have ty: "\<Gamma> \<turnstile> Imp (App gr_Pure Y0) (App gr_Pure (gr_Xplus Y0)) : Prop" by (gr_typ yt)
  show ?thesis by (rule grk_PC4[OF pd ac ll e ty]) gr_taut
qed

text \<open>
  "This is pure by logical purity of the corresponding term \<open>D\<^sub>-\<close> and
  Application closure."
\<close>

theorem gr_Theorem1_Pure_Xminus:
  assumes st: "gr_T0 \<subseteq> T" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure Y0) (App gr_Pure (gr_Xminus Y0))"
proof -
  let ?DY = "App gr_Dminus Y0"
  have dyt: "\<Gamma> \<turnstile> ?DY : gr_u" by (rule has_type.App[OF typed_gr_Dminus yt])
  have pd: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Dminus"
    by (rule gr_T0_purity[OF st typed_gr_Dminus gr_Dminus_consts typed_gr_Dminus])
  have ac: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_pure (gr_u \<rightarrow>\<^sub>o gr_u) gr_Dminus) (pp_pure gr_u Y0)) (pp_pure gr_u ?DY)"
    by (rule gr_T0_application[OF st typed_gr_Dminus yt])
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u ?DY (gr_Xminus Y0))
      (Imp (App gr_Pure ?DY) (App gr_Pure (gr_Xminus Y0)))"
    by (rule grk_LL[OF dyt typed_gr_Xminus[OF yt] typed_pp_Pure])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq gr_u ?DY (gr_Xminus Y0)" by (rule gr_Dminus_app_eq[OF yt])
  have ty: "\<Gamma> \<turnstile> Imp (App gr_Pure Y0) (App gr_Pure (gr_Xminus Y0)) : Prop" by (gr_typ yt)
  show ?thesis by (rule grk_PC4[OF pd ac ll e ty]) gr_taut
qed

section \<open>The values of \<open>X\<^sub>+\<close>, \<open>X\<^sub>-\<close> at \<open>r\<close> and at \<open>\<not>q\<close>\<close>

text \<open>
  "The identity \<open>gr = q\<close> identifies \<open>X\<^sub>+r\<close> with the entire disjunction in the
  box":  \<open>X\<^sub>+r \<leftrightarrow> (q \<or> Y\<^sub>0q \<or> Y\<^sub>0(\<not>q))\<close>.  These equivalences are hypothesis-free
  theorems, so they may be necessitated.
\<close>

lemma gr_Theorem1_Xplus_r:
  assumes rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xplus Y0) r \<longleftrightarrow>\<^sub>o gr_sgA Y0 (gr_q r))"
proof -
  let ?q = "gr_q r"
  let ?g = "App gr_g r"
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xplus Y0) r \<longleftrightarrow>\<^sub>o gr_XplusB Y0 r)"
    by (rule gr_Xplus_app[OF yt rt])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?g ?q" by (rule gr_Lemma3_g_r[OF rt])
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?g \<longleftrightarrow>\<^sub>o ?q)" by (rule grk_eq_iff_rule[OF e])
  have e2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 ?g \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule grk_eq_app_iff_rule[OF yt e])
  have e3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?g) \<longleftrightarrow>\<^sub>o App Y0 (Neg ?q))"
    by (rule grk_eq_app_iff_rule[OF yt grk_eq_neg_rule[OF e]])
  have ty: "\<Gamma> \<turnstile> (App (gr_Xplus Y0) r \<longleftrightarrow>\<^sub>o gr_sgA Y0 ?q) : Prop" by (gr_typ rt yt)
  show ?thesis by (rule grk_PC4[OF b e1 e2 e3 ty]) gr_taut
qed

lemma gr_Theorem1_Xminus_r:
  assumes rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xminus Y0) r \<longleftrightarrow>\<^sub>o gr_sgB Y0 (gr_q r))"
proof -
  let ?q = "gr_q r"
  let ?g = "App gr_g r"
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xminus Y0) r \<longleftrightarrow>\<^sub>o gr_XminusB Y0 r)"
    by (rule gr_Xminus_app[OF yt rt])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?g ?q" by (rule gr_Lemma3_g_r[OF rt])
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?g \<longleftrightarrow>\<^sub>o ?q)" by (rule grk_eq_iff_rule[OF e])
  have e2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 ?g \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule grk_eq_app_iff_rule[OF yt e])
  have e3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?g) \<longleftrightarrow>\<^sub>o App Y0 (Neg ?q))"
    by (rule grk_eq_app_iff_rule[OF yt grk_eq_neg_rule[OF e]])
  have ty: "\<Gamma> \<turnstile> (App (gr_Xminus Y0) r \<longleftrightarrow>\<^sub>o gr_sgB Y0 ?q) : Prop" by (gr_typ rt yt)
  show ?thesis by (rule grk_PC4[OF b e1 e2 e3 ty]) gr_taut
qed

text \<open>
  "Using \<open>g(\<not>q) = \<not>q\<close> and double negation, we obtain \<open>\<not>q \<or> Y\<^sub>0(\<not>q) \<or> Y\<^sub>0q\<close>."
\<close>

lemma gr_Theorem1_Xplus_nq:
  assumes rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App (gr_Xplus Y0) (Neg (gr_q r)) \<longleftrightarrow>\<^sub>o
      Disj (Neg (gr_q r)) (Disj (App Y0 (Neg (gr_q r))) (App Y0 (gr_q r))))"
proof -
  let ?q = "gr_q r"
  let ?nq = "Neg ?q"
  let ?g = "App gr_g ?nq"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  have nqt: "\<Gamma> \<turnstile> ?nq : Prop" by (gr_typ rt)
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xplus Y0) ?nq \<longleftrightarrow>\<^sub>o gr_XplusB Y0 ?nq)"
    by (rule gr_Xplus_app[OF yt nqt])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?g ?nq" by (rule gr_Lemma3_g_neg_q[OF rt])
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?g \<longleftrightarrow>\<^sub>o ?nq)" by (rule grk_eq_iff_rule[OF e])
  have e2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 ?g \<longleftrightarrow>\<^sub>o App Y0 ?nq)"
    by (rule grk_eq_app_iff_rule[OF yt e])
  have e3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?g) \<longleftrightarrow>\<^sub>o App Y0 (Neg ?nq))"
    by (rule grk_eq_app_iff_rule[OF yt grk_eq_neg_rule[OF e]])
  text \<open>Double negation.\<close>
  have e4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?nq) \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule grk_eq_app_iff_rule[OF yt grk_DN[OF qt]])
  have ty: "\<Gamma> \<turnstile> (App (gr_Xplus Y0) ?nq \<longleftrightarrow>\<^sub>o
      Disj ?nq (Disj (App Y0 ?nq) (App Y0 ?q))) : Prop"
    by (gr_typ rt yt)
  show ?thesis by (rule grk_PC5[OF b e1 e2 e3 e4 ty]) gr_taut
qed

text \<open>
  "Using \<open>g(\<not>q) = \<not>q\<close> and double negation, we obtain \<open>q \<or> Y\<^sub>0(\<not>q) \<or> Y\<^sub>0q\<close>."
\<close>

lemma gr_Theorem1_Xminus_nq:
  assumes rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App (gr_Xminus Y0) (Neg (gr_q r)) \<longleftrightarrow>\<^sub>o
      Disj (gr_q r) (Disj (App Y0 (Neg (gr_q r))) (App Y0 (gr_q r))))"
proof -
  let ?q = "gr_q r"
  let ?nq = "Neg ?q"
  let ?g = "App gr_g ?nq"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  have nqt: "\<Gamma> \<turnstile> ?nq : Prop" by (gr_typ rt)
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (gr_Xminus Y0) ?nq \<longleftrightarrow>\<^sub>o gr_XminusB Y0 ?nq)"
    by (rule gr_Xminus_app[OF yt nqt])
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?g ?nq" by (rule gr_Lemma3_g_neg_q[OF rt])
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?g \<longleftrightarrow>\<^sub>o ?nq)" by (rule grk_eq_iff_rule[OF e])
  have e2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 ?g \<longleftrightarrow>\<^sub>o App Y0 ?nq)"
    by (rule grk_eq_app_iff_rule[OF yt e])
  have e3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?g) \<longleftrightarrow>\<^sub>o App Y0 (Neg ?nq))"
    by (rule grk_eq_app_iff_rule[OF yt grk_eq_neg_rule[OF e]])
  have e4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App Y0 (Neg ?nq) \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule grk_eq_app_iff_rule[OF yt grk_DN[OF qt]])
  have ty: "\<Gamma> \<turnstile> (App (gr_Xminus Y0) ?nq \<longleftrightarrow>\<^sub>o
      Disj ?q (Disj (App Y0 ?nq) (App Y0 ?q))) : Prop"
    by (gr_typ rt yt)
  show ?thesis by (rule grk_PC5[OF b e1 e2 e3 e4 ty]) gr_taut
qed

section \<open>The two cases\<close>

text \<open>
  "Case 1.  Suppose that \<open>\<box>(q \<or> Y\<^sub>0q \<or> Y\<^sub>0(\<not>q))\<close>.  Factivity gives the
  disjunction inside the box.  Since its last two disjuncts are false, \<open>q\<close>
  holds. ... The identity \<open>gr = q\<close> identifies \<open>X\<^sub>+r\<close> with the entire disjunction
  in the box, giving \<open>\<box>(X\<^sub>+r)\<close>.  Condition (R) yields \<open>\<forall>p X\<^sub>+p\<close>, whose instance
  at \<open>\<not>q\<close> is \<open>X\<^sub>+(\<not>q)\<close>. ... we obtain \<open>\<not>q \<or> Y\<^sub>0(\<not>q) \<or> Y\<^sub>0q\<close>.  Each disjunct is
  false, which is a contradiction."

  Here \<open>Y\<^sub>0\<close> is a stage ("It is pure and symmetric, so \<open>\<not>Y\<^sub>0(\<not>q)\<close> also holds")
  with \<open>\<not>Y\<^sub>0q\<close>.
\<close>

theorem gr_Theorem1_case1:
  assumes st: "gr_T0 \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0) (Imp (Neg (App Y0 (gr_q r)))
      (Imp (\<box>\<^sub>o (gr_sgA Y0 (gr_q r))) ObjFalse)))"
proof -
  let ?q = "gr_q r"
  let ?X = "gr_Xplus Y0"
  let ?val = "Disj (Neg ?q) (Disj (App Y0 (Neg ?q)) (App Y0 ?q))"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  have nqt: "\<Gamma> \<turnstile> Neg ?q : Prop" by (gr_typ rt)
  have xt: "\<Gamma> \<turnstile> ?X : gr_u" by (gr_typ yt)
  text \<open>\<open>Y\<^sub>0\<close> is pure and symmetric.\<close>
  have sp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y0) (App gr_Pure Y0)"
    by (rule gr_Stage_pure) (gr_typ yt)+
  have sy: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y0) (App Y0 (Neg ?q) \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule gr_Lemma5_14_at[OF st yt qt])
  text \<open>Factivity.\<close>
  have fa: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sgA Y0 ?q)) (gr_sgA Y0 ?q)"
    by (rule grk_T) (gr_typ rt yt)
  text \<open>\<open>X\<^sub>+\<close> is pure.\<close>
  have px: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure Y0) (App gr_Pure ?X)"
    by (rule gr_Theorem1_Pure_Xplus[OF st yt])
  text \<open>\<open>gr = q\<close> gives \<open>\<box>(X\<^sub>+r)\<close> from the boxed disjunction.\<close>
  have bx: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o (App ?X r) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (gr_sgA Y0 ?q))"
    by (rule grk_box_iff[OF gr_Theorem1_Xplus_r[OF rt yt]])
  text \<open>Condition (R) yields \<open>\<forall>p X\<^sub>+p\<close>, whose instance at \<open>\<not>q\<close> is \<open>X\<^sub>+(\<not>q)\<close>.\<close>
  have re: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_R gr_Pure r) (Imp (App gr_Pure ?X) (Imp (\<box>\<^sub>o (App ?X r)) (gr_AllP ?X)))"
    by (rule gr_R_E) (gr_typ rt yt)+
  have ae: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_AllP ?X) (App ?X (Neg ?q))"
    by (rule gr_AllP_E[OF xt nqt])
  have ty1: "\<Gamma> \<turnstile> Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0)
      (Imp (\<box>\<^sub>o (gr_sgA Y0 ?q)) (App ?X (Neg ?q)))) : Prop"
    by (gr_typ rt yt)
  have inst: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0)
      (Imp (\<box>\<^sub>o (gr_sgA Y0 ?q)) (App ?X (Neg ?q))))"
    by (rule grk_PC5[OF sp px bx re ae ty1]) gr_taut
  text \<open>Its value: \<open>\<not>q \<or> Y\<^sub>0(\<not>q) \<or> Y\<^sub>0q\<close>.  Each disjunct is false.\<close>
  have xv: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?X (Neg ?q) \<longleftrightarrow>\<^sub>o ?val)"
    by (rule gr_Theorem1_Xplus_nq[OF rt yt])
  have ty: "\<Gamma> \<turnstile> Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0) (Imp (Neg (App Y0 ?q))
      (Imp (\<box>\<^sub>o (gr_sgA Y0 ?q)) ObjFalse))) : Prop"
    by (gr_typ rt yt)
  show ?thesis by (rule grk_PC4[OF inst xv fa sy ty]) gr_taut
qed

text \<open>
  "Case 2.  Suppose that \<open>\<box>(\<not>q \<or> Y\<^sub>0q \<or> Y\<^sub>0(\<not>q))\<close>.  Factivity and the same two
  local falsities give \<open>\<not>q\<close>. ... Again \<open>gr = q\<close> gives \<open>\<box>(X\<^sub>-r)\<close>.  Condition (R)
  yields \<open>\<forall>p X\<^sub>-p\<close>, and therefore \<open>X\<^sub>-(\<not>q)\<close>. ... we obtain
  \<open>q \<or> Y\<^sub>0(\<not>q) \<or> Y\<^sub>0q\<close>.  All three disjuncts are false."
\<close>

theorem gr_Theorem1_case2:
  assumes st: "gr_T0 \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0) (Imp (Neg (App Y0 (gr_q r)))
      (Imp (\<box>\<^sub>o (gr_sgB Y0 (gr_q r))) ObjFalse)))"
proof -
  let ?q = "gr_q r"
  let ?X = "gr_Xminus Y0"
  let ?val = "Disj ?q (Disj (App Y0 (Neg ?q)) (App Y0 ?q))"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  have nqt: "\<Gamma> \<turnstile> Neg ?q : Prop" by (gr_typ rt)
  have xt: "\<Gamma> \<turnstile> ?X : gr_u" by (gr_typ yt)
  have sp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y0) (App gr_Pure Y0)"
    by (rule gr_Stage_pure) (gr_typ yt)+
  have sy: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Stage gr_Pure Y0) (App Y0 (Neg ?q) \<longleftrightarrow>\<^sub>o App Y0 ?q)"
    by (rule gr_Lemma5_14_at[OF st yt qt])
  have fa: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sgB Y0 ?q)) (gr_sgB Y0 ?q)"
    by (rule grk_T) (gr_typ rt yt)
  have px: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_Pure Y0) (App gr_Pure ?X)"
    by (rule gr_Theorem1_Pure_Xminus[OF st yt])
  have bx: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o (App ?X r) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (gr_sgB Y0 ?q))"
    by (rule grk_box_iff[OF gr_Theorem1_Xminus_r[OF rt yt]])
  have re: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_R gr_Pure r) (Imp (App gr_Pure ?X) (Imp (\<box>\<^sub>o (App ?X r)) (gr_AllP ?X)))"
    by (rule gr_R_E) (gr_typ rt yt)+
  have ae: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_AllP ?X) (App ?X (Neg ?q))"
    by (rule gr_AllP_E[OF xt nqt])
  have ty1: "\<Gamma> \<turnstile> Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0)
      (Imp (\<box>\<^sub>o (gr_sgB Y0 ?q)) (App ?X (Neg ?q)))) : Prop"
    by (gr_typ rt yt)
  have inst: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0)
      (Imp (\<box>\<^sub>o (gr_sgB Y0 ?q)) (App ?X (Neg ?q))))"
    by (rule grk_PC5[OF sp px bx re ae ty1]) gr_taut
  have xv: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?X (Neg ?q) \<longleftrightarrow>\<^sub>o ?val)"
    by (rule gr_Theorem1_Xminus_nq[OF rt yt])
  have ty: "\<Gamma> \<turnstile> Imp (gr_R gr_Pure r) (Imp (gr_Stage gr_Pure Y0) (Imp (Neg (App Y0 ?q))
      (Imp (\<box>\<^sub>o (gr_sgB Y0 ?q)) ObjFalse))) : Prop"
    by (gr_typ rt yt)
  show ?thesis by (rule grk_PC4[OF inst xv fa sy ty]) gr_taut
qed

text \<open>"We consider the two disjuncts of \<open>(\<Sigma>Y\<^sub>0)q\<close>."  Both lead to a contradiction.\<close>

theorem gr_Theorem1_cases:
  assumes st: "gr_T0 \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop" and yt: "\<Gamma> \<turnstile> Y0 : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (gr_R gr_Pure r)
      (Imp (Conj (gr_Stage gr_Pure Y0)
          (Conj (Neg (App Y0 (gr_q r))) (App (App gr_Sigma Y0) (gr_q r))))
        ObjFalse)"
proof -
  let ?q = "gr_q r"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  have sa: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (App gr_Sigma Y0) ?q \<longleftrightarrow>\<^sub>o gr_sg Y0 ?q)"
    by (rule gr_Sigma_app[OF yt qt])
  have ty: "\<Gamma> \<turnstile> Imp (gr_R gr_Pure r)
      (Imp (Conj (gr_Stage gr_Pure Y0)
          (Conj (Neg (App Y0 ?q)) (App (App gr_Sigma Y0) ?q))) ObjFalse) : Prop"
    by (gr_typ rt yt)
  show ?thesis
    by (rule grk_PC3[OF gr_Theorem1_case1[OF st rt yt] gr_Theorem1_case2[OF st rt yt] sa ty])
      gr_taut
qed

section \<open>No proposition satisfies (R)\<close>

text \<open>
  "Suppose that \<open>r\<close> satisfies (R).  Put \<open>q = r & Lr = gr\<close>.  By Lemmas 3 and 6,
  \<open>Pq\<close>.  Choose a stage containing \<open>q\<close>.  Lemma 5 gives a stage \<open>Y\<^sub>0\<close> with
  \<open>\<not>Y\<^sub>0q\<close>, \<open>(\<Sigma>Y\<^sub>0)q\<close>. ... This completes the contradiction in both cases, and
  proves that no \<open>r\<close> satisfies (R)."
\<close>

text \<open>There is a stage \<open>Y\<^sub>0\<close> with \<open>\<not>Y\<^sub>0q\<close> and \<open>(\<Sigma>Y\<^sub>0)q\<close> (no hypothesis on \<open>r\<close>).\<close>

lemma gr_Theorem1_predecessor_of_q:
  assumes st: "gr_Th \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_PredEx gr_Pure (gr_q r)"
proof -
  let ?q = "gr_q r"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  text \<open>By Lemmas 3 and 6, \<open>Pq\<close>.\<close>
  have pq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_P ?q"
    by (rule grk_MP[OF gr_Lemma3_Lq[OF rt] gr_Lemma6_L_in_P[OF st qt]])
  have pb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Pbody gr_Pure ?q"
    by (rule grk_iff_mp[OF gr_P_app[OF qt] pq])
  text \<open>Choose a stage containing \<open>q\<close>; Lemma 5 (15) gives \<open>Y\<^sub>0\<close>.\<close>
  have ex: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pbody gr_Pure ?q) (gr_PredEx gr_Pure ?q)"
  proof (rule gr_Pbody_E)
    show "\<Gamma> \<turnstile> gr_PredEx gr_Pure ?q : Prop" by (gr_typ rt)
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?Y = "Var 0"
    let ?q' = "shift ?q"
    have c: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (gr_Stage gr_Pure ?Y) (Imp (App ?Y ?q') (gr_PredEx gr_Pure ?q'))"
      by (rule gr_Lemma5_15[OF gr_Th_T0[OF st]]) (gr_typ rt)+
    have ty: "?\<Delta> \<turnstile> Imp (Conj (gr_Stage gr_Pure ?Y) (App ?Y ?q'))
        (gr_PredEx gr_Pure ?q') : Prop"
      by (gr_typ rt)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (gr_Stage gr_Pure ?Y) (App ?Y ?q')) (gr_PredEx gr_Pure ?q')"
      by (rule grk_PC1[OF c ty]) gr_taut
    then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (gr_Stage (shift gr_Pure) (Var 0)) (App (Var 0) (shift ?q)))
          (shift (gr_PredEx gr_Pure ?q))"
      by (simp add: grs)
  qed
  show ?thesis by (rule grk_MP[OF pb ex])
qed

text \<open>Open form: for every proposition \<open>r\<close>, \<open>\<T> \<turnstile> \<not>(R)\<close>.\<close>

theorem gr_Theorem1_R_at:
  assumes st: "gr_Th \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (gr_R gr_Pure r)"
proof -
  let ?q = "gr_q r"
  let ?Q = "Imp (gr_R gr_Pure r) ObjFalse"
  have el: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_PredEx gr_Pure ?q) ?Q"
  proof (rule gr_PredEx_E)
    show "\<Gamma> \<turnstile> ?Q : Prop" by (gr_typ rt)
    let ?\<Delta> = "gr_u # \<Gamma>"
    let ?r = "shift r"
    let ?Y = "Var 0"
    let ?w = "Conj (gr_Stage gr_Pure ?Y)
        (Conj (Neg (App ?Y (gr_q ?r))) (App (App gr_Sigma ?Y) (gr_q ?r)))"
    have c: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_R gr_Pure ?r) (Imp ?w ObjFalse)"
      by (rule gr_Theorem1_cases[OF gr_Th_T0[OF st]]) (gr_typ rt)+
    have ty: "?\<Delta> \<turnstile> Imp ?w (Imp (gr_R gr_Pure ?r) ObjFalse) : Prop" by (gr_typ rt)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?w (Imp (gr_R gr_Pure ?r) ObjFalse)"
      by (rule grk_PC1[OF c ty]) gr_taut
    then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Conj (gr_Stage (shift gr_Pure) (Var 0))
            (Conj (Neg (App (Var 0) (shift ?q))) (App (App gr_Sigma (Var 0)) (shift ?q))))
          (shift ?Q)"
      by (simp add: grs)
  qed
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    by (rule grk_MP[OF gr_Theorem1_predecessor_of_q[OF st rt] el])
  then show ?thesis by (rule grk_neg_I)
qed

text \<open>
  THEOREM 1, first assertion, as the closed sentence \<open>\<not>\<exists>r.(R)\<close>:
  "The theory \<open>\<T>\<close> proves that no proposition \<open>r\<close> satisfies (R)."
\<close>

theorem gr_Theorem1_R:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Exists Prop (gr_R gr_Pure (Var 0)))"
  by (rule grk_not_exists, rule gr_Theorem1_R_at[OF st]) gr_typ

section \<open>First consequence: no fun' proposition\<close>

text \<open>
  "For the first consequence suppose that \<open>fun'(r)\<close> and that \<open>X\<close> is pure with
  \<open>\<box>(Xr)\<close>.  The operator \<open>K\<^sub>\<top> = \<lambda>p.\<top>\<close> is pure by the Purity schema.  Since
  \<open>Xr = \<top> = K\<^sub>\<top>r\<close>, the definition of \<open>fun'(r)\<close> yields \<open>X = K\<^sub>\<top>\<close>.  It follows
  that \<open>Xp = \<top>\<close>, hence \<open>Xp\<close>, for every \<open>p\<close>."
\<close>

lemma gr_Theorem1_funp_step:
  assumes st: "gr_T0 \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop" and xt: "\<Gamma> \<turnstile> X : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Imp (App gr_Pure X) (Imp (\<box>\<^sub>o (App X r)) (gr_AllP X)))"
proof -
  let ?Xr = "App X r"
  let ?Kr = "App gr_Ktop r"
  let ?E = "Eq gr_u X gr_Ktop"
  have ft: "\<Gamma> \<turnstile> pp_fun_prime r : Prop" by (rule typed_pp_fun_prime[OF rt])
  text \<open>The definition of \<open>fun'(r)\<close>, at \<open>X\<close> and \<open>K\<^sub>\<top>\<close>.\<close>
  have fi: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime r) (Imp (pp_pure gr_u X) (Imp (pp_pure gr_u gr_Ktop)
        (Imp (Eq Prop ?Xr ?Kr) ?E)))"
    by (rule gr_fun_prime_inst[OF rt xt typed_gr_Ktop])
  text \<open>\<open>K\<^sub>\<top>\<close> is pure by the Purity schema.\<close>
  have pk: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure gr_u gr_Ktop"
    by (rule gr_T0_purity[OF st typed_gr_Ktop gr_Ktop_consts typed_gr_Ktop])
  text \<open>\<open>Xr = \<top> = K\<^sub>\<top>r\<close>.\<close>
  have kr: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ObjTrue ?Kr"
    by (rule grk_eq_sym_rule[OF gr_Ktop_app_eq[OF rt]])
  have tr: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop ?Xr ObjTrue) (Imp (Eq Prop ObjTrue ?Kr) (Eq Prop ?Xr ?Kr))"
    by (rule grk_eq_trans) (gr_typ rt xt)+
  text \<open>From \<open>X = K\<^sub>\<top>\<close>: \<open>Xp = \<top>\<close>, hence \<open>Xp\<close>, for every \<open>p\<close>.\<close>
  have all: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E (gr_AllP X)"
  proof (rule gr_AllP_I_imp)
    show "\<Gamma> \<turnstile> ?E : Prop" by (gr_typ xt)
    let ?\<Delta> = "Prop # \<Gamma>"
    let ?X = "shift X"
    have b: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u ?X gr_Ktop) (\<box>\<^sub>o (App ?X (Var 0)))"
      by (rule gr_Ktop_eq_box) (gr_typ xt)+
    have t: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (App ?X (Var 0))) (App ?X (Var 0))"
      by (rule grk_T) (gr_typ xt)
    have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq gr_u ?X gr_Ktop) (App ?X (Var 0))"
      by (rule grk_imp_trans[OF b t])
    then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?E) (App (shift X) (Var 0))"
      by (simp add: grs)
  qed
  have ty: "\<Gamma> \<turnstile> Imp (pp_fun_prime r)
      (Imp (App gr_Pure X) (Imp (Eq Prop ?Xr ObjTrue) (gr_AllP X))) : Prop"
    by (gr_typ ft rt xt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r)
      (Imp (App gr_Pure X) (Imp (Eq Prop ?Xr ObjTrue) (gr_AllP X)))"
    by (rule grk_PC5[OF fi pk kr tr all ty]) gr_taut
  then show ?thesis by (simp only: ObjBox_def)
qed

text \<open>"Thus \<open>r\<close> satisfies (R), contradicting the result just proved."\<close>

theorem gr_Theorem1_funp_R:
  assumes st: "gr_T0 \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r) (gr_R gr_Pure r)"
proof (rule gr_R_I_imp)
  show "\<Gamma> \<turnstile> pp_fun_prime r : Prop" by (rule typed_pp_fun_prime[OF rt])
  have "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime (shift r))
        (Imp (App gr_Pure (Var 0)) (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0))))"
    by (rule gr_Theorem1_funp_step[OF st]) (gr_typ rt)+
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (pp_fun_prime r))
        (Imp (App (shift gr_Pure) (Var 0))
          (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0))))"
    by (simp add: grs)
qed

theorem gr_Theorem1_funp_at:
  assumes st: "gr_Th \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_fun_prime r)"
proof -
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r) (gr_R gr_Pure r)"
    by (rule gr_Theorem1_funp_R[OF gr_Th_T0[OF st] rt])
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (gr_R gr_Pure r)" by (rule gr_Theorem1_R_at[OF st rt])
  have ty: "\<Gamma> \<turnstile> Neg (pp_fun_prime r) : Prop"
    by (gr_typ typed_pp_fun_prime[OF rt])
  show ?thesis by (rule grk_PC2[OF a b ty]) gr_taut
qed

text \<open>
  THEOREM 1, second assertion: \<open>\<T> \<turnstile> \<not>\<exists>r fun'(r)\<close>.  The sentence
  \<open>\<exists>r fun'(r)\<close> is the development's \<open>pp_exists_fun_prime\<close>.
\<close>

theorem gr_Theorem1_funp:
  assumes st: "gr_Th \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg pp_exists_fun_prime"
  unfolding pp_exists_fun_prime_def
  by (rule grk_not_exists, rule gr_Theorem1_funp_at[OF st]) gr_typ

section \<open>Second consequence: no fundamental proposition\<close>

text \<open>
  "Finally, unary Recombination states
     \<open>\<forall>X r((Pure(X) & Fun(r)) \<rightarrow> (\<box>(Xr) \<rightarrow> \<forall>p Xp))\<close>.
   Every fundamental proposition would therefore satisfy (R)."
\<close>

theorem gr_Theorem1_Fun_R:
  assumes ur: "pp_unary_recombination \<in> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun Prop r) (gr_R gr_Pure r)"
proof (rule gr_R_I_imp)
  show "\<Gamma> \<turnstile> pp_fun Prop r : Prop" by (rule typed_pp_fun[OF rt])
  let ?\<Delta> = "gr_u # \<Gamma>"
  let ?r = "shift r"
  let ?X = "Var 0"
  have i: "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_pure gr_u ?X) (pp_fun Prop ?r)) (Imp (\<box>\<^sub>o (App ?X ?r)) (gr_AllP ?X))"
    by (rule gr_unary_recombination_inst[OF ur]) (gr_typ rt)+
  have ty: "?\<Delta> \<turnstile> Imp (pp_fun Prop ?r)
      (Imp (App gr_Pure ?X) (Imp (\<box>\<^sub>o (App ?X ?r)) (gr_AllP ?X))) : Prop"
    by (gr_typ rt typed_pp_fun)
  have "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun Prop ?r)
      (Imp (App gr_Pure ?X) (Imp (\<box>\<^sub>o (App ?X ?r)) (gr_AllP ?X)))"
    by (rule grk_PC1[OF i ty]) gr_taut
  then show "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (pp_fun Prop r))
        (Imp (App (shift gr_Pure) (Var 0))
          (Imp (\<box>\<^sub>o (App (Var 0) (shift r))) (gr_AllP (Var 0))))"
    by (simp add: grs gr_pp_fun_shift)
qed

theorem gr_Theorem1_Fun_at:
  assumes st: "gr_Th \<subseteq> T" and ur: "pp_unary_recombination \<in> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_fun Prop r)"
proof -
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun Prop r) (gr_R gr_Pure r)"
    by (rule gr_Theorem1_Fun_R[OF ur rt])
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (gr_R gr_Pure r)" by (rule gr_Theorem1_R_at[OF st rt])
  have ty: "\<Gamma> \<turnstile> Neg (pp_fun Prop r) : Prop" by (gr_typ typed_pp_fun[OF rt])
  show ?thesis by (rule grk_PC2[OF a b ty]) gr_taut
qed

text \<open>
  THEOREM 1, third assertion: \<open>\<T>\<close> + unary Recombination \<open>\<turnstile> \<not>\<exists>r Fun(r)\<close>.
\<close>

theorem gr_Theorem1_Fun:
  assumes st: "gr_Th \<subseteq> T" and ur: "pp_unary_recombination \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Exists Prop (pp_fun Prop (Var 0)))"
  by (rule grk_not_exists, rule gr_Theorem1_Fun_at[OF st ur]) gr_typ

end
