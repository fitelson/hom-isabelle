theory Goodman_PP_Refutation_Lemma3
  imports Goodman_PP_Refutation_Lemma2
begin

text \<open>
  LEMMA 3 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "Put \<open>g = \<lambda>p.(p & Lp)\<close>.  For each proposition \<open>r\<close>, put \<open>q = gr\<close>.
     Then logic proves \<open>Lq\<close> and \<open>g(\<not>q) = \<not>q\<close>."

  In Isabelle \<open>q\<close> is \<open>gr_q r\<close>, i.e. \<open>r & Lr\<close>, the beta-normal form of
  \<open>g r\<close> (the note itself writes \<open>q = r & Lr = gr\<close>); the identity \<open>g r = q\<close>
  is \<open>gr_Lemma3_g_r\<close>.  Every theorem holds for every stock \<open>T\<close>.
\<close>

text \<open>"The identities \<open>gr = q\<close> and \<open>g(\<not>q) = \<not>q\<close> ...":  \<open>g r = q\<close>, by beta.\<close>

theorem gr_Lemma3_g_r:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_g r) (gr_q r)"
  by (rule grk_iff_eq[OF gr_g_app[OF rt]])

section \<open>\<open>q \<rightarrow> Lq\<close> and its universal closure\<close>

text \<open>
  "Conjoining \<open>Lr\<close> to \<open>r\<close> gives a proposition \<open>q\<close> for which we can first
  prove \<open>q \<rightarrow> Lq\<close>.  Assume \<open>q\<close>, so \<open>Lr\<close>.  By (9), \<open>\<box>(Lr)\<close>, which by
  definition is \<open>Lr = \<top>\<close>.  Hence \<open>q = r & Lr = r & \<top> = r\<close>.  Substitution
  in \<open>Lr\<close> gives \<open>Lq\<close>."
\<close>

lemma gr_Lemma3_q_imp_Lq:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_q r) (App gr_L (gr_q r))"
proof -
  let ?Lr = "App gr_L r"
  let ?q = "Conj r ?Lr"
  let ?rT = "Conj r ObjTrue"
  have lrt: "\<Gamma> \<turnstile> ?Lr : Prop" by (gr_typ rt)
  text \<open>Assume \<open>q\<close>, so \<open>Lr\<close>.\<close>
  have s1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?q ?Lr"
    by (rule grk_taut) (gr_typ rt, gr_taut)
  text \<open>By (9), \<open>\<box>(Lr)\<close>, which by definition is \<open>Lr = \<top>\<close>.\<close>
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?Lr (\<box>\<^sub>o ?Lr)" by (rule gr_Lemma2_9[OF rt])
  then have s2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?Lr (Eq Prop ?Lr ObjTrue)"
    by (simp only: ObjBox_def)
  have s12: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?q (Eq Prop ?Lr ObjTrue)"
    by (rule grk_imp_trans[OF s1 s2])
  text \<open>Hence \<open>q = r & Lr = r & \<top> = r\<close>.\<close>
  have s3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop ?Lr ObjTrue) (Eq Prop ?q ?rT)"
    by (rule grk_eq_conj_right[OF lrt typed_ObjTrue rt])
  have s4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?rT r"
    by (rule grk_iff_eq, rule grk_PC1[OF CEV_axiom_proves_ObjTrue]) (gr_typ rt, gr_taut)
  have s5: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop ?q ?rT) (Imp (Eq Prop ?rT r) (Eq Prop ?q r))"
    by (rule grk_eq_trans) (gr_typ rt)+
  have s6: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop ?q r) (Eq Prop r ?q)"
    by (rule grk_eq_sym) (gr_typ rt)+
  text \<open>Substitution in \<open>Lr\<close> gives \<open>Lq\<close>.\<close>
  have s7: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop r ?q) (Imp ?Lr (App gr_L ?q))"
    by (rule grk_LL) (gr_typ rt)+
  have ty: "\<Gamma> \<turnstile> Imp ?q (App gr_L ?q) : Prop" by (gr_typ rt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?q (App gr_L ?q)"
    by (rule grk_PC6[OF s12 s3 s4 s5 s6 s7 ty]) gr_taut
  then show ?thesis by (simp only: gr_q_def)
qed

text \<open>
  "Discharging \<open>q\<close> and generalizing \<open>r\<close> proves
     \<open>\<forall>r((r & Lr) \<rightarrow> L(r & Lr))\<close>."
\<close>

theorem gr_Lemma3_closure:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop (Imp (gr_q (Var 0)) (App gr_L (gr_q (Var 0))))"
  by (rule grk_gen, rule gr_Lemma3_q_imp_Lq) gr_typ

section \<open>\<open>Lq\<close>\<close>

text \<open>
  "Necessitation and boxed universal instantiation therefore give
  \<open>\<box>(\<not>q \<or> Lq)\<close>.  By weakening inside the box we obtain
  \<open>\<box>(\<not>q \<or> Lq \<or> L(\<not>q))\<close>.  This is the second disjunct of \<open>(\<Sigma>L)q\<close>, so (8)
  gives \<open>Lq\<close>."
\<close>

theorem gr_Lemma3_Lq:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_L (gr_q r)"
proof -
  let ?q = "gr_q r"
  let ?Lq = "App gr_L ?q"
  let ?Lnq = "App gr_L (Neg ?q)"
  let ?body = "Imp (gr_q (Var 0)) (App gr_L (gr_q (Var 0)))"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (gr_typ rt)
  text \<open>Necessitation of the universal closure.\<close>
  have nec: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Forall Prop ?body)"
    by (rule grk_nec[OF gr_Lemma3_closure])
  text \<open>Boxed universal instantiation at \<open>r\<close>.\<close>
  have bt: "Prop # \<Gamma> \<turnstile> ?body : Prop" by gr_typ
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Forall Prop ?body)) (\<box>\<^sub>o (subst0 r ?body))"
    by (rule grk_boxed_UI[OF bt rt])
  then have ui: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Forall Prop ?body)) (\<box>\<^sub>o (Imp ?q ?Lq))"
    by (simp add: grs)
  have b1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Imp ?q ?Lq)" by (rule grk_MP[OF nec ui])
  have w1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp ?q ?Lq)) (\<box>\<^sub>o (Disj (Neg ?q) ?Lq))"
    by (rule grk_box_mono, rule grk_taut) (gr_typ rt, gr_taut)
  have b2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Disj (Neg ?q) ?Lq)" by (rule grk_MP[OF b1 w1])
  text \<open>Weakening inside the box.\<close>
  have w2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Disj (Neg ?q) ?Lq)) (\<box>\<^sub>o (Disj (Neg ?q) (Disj ?Lq ?Lnq)))"
    by (rule grk_box_mono, rule grk_taut) (gr_typ rt, gr_taut)
  have b3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Disj (Neg ?q) (Disj ?Lq ?Lnq))"
    by (rule grk_MP[OF b2 w2])
  text \<open>This is the second disjunct of \<open>(\<Sigma>L)q\<close>.\<close>
  from b3 have b3': "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (gr_sgB gr_L ?q)"
    by (simp only: gr_sgB_def)
  have ty: "\<Gamma> \<turnstile> gr_sg gr_L ?q : Prop" by (gr_typ rt)
  have sg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sg gr_L ?q"
    by (rule grk_PC1[OF b3' ty]) gr_taut
  have sig: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App (App gr_Sigma gr_L) ?q"
    by (rule grk_iff_mp_rev[OF gr_Sigma_app[OF typed_gr_L qt] sg])
  text \<open>So (8) gives \<open>Lq\<close>.\<close>
  show ?thesis by (rule grk_iff_mp_rev[OF gr_Lemma2_8[OF qt] sig])
qed

section \<open>\<open>g(\<not>q) = \<not>q\<close>\<close>

text \<open>"Symmetry gives \<open>L(\<not>q)\<close>, and (9) gives \<open>L(\<not>q) = \<top>\<close>."\<close>

theorem gr_Lemma3_Lnq:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App gr_L (Neg (gr_q r))"
proof -
  have qt: "\<Gamma> \<turnstile> gr_q r : Prop" by (gr_typ rt)
  show ?thesis by (rule grk_iff_mp_rev[OF gr_Lemma2_10[OF qt] gr_Lemma3_Lq[OF rt]])
qed

theorem gr_Lemma3_Lnq_top:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_L (Neg (gr_q r))) ObjTrue"
proof -
  have nqt: "\<Gamma> \<turnstile> Neg (gr_q r) : Prop" by (gr_typ rt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (App gr_L (Neg (gr_q r)))"
    by (rule grk_MP[OF gr_Lemma3_Lnq[OF rt] gr_Lemma2_9[OF nqt]])
  then show ?thesis by (simp only: ObjBox_def)
qed

text \<open>"Thus \<open>g(\<not>q) = \<not>q & L(\<not>q) = \<not>q & \<top> = \<not>q\<close>."\<close>

theorem gr_Lemma3_g_neg_q:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_g (Neg (gr_q r))) (Neg (gr_q r))"
proof -
  let ?nq = "Neg (gr_q r)"
  let ?Lnq = "App gr_L ?nq"
  have nqt: "\<Gamma> \<turnstile> ?nq : Prop" by (gr_typ rt)
  have lnqt: "\<Gamma> \<turnstile> ?Lnq : Prop" by (gr_typ rt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_g ?nq) (gr_q ?nq)"
    by (rule gr_Lemma3_g_r[OF nqt])
  then have i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App gr_g ?nq) (Conj ?nq ?Lnq)"
    by (simp only: gr_q_def)
  have i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Conj ?nq ?Lnq) (Conj ?nq ObjTrue)"
    by (rule grk_MP[OF gr_Lemma3_Lnq_top[OF rt]
          grk_eq_conj_right[OF lnqt typed_ObjTrue nqt]])
  have i3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Conj ?nq ObjTrue) ?nq"
    by (rule grk_iff_eq, rule grk_PC1[OF CEV_axiom_proves_ObjTrue]) (gr_typ rt, gr_taut)
  show ?thesis by (rule grk_eq_trans_rule[OF grk_eq_trans_rule[OF i1 i2] i3])
qed

end
