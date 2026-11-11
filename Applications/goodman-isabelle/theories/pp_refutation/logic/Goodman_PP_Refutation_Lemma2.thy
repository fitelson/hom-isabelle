theory Goodman_PP_Refutation_Lemma2
  imports Goodman_PP_Refutation_Lemma1
begin

text \<open>
  LEMMA 2 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "Logic alone proves
       (8)   \<open>Lp \<leftrightarrow> (\<Sigma>L)p\<close>
       (9)   \<open>Lp \<rightarrow> \<box>(Lp)\<close>
       (10)  \<open>L(\<not>p) \<leftrightarrow> Lp\<close>.
     It also proves \<open>Pre(W) \<rightarrow> \<box>(L \<subseteq> W)\<close> for every \<open>W\<close>."   (the last is (11))

  Every theorem holds for every stock \<open>T\<close> and arbitrary well-typed parameters.
  Order below as in the note's proof: (11), \<open>\<Sigma>L \<subseteq> L\<close>, \<open>Pre(L)\<close>, \<open>Pre(\<Sigma>L)\<close>,
  \<open>L \<subseteq> \<Sigma>L\<close>, (8), (9), (10).
\<close>

section \<open>(11)\<close>

text \<open>
  "Instantiating the quantifier in (3) gives the logical theorem
  \<open>Pre(W) \<rightarrow> L \<subseteq> W\<close>."
\<close>

lemma gr_Lemma2_inst_pointwise:
  assumes wt: "\<Gamma> \<turnstile> W : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (Imp (App gr_L p) (App W p))"
proof -
  have ty: "\<Gamma> \<turnstile> Imp (gr_Pre W) (Imp (App gr_L p) (App W p)) : Prop"
    by (gr_typ wt pt)
  show ?thesis
    by (rule grk_PC2[OF gr_L_app[OF pt] gr_Lbody_E[OF pt wt] ty]) gr_taut
qed

theorem gr_Lemma2_inst:
  assumes wt: "\<Gamma> \<turnstile> W : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (gr_sub gr_L W)"
proof (rule gr_sub_I_imp)
  show "\<Gamma> \<turnstile> gr_Pre W : Prop" by (gr_typ wt)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Pre (shift W)) (Imp (App gr_L (Var 0)) (App (shift W) (Var 0)))"
    by (rule gr_Lemma2_inst_pointwise; gr_typ wt)
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (gr_Pre W)) (Imp (App (shift gr_L) (Var 0)) (App (shift W) (Var 0)))"
    by (simp add: grs)
qed

text \<open>
  "Its necessitation, together with \<open>Pre(W) \<rightarrow> \<box>Pre(W)\<close> from axiom 4, gives
     (11)  \<open>Pre(W) \<rightarrow> \<box>(L \<subseteq> W)\<close>."
\<close>

theorem gr_Lemma2_11:
  assumes wt: "\<Gamma> \<turnstile> W : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (\<box>\<^sub>o (gr_sub gr_L W))"
proof -
  have nec: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Imp (gr_Pre W) (gr_sub gr_L W))"
    by (rule grk_nec[OF gr_Lemma2_inst[OF wt]])
  have k: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp (gr_Pre W) (gr_sub gr_L W)))
      (Imp (\<box>\<^sub>o (gr_Pre W)) (\<box>\<^sub>o (gr_sub gr_L W)))"
    by (rule grk_K) (gr_typ wt)+
  have four: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (\<box>\<^sub>o (gr_Pre W))"
    unfolding gr_Pre_def by (rule grk_4) (gr_typ wt)
  have ty: "\<Gamma> \<turnstile> Imp (gr_Pre W) (\<box>\<^sub>o (gr_sub gr_L W)) : Prop" by (gr_typ wt)
  show ?thesis by (rule grk_PC3[OF nec k four ty]) gr_taut
qed

section \<open>\<open>\<Sigma>L \<subseteq> L\<close> and \<open>Pre(L)\<close>\<close>

text \<open>
  "We first show \<open>\<Sigma>L \<subseteq> L\<close>.  Suppose that \<open>(\<Sigma>L)p\<close> and let \<open>W\<close> satisfy
  \<open>Pre(W)\<close>.  By (11) and (7), \<open>(\<Sigma>W)p\<close>.  Factivity applied to \<open>Pre(W)\<close> then
  gives \<open>Wp\<close>."
\<close>

lemma gr_Lemma2_SigmaL_step:
  assumes wt: "\<Gamma> \<turnstile> W : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App (App gr_Sigma gr_L) p) (Imp (gr_Pre W) (App W p))"
proof -
  let ?SL = "App gr_Sigma gr_L"
  let ?SW = "App gr_Sigma W"
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (\<box>\<^sub>o (gr_sub gr_L W))"
    by (rule gr_Lemma2_11[OF wt])
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sub gr_L W)) (gr_sub ?SL ?SW)"
    by (rule gr_Lemma1_7[OF typed_gr_L wt])
  have c: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_sub ?SL ?SW) (Imp (App ?SL p) (App ?SW p))"
    by (rule gr_sub_E) (gr_typ wt pt)+
  have d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_Pre W) (gr_sub ?SW W)"
    unfolding gr_Pre_def by (rule grk_T) (gr_typ wt)
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_sub ?SW W) (Imp (App ?SW p) (App W p))"
    by (rule gr_sub_E) (gr_typ wt pt)+
  have ty: "\<Gamma> \<turnstile> Imp (App ?SL p) (Imp (gr_Pre W) (App W p)) : Prop"
    by (gr_typ wt pt)
  show ?thesis by (rule grk_PC5[OF a b c d e ty]) gr_taut
qed

text \<open>"Discharging \<open>Pre(W)\<close> and generalizing \<open>W\<close> gives \<open>Lp\<close> by (3)."\<close>

lemma gr_Lemma2_SigmaL_imp_L:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App (App gr_Sigma gr_L) p) (App gr_L p)"
proof -
  let ?H = "App (App gr_Sigma gr_L) p"
  have ht: "\<Gamma> \<turnstile> ?H : Prop" by (gr_typ pt)
  have "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (App gr_Sigma gr_L) (shift p)) (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p)))"
    by (rule gr_Lemma2_SigmaL_step; gr_typ pt)
  then have "gr_u # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Imp (gr_Pre (Var 0)) (App (Var 0) (shift p)))"
    by (simp add: grs)
  then have g: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (gr_Lbody p)"
    by (rule gr_Lbody_I_imp[OF ht])
  have ty: "\<Gamma> \<turnstile> Imp ?H (App gr_L p) : Prop" by (gr_typ pt)
  show ?thesis by (rule grk_PC2[OF g gr_L_app[OF pt] ty]) gr_taut
qed

text \<open>
  "After discharging \<open>(\<Sigma>L)p\<close> and generalizing \<open>p\<close>, we have proved
  \<open>\<Sigma>L \<subseteq> L\<close> as a logical theorem."
\<close>

theorem gr_Lemma2_SigmaL_sub_L:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sub (App gr_Sigma gr_L) gr_L"
proof (rule gr_sub_I)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (App gr_Sigma gr_L) (Var 0)) (App gr_L (Var 0))"
    by (rule gr_Lemma2_SigmaL_imp_L) gr_typ
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (shift (App gr_Sigma gr_L)) (Var 0)) (App (shift gr_L) (Var 0))"
    by (simp add: grs)
qed

text \<open>"Necessitation therefore gives \<open>\<box>(\<Sigma>L \<subseteq> L)\<close>, which is \<open>Pre(L)\<close>."\<close>

theorem gr_Lemma2_Pre_L: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Pre gr_L"
  unfolding gr_Pre_def by (rule grk_nec[OF gr_Lemma2_SigmaL_sub_L])

section \<open>\<open>Pre(\<Sigma>L)\<close> and \<open>L \<subseteq> \<Sigma>L\<close>\<close>

text \<open>
  "Now apply the stronger monotonicity law (6) with \<open>V = \<Sigma>L\<close> and \<open>W = L\<close>.
  It gives \<open>\<box>(\<Sigma>(\<Sigma>L) \<subseteq> \<Sigma>L)\<close>, which is \<open>Pre(\<Sigma>L)\<close>."
\<close>

theorem gr_Lemma2_Pre_SigmaL: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Pre (App gr_Sigma gr_L)"
proof -
  let ?S = "App gr_Sigma gr_L"
  have st: "\<Gamma> \<turnstile> ?S : gr_u" by gr_typ
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_Pre gr_L" by (rule gr_Lemma2_Pre_L)
  then have boxed: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (gr_sub ?S gr_L)"
    by (simp only: gr_Pre_def)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (gr_sub (App gr_Sigma ?S) ?S)"
    by (rule grk_MP[OF boxed gr_Lemma1_6[OF st typed_gr_L]])
  then show ?thesis by (simp only: gr_Pre_def)
qed

text \<open>"Instantiating (3) at \<open>W = \<Sigma>L\<close> thus proves \<open>L \<subseteq> \<Sigma>L\<close>."\<close>

lemma gr_Lemma2_L_imp_SigmaL:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_L p) (App (App gr_Sigma gr_L) p)"
proof -
  have st: "\<Gamma> \<turnstile> App gr_Sigma gr_L : gr_u" by gr_typ
  have e: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (gr_Lbody p)
        (Imp (gr_Pre (App gr_Sigma gr_L)) (App (App gr_Sigma gr_L) p))"
    by (rule gr_Lbody_E[OF pt st])
  have ty: "\<Gamma> \<turnstile> Imp (App gr_L p) (App (App gr_Sigma gr_L) p) : Prop"
    by (gr_typ pt)
  show ?thesis
    by (rule grk_PC3[OF gr_L_app[OF pt] e gr_Lemma2_Pre_SigmaL ty]) gr_taut
qed

theorem gr_Lemma2_L_sub_SigmaL:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gr_sub gr_L (App gr_Sigma gr_L)"
proof (rule gr_sub_I)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App gr_L (Var 0)) (App (App gr_Sigma gr_L) (Var 0))"
    by (rule gr_Lemma2_L_imp_SigmaL) gr_typ
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App (shift gr_L) (Var 0)) (App (shift (App gr_Sigma gr_L)) (Var 0))"
    by (simp add: grs)
qed

section \<open>(8)\<close>

text \<open>"Together the two inclusions give (8)":  \<open>Lp \<leftrightarrow> (\<Sigma>L)p\<close>.\<close>

theorem gr_Lemma2_8:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_L p \<longleftrightarrow>\<^sub>o App (App gr_Sigma gr_L) p)"
proof -
  let ?SL = "App gr_Sigma gr_L"
  have i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_L p) (App ?SL p)"
    by (rule grk_MP[OF gr_Lemma2_L_sub_SigmaL gr_sub_E]) (gr_typ pt)+
  have i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App ?SL p) (App gr_L p)"
    by (rule grk_MP[OF gr_Lemma2_SigmaL_sub_L gr_sub_E]) (gr_typ pt)+
  show ?thesis by (rule grk_iff_intro[OF i1 i2])
qed

lemma gr_Lemma2_8_unfolded:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_L p \<longleftrightarrow>\<^sub>o gr_sg gr_L p)"
  by (rule grk_iff_trans[OF gr_Lemma2_8[OF pt] gr_Sigma_app[OF typed_gr_L pt]])

section \<open>(9)\<close>

text \<open>
  "The fixed-point biconditional is a logical theorem, so its necessitation
  is available.  From \<open>Lp\<close>, it gives \<open>(\<Sigma>L)p\<close>, then \<open>\<box>((\<Sigma>L)p)\<close> by (5), and
  finally \<open>\<box>(Lp)\<close> by K and the necessitated reverse implication.  This
  proves (9)":  \<open>Lp \<rightarrow> \<box>(Lp)\<close>.
\<close>

theorem gr_Lemma2_9:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gr_L p) (\<box>\<^sub>o (App gr_L p))"
proof -
  let ?S = "App (App gr_Sigma gr_L) p"
  let ?Lp = "App gr_L p"
  have fp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?Lp \<longleftrightarrow>\<^sub>o ?S)" by (rule gr_Lemma2_8[OF pt])
  have nfix: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (?Lp \<longleftrightarrow>\<^sub>o ?S)" by (rule grk_nec[OF fp])
  have rev: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (?Lp \<longleftrightarrow>\<^sub>o ?S)) (\<box>\<^sub>o (Imp ?S ?Lp))"
    by (rule grk_box_mono, rule grk_taut) (gr_typ pt, gr_taut)
  have k: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp ?S ?Lp)) (Imp (\<box>\<^sub>o ?S) (\<box>\<^sub>o ?Lp))"
    by (rule grk_K) (gr_typ pt)+
  have five: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?S (\<box>\<^sub>o ?S)"
    by (rule gr_Lemma1_5[OF typed_gr_L pt])
  have ty: "\<Gamma> \<turnstile> Imp ?Lp (\<box>\<^sub>o ?Lp) : Prop" by (gr_typ pt)
  show ?thesis by (rule grk_PC5[OF fp nfix rev k five ty]) gr_taut
qed

section \<open>(10)\<close>

text \<open>
  "The symmetry law (10) follows by applying (8) on both sides of (4) with
  \<open>Y = L\<close>":  \<open>L(\<not>p) \<leftrightarrow> Lp\<close>.
\<close>

theorem gr_Lemma2_10:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App gr_L (Neg p) \<longleftrightarrow>\<^sub>o App gr_L p)"
proof -
  have npt: "\<Gamma> \<turnstile> Neg p : Prop" by (gr_typ pt)
  show ?thesis
    by (rule grk_iff_trans[OF gr_Lemma2_8[OF npt]
          grk_iff_trans[OF gr_Lemma1_4[OF typed_gr_L pt] grk_iff_sym[OF gr_Lemma2_8[OF pt]]]])
qed

end
