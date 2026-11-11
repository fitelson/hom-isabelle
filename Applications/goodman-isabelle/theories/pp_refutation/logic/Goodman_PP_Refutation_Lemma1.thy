theory Goodman_PP_Refutation_Lemma1
  imports Goodman_PP_Refutation_Objects_Logic
begin

text \<open>
  LEMMA 1 of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>):

    "The following are logical theorems.
       (4)  \<open>(\<Sigma>Y)(\<not>p) \<leftrightarrow> (\<Sigma>Y)p\<close>
       (5)  \<open>(\<Sigma>Y)p \<rightarrow> \<box>((\<Sigma>Y)p)\<close>
       (6)  \<open>\<box>(V \<subseteq> W) \<rightarrow> \<box>(\<Sigma>V \<subseteq> \<Sigma>W)\<close>"

  and, from its proof, (7) \<open>\<box>(V \<subseteq> W) \<rightarrow> (\<Sigma>V \<subseteq> \<Sigma>W)\<close>.  "Logical theorem":
  derivable for every stock \<open>T\<close> (in particular the empty one), for arbitrary
  well-typed parameters in any context.  Order below: (4), (5), (7), (6), as
  in the note's proof.
\<close>

section \<open>(4)\<close>

text \<open>
  "Replacing \<open>p\<close> by \<open>\<not>p\<close> in (1) interchanges the two boxed disjuncts and
  interchanges \<open>Yp\<close> with \<open>Y(\<not>p)\<close> inside each box.  Double negation and
  commutativity of disjunction give (4)."
\<close>

lemma gr_Lemma1_4_unfolded:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (gr_sg Y (Neg p) \<longleftrightarrow>\<^sub>o gr_sg Y p)"
proof -
  let ?np = "Neg p"
  let ?nnp = "Neg (Neg p)"
  have npt: "\<Gamma> \<turnstile> ?np : Prop" by (gr_typ pt)
  have nnpt: "\<Gamma> \<turnstile> ?nnp : Prop" by (gr_typ pt)
  text \<open>Double negation, as an identity, and its use under \<open>Y\<close>.\<close>
  have dn: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?nnp p" by (rule grk_DN[OF pt])
  have dn': "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop p ?nnp" by (rule grk_eq_sym_rule[OF dn])
  have y1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App Y ?nnp) (App Y p)"
    by (rule grk_MP[OF dn grk_LL[OF nnpt pt yt]])
  have y2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App Y p) (App Y ?nnp)"
    by (rule grk_MP[OF dn' grk_LL[OF pt nnpt yt]])
  text \<open>The matrices of the two boxes are interchanged.\<close>
  have tA: "\<Gamma> \<turnstile> (gr_sgA Y ?np \<longleftrightarrow>\<^sub>o gr_sgB Y p) : Prop" by (gr_typ yt pt)
  have cA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (gr_sgA Y ?np \<longleftrightarrow>\<^sub>o gr_sgB Y p)"
    by (rule grk_PC2[OF y1 y2 tA]) gr_taut
  have tB: "\<Gamma> \<turnstile> (gr_sgB Y ?np \<longleftrightarrow>\<^sub>o gr_sgA Y p) : Prop" by (gr_typ yt pt)
  have cB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (gr_sgB Y ?np \<longleftrightarrow>\<^sub>o gr_sgA Y p)"
    by (rule grk_PC2[OF y1 y2 tB]) gr_taut
  have bA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o (gr_sgA Y ?np) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (gr_sgB Y p))"
    by (rule grk_box_iff[OF cA])
  have bB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o (gr_sgB Y ?np) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (gr_sgA Y p))"
    by (rule grk_box_iff[OF cB])
  have ty: "\<Gamma> \<turnstile> (gr_sg Y ?np \<longleftrightarrow>\<^sub>o gr_sg Y p) : Prop" by (gr_typ yt pt)
  show ?thesis by (rule grk_PC2[OF bA bB ty]) gr_taut
qed

text \<open>(4): \<open>(\<Sigma>Y)(\<not>p) \<leftrightarrow> (\<Sigma>Y)p\<close>.\<close>

theorem gr_Lemma1_4:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App (App gr_Sigma Y) (Neg p) \<longleftrightarrow>\<^sub>o App (App gr_Sigma Y) p)"
proof -
  have npt: "\<Gamma> \<turnstile> Neg p : Prop" by (gr_typ pt)
  show ?thesis
    by (rule grk_iff_trans[OF gr_Sigma_app[OF yt npt]
          grk_iff_trans[OF gr_Lemma1_4_unfolded[OF yt pt]
            grk_iff_sym[OF gr_Sigma_app[OF yt pt]]]])
qed

section \<open>(5)\<close>

text \<open>
  "For (5), S4 proves \<open>\<box>A \<or> \<box>B \<rightarrow> \<box>(\<box>A \<or> \<box>B)\<close>.  Apply this to the two
  disjuncts in (1)."   (The S4 theorem is \<open>grk_box_disj_stable\<close>.)
\<close>

lemma gr_Lemma1_5_unfolded:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_sg Y p) (\<box>\<^sub>o (gr_sg Y p))"
proof -
  have at: "\<Gamma> \<turnstile> gr_sgA Y p : Prop" by (gr_typ yt pt)
  have bt: "\<Gamma> \<turnstile> gr_sgB Y p : Prop" by (gr_typ yt pt)
  show ?thesis unfolding gr_sg_def by (rule grk_box_disj_stable[OF at bt])
qed

text \<open>(5): \<open>(\<Sigma>Y)p \<rightarrow> \<box>((\<Sigma>Y)p)\<close>.\<close>

theorem gr_Lemma1_5:
  assumes yt: "\<Gamma> \<turnstile> Y : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App (App gr_Sigma Y) p) (\<box>\<^sub>o (App (App gr_Sigma Y) p))"
proof -
  have s4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gr_sg Y p) (\<box>\<^sub>o (gr_sg Y p))"
    by (rule gr_Lemma1_5_unfolded[OF yt pt])
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (App gr_Sigma Y) p \<longleftrightarrow>\<^sub>o gr_sg Y p)"
    by (rule gr_Sigma_app[OF yt pt])
  have bb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o (App (App gr_Sigma Y) p) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (gr_sg Y p))"
    by (rule grk_box_iff[OF b])
  have ty: "\<Gamma> \<turnstile> Imp (App (App gr_Sigma Y) p) (\<box>\<^sub>o (App (App gr_Sigma Y) p)) : Prop"
    by (gr_typ yt pt)
  show ?thesis by (rule grk_PC3[OF s4 b bb ty]) gr_taut
qed

section \<open>(7)\<close>

text \<open>
  "For monotonicity, suppose that \<open>\<box>(V \<subseteq> W)\<close>.  Boxed universal instantiation
  gives both \<open>\<box>(Vp \<rightarrow> Wp)\<close> and \<open>\<box>(V(\<not>p) \<rightarrow> W(\<not>p))\<close>.  The normal modal rules
  therefore take each disjunct of \<open>(\<Sigma>V)p\<close> to its corresponding disjunct in
  \<open>(\<Sigma>W)p\<close>."
\<close>

lemma gr_Lemma1_7_unfolded:
  assumes vt: "\<Gamma> \<turnstile> V : gr_u" and wt: "\<Gamma> \<turnstile> W : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sub V W)) (Imp (gr_sg V p) (gr_sg W p))"
proof -
  let ?I1 = "Imp (App V p) (App W p)"
  let ?I2 = "Imp (App V (Neg p)) (App W (Neg p))"
  have npt: "\<Gamma> \<turnstile> Neg p : Prop" by (gr_typ pt)
  text \<open>Boxed universal instantiation.\<close>
  have u1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sub V W)) (\<box>\<^sub>o ?I1)"
    by (rule grk_box_mono[OF gr_sub_E[OF vt wt pt]])
  have u2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sub V W)) (\<box>\<^sub>o ?I2)"
    by (rule grk_box_mono[OF gr_sub_E[OF vt wt npt]])
  text \<open>The normal modal rules, disjunct by disjunct.\<close>
  have tA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?I1 (Imp ?I2 (Imp (gr_sgA V p) (gr_sgA W p)))"
    by (rule grk_taut) (gr_typ vt wt pt, gr_taut)
  have tB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?I1 (Imp ?I2 (Imp (gr_sgB V p) (gr_sgB W p)))"
    by (rule grk_taut) (gr_typ vt wt pt, gr_taut)
  have kA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o ?I1) (Imp (\<box>\<^sub>o ?I2) (Imp (\<box>\<^sub>o (gr_sgA V p)) (\<box>\<^sub>o (gr_sgA W p))))"
    by (rule grk_box_mono3[OF tA])
  have kB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o ?I1) (Imp (\<box>\<^sub>o ?I2) (Imp (\<box>\<^sub>o (gr_sgB V p)) (\<box>\<^sub>o (gr_sgB W p))))"
    by (rule grk_box_mono3[OF tB])
  have ty: "\<Gamma> \<turnstile> Imp (\<box>\<^sub>o (gr_sub V W)) (Imp (gr_sg V p) (gr_sg W p)) : Prop"
    by (gr_typ vt wt pt)
  show ?thesis by (rule grk_PC4[OF u1 u2 kA kB ty]) gr_taut
qed

lemma gr_Lemma1_7_pointwise:
  assumes vt: "\<Gamma> \<turnstile> V : gr_u" and wt: "\<Gamma> \<turnstile> W : gr_u" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<box>\<^sub>o (gr_sub V W)) (Imp (App (App gr_Sigma V) p) (App (App gr_Sigma W) p))"
proof -
  have ty: "\<Gamma> \<turnstile> Imp (\<box>\<^sub>o (gr_sub V W))
      (Imp (App (App gr_Sigma V) p) (App (App gr_Sigma W) p)) : Prop"
    by (gr_typ vt wt pt)
  show ?thesis
    by (rule grk_PC3[OF gr_Lemma1_7_unfolded[OF vt wt pt] gr_Sigma_app[OF vt pt]
          gr_Sigma_app[OF wt pt] ty]) gr_taut
qed

text \<open>
  "Generalizing \<open>p\<close> and discharging the assumption proves
     (7)  \<open>\<box>(V \<subseteq> W) \<rightarrow> (\<Sigma>V \<subseteq> \<Sigma>W)\<close>."
\<close>

theorem gr_Lemma1_7:
  assumes vt: "\<Gamma> \<turnstile> V : gr_u" and wt: "\<Gamma> \<turnstile> W : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<box>\<^sub>o (gr_sub V W)) (gr_sub (App gr_Sigma V) (App gr_Sigma W))"
proof (rule gr_sub_I_imp)
  show "\<Gamma> \<turnstile> \<box>\<^sub>o (gr_sub V W) : Prop" by (gr_typ vt wt)
  have "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (gr_sub (shift V) (shift W)))
        (Imp (App (App gr_Sigma (shift V)) (Var 0)) (App (App gr_Sigma (shift W)) (Var 0)))"
    by (rule gr_Lemma1_7_pointwise; gr_typ vt wt)
  then show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (\<box>\<^sub>o (gr_sub V W)))
        (Imp (App (shift (App gr_Sigma V)) (Var 0)) (App (shift (App gr_Sigma W)) (Var 0)))"
    by (simp add: grs)
qed

section \<open>(6)\<close>

text \<open>
  "Necessitate the universal closure of this theorem and instantiate inside
  the box at \<open>V, W\<close>.  Axiom 4 gives \<open>\<box>(V \<subseteq> W) \<rightarrow> \<box>\<box>(V \<subseteq> W)\<close>, so K gives
  the boxed conclusion in (6)."
\<close>

text \<open>The universal closure \<open>\<forall>V\<forall>W(\<box>(V \<subseteq> W) \<rightarrow> (\<Sigma>V \<subseteq> \<Sigma>W))\<close> of (7).\<close>

theorem gr_Lemma1_7_closure:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Forall gr_u (Forall gr_u
      (Imp (\<box>\<^sub>o (gr_sub (Var (Suc 0)) (Var 0)))
        (gr_sub (App gr_Sigma (Var (Suc 0))) (App gr_Sigma (Var 0)))))"
  by (rule grk_gen, rule grk_gen, rule gr_Lemma1_7) gr_typ+

text \<open>(6): \<open>\<box>(V \<subseteq> W) \<rightarrow> \<box>(\<Sigma>V \<subseteq> \<Sigma>W)\<close>.\<close>

theorem gr_Lemma1_6:
  assumes vt: "\<Gamma> \<turnstile> V : gr_u" and wt: "\<Gamma> \<turnstile> W : gr_u"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<box>\<^sub>o (gr_sub V W)) (\<box>\<^sub>o (gr_sub (App gr_Sigma V) (App gr_Sigma W)))"
proof -
  let ?M = "\<lambda>V W. Imp (\<box>\<^sub>o (gr_sub V W)) (gr_sub (App gr_Sigma V) (App gr_Sigma W))"
  let ?C1 = "Forall gr_u (?M (Var (Suc 0)) (Var 0))"
  let ?C = "Forall gr_u ?C1"
  text \<open>Necessitation of the universal closure.\<close>
  have nec: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o ?C" by (rule grk_nec[OF gr_Lemma1_7_closure])
  text \<open>Instantiation inside the box, at \<open>V\<close> and then at \<open>W\<close>.\<close>
  have t1: "gr_u # \<Gamma> \<turnstile> ?C1 : Prop" by gr_typ
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o ?C) (\<box>\<^sub>o (subst0 V ?C1))"
    by (rule grk_boxed_UI[OF t1 vt])
  then have i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o ?C) (\<box>\<^sub>o (Forall gr_u (?M (shift V) (Var 0))))"
    by (simp add: grk_subst0_Forall grs shift_def)
  have t2: "gr_u # \<Gamma> \<turnstile> ?M (shift V) (Var 0) : Prop" by (gr_typ vt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Forall gr_u (?M (shift V) (Var 0)))) (\<box>\<^sub>o (subst0 W (?M (shift V) (Var 0))))"
    by (rule grk_boxed_UI[OF t2 wt])
  then have i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Forall gr_u (?M (shift V) (Var 0)))) (\<box>\<^sub>o (?M V W))"
    by (simp add: grs)
  have nb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (?M V W)"
    by (rule grk_MP[OF grk_MP[OF nec i1] i2])
  text \<open>Axiom 4 and K.\<close>
  have k: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (?M V W))
      (Imp (\<box>\<^sub>o (\<box>\<^sub>o (gr_sub V W))) (\<box>\<^sub>o (gr_sub (App gr_Sigma V) (App gr_Sigma W))))"
    by (rule grk_K) (gr_typ vt wt)+
  have four: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (gr_sub V W)) (\<box>\<^sub>o (\<box>\<^sub>o (gr_sub V W)))"
    by (rule grk_4) (gr_typ vt wt)
  have ty: "\<Gamma> \<turnstile> Imp (\<box>\<^sub>o (gr_sub V W))
      (\<box>\<^sub>o (gr_sub (App gr_Sigma V) (App gr_Sigma W))) : Prop"
    by (gr_typ vt wt)
  show ?thesis by (rule grk_PC3[OF nb k four ty]) gr_taut
qed

end
