theory Classicism_2_11_Transfer
  imports "Classicism_2_11_Formulas.Classicism_2_11_Order_Defs" "Classicism_2_11_Formulas.Classicism_2_11_World_Cases"
begin

section \<open>Transfer of the order notions along the encoding pc_enc\<close>

text \<open>
  At every world w of the concrete frame and every type τ, the encoding
  pc_enc τ w is a bijection from raw_D τ w onto paper_D τ w. This theory
  shows that it also carries the generic order notions of the concrete
  action model (at pa_Ar, Fst, Snd, paper_D) to their raw mirrors:
  the order ≤, emptiness, atoms, atomicity, and completeness (every HOL
  subset of the carrier has a greatest lower bound).
\<close>

subsection \<open>Quantifier bookkeeping\<close>

lemma c211_pc_enc_eq_iff:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D \<tau> w)" and ym: "Elem y (raw_D \<tau> w)"
  shows "pc_enc \<tau> w x = pc_enc \<tau> w y \<longleftrightarrow> x = y"
  using pc_enc_injective[OF ww xm ym] by blast

lemma c211_paper_D_forall:
  "(\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow> P z) \<longleftrightarrow>
    (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow> P (pc_enc \<tau> w z))"
  unfolding pc_D_member by blast

lemma c211_paper_D_exists:
  "(\<exists>z. Elem z (paper_D \<tau> w) \<and> P z) \<longleftrightarrow>
    (\<exists>z. Elem z (raw_D \<tau> w) \<and> P (pc_enc \<tau> w z))"
  unfolding pc_D_member by blast

text \<open>Arrows out of w are exactly the pairs Opair w v with raw_rel w v, and
  arguments at their targets are exactly encodings of raw arguments.\<close>

lemma c211_arrow_arg_forall:
  assumes ww: "Elem w raw_W"
  shows "(\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> Elem x (paper_D \<sigma> (Snd i)) \<longrightarrow>
      P (Snd i) i x) \<longleftrightarrow>
    (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      P v (Opair w v) (pc_enc \<sigma> v x))"
proof
  assume L: "\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> Elem x (paper_D \<sigma> (Snd i)) \<longrightarrow>
      P (Snd i) i x"
  show "\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      P v (Opair w v) (pc_enc \<sigma> v x)"
  proof (intro allI impI)
    fix v x assume vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (raw_D \<sigma> v)"
    have arrow: "Opair w v \<in> explode pa_Ar"
      by (simp only: explode_Elem pa_arrow_pair ww vw wv simp_thms)
    have source: "Fst (Opair w v) = w" by (rule Fst)
    have arg: "Elem (pc_enc \<sigma> v x) (paper_D \<sigma> (Snd (Opair w v)))"
      by (simp only: Snd pc_enc_type[OF xm])
    have "P (Snd (Opair w v)) (Opair w v) (pc_enc \<sigma> v x)"
      using L arrow source arg by blast
    then show "P v (Opair w v) (pc_enc \<sigma> v x)" by (simp only: Snd)
  qed
next
  assume R: "\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      P v (Opair w v) (pc_enc \<sigma> v x)"
  show "\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> Elem x (paper_D \<sigma> (Snd i)) \<longrightarrow>
      P (Snd i) i x"
  proof (intro allI impI)
    fix i x assume arrow: "i \<in> explode pa_Ar" and source: "Fst i = w"
      and xm: "Elem x (paper_D \<sigma> (Snd i))"
    note split = c211_arrow_split[OF arrow]
    obtain x' where x'm: "Elem x' (raw_D \<sigma> (Snd i))" and x: "x = pc_enc \<sigma> (Snd i) x'"
      using xm unfolding pc_D_member by blast
    have rel: "raw_rel w (Snd i)" using split(4) source by simp
    have i: "Opair w (Snd i) = i" using split(1) source by simp
    have "P (Snd i) (Opair w (Snd i)) (pc_enc \<sigma> (Snd i) x')"
      using R split(3) rel x'm by blast
    then show "P (Snd i) i x" by (simp only: i x)
  qed
qed

subsection \<open>The order ≤\<close>

lemma c211_transfer_leq_ind:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D Ind w)" and ym: "Elem y (raw_D Ind w)"
  shows "c211_cleq Ind w (pc_enc Ind w x) (pc_enc Ind w y) \<longleftrightarrow> c211_rleq Ind w x y"
  by (simp only: c211_pleq.simps(1) c211_rleq.simps(1) c211_pc_enc_eq_iff[OF ww xm ym])

lemma c211_transfer_leq_prop:
  "c211_cleq Prop w (pc_enc Prop w x) (pc_enc Prop w y) \<longleftrightarrow> c211_rleq Prop w x y"
proof
  assume L: "c211_cleq Prop w (pc_enc Prop w x) (pc_enc Prop w y)"
  show "c211_rleq Prop w x y"
    unfolding c211_rleq.simps(2)
  proof (intro allI impI)
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
      and tx: "raw_truth v (raw_T Prop w v x)"
    have "Elem (Opair w v) (pc_enc Prop w x)"
      using vw wv tx by (simp only: pc_prop_pair simp_thms)
    then have "Elem (Opair w v) (pc_enc Prop w y)"
      using L unfolding c211_pleq.simps(2) by blast
    then show "raw_truth v (raw_T Prop w v y)" using pc_prop_pair by blast
  qed
next
  assume R: "c211_rleq Prop w x y"
  show "c211_cleq Prop w (pc_enc Prop w x) (pc_enc Prop w y)"
    unfolding c211_pleq.simps(2)
  proof (intro allI impI)
    fix j assume jx: "Elem j (pc_enc Prop w x)"
    obtain v where j: "j = Opair w v" and vw: "Elem v raw_W" and wv: "raw_rel w v"
      and tx: "raw_truth v (raw_T Prop w v x)"
      using jx unfolding pc_prop_member by blast
    have "raw_truth v (raw_T Prop w v y)"
      using R vw wv tx unfolding c211_rleq.simps(2) by blast
    then show "Elem j (pc_enc Prop w y)"
      using vw wv by (simp only: j pc_prop_pair simp_thms)
  qed
qed

lemma c211_transfer_leq_arr:
  assumes ww: "Elem w raw_W"
    and Fm: "Elem F (raw_D (Arr \<sigma> \<rho>) w)" and Gm: "Elem G (raw_D (Arr \<sigma> \<rho>) w)"
    and IH: "\<And>v a b. Elem v raw_W \<Longrightarrow> Elem a (raw_D \<rho> v) \<Longrightarrow> Elem b (raw_D \<rho> v) \<Longrightarrow>
      c211_cleq \<rho> v (pc_enc \<rho> v a) (pc_enc \<rho> v b) \<longleftrightarrow> c211_rleq \<rho> v a b"
  shows "c211_cleq (Arr \<sigma> \<rho>) w (pc_enc (Arr \<sigma> \<rho>) w F) (pc_enc (Arr \<sigma> \<rho>) w G) \<longleftrightarrow>
    c211_rleq (Arr \<sigma> \<rho>) w F G"
proof -
  have point: "c211_cleq \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair (Opair w v) (pc_enc \<sigma> v x)))
        (app (pc_enc (Arr \<sigma> \<rho>) w G) (Opair (Opair w v) (pc_enc \<sigma> v x))) \<longleftrightarrow>
      c211_rleq \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x)
        (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v G) x)"
    if vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (raw_D \<sigma> v)" for v x
  proof -
    have fa: "Elem (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x) (raw_D \<rho> v)"
      by (rule raw_app_type[OF raw_T_type[OF ww vw wv Fm] xm])
    have ga: "Elem (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v G) x) (raw_D \<rho> v)"
      by (rule raw_app_type[OF raw_T_type[OF ww vw wv Gm] xm])
    show ?thesis by (simp only: pc_enc_app[OF ww vw wv xm] IH[OF vw fa ga])
  qed
  have "c211_cleq (Arr \<sigma> \<rho>) w (pc_enc (Arr \<sigma> \<rho>) w F) (pc_enc (Arr \<sigma> \<rho>) w G) \<longleftrightarrow>
      (\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> Elem x (paper_D \<sigma> (Snd i)) \<longrightarrow>
        c211_cleq \<rho> (Snd i) (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair i x))
          (app (pc_enc (Arr \<sigma> \<rho>) w G) (Opair i x)))"
    by (simp only: c211_pleq.simps(3))
  also have "\<dots> \<longleftrightarrow> (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_cleq \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair (Opair w v) (pc_enc \<sigma> v x)))
        (app (pc_enc (Arr \<sigma> \<rho>) w G) (Opair (Opair w v) (pc_enc \<sigma> v x))))"
    by (rule c211_arrow_arg_forall[OF ww, where \<sigma> = \<sigma> and
          P = "\<lambda>v i x. c211_cleq \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair i x))
            (app (pc_enc (Arr \<sigma> \<rho>) w G) (Opair i x))"])
  also have "\<dots> \<longleftrightarrow> (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_rleq \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x)
        (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v G) x))"
    using point by blast
  also have "\<dots> \<longleftrightarrow> c211_rleq (Arr \<sigma> \<rho>) w F G"
    by (simp only: c211_rleq.simps(3))
  finally show ?thesis .
qed

theorem c211_transfer_leq:
  assumes "Elem w raw_W" and "Elem x (raw_D \<tau> w)" and "Elem y (raw_D \<tau> w)"
  shows "c211_cleq \<tau> w (pc_enc \<tau> w x) (pc_enc \<tau> w y) \<longleftrightarrow> c211_rleq \<tau> w x y"
  using assms
proof (induction \<tau> arbitrary: w x y)
  case Ind
  show ?case by (rule c211_transfer_leq_ind[OF Ind.prems])
next
  case Prop
  show ?case by (rule c211_transfer_leq_prop)
next
  case (Arr \<sigma> \<rho>)
  show ?case by (rule c211_transfer_leq_arr[OF Arr.prems Arr.IH(2)])
qed

subsection \<open>Emptiness\<close>

lemma c211_transfer_empty_ind:
  "c211_cempty Ind w (pc_enc Ind w x) \<longleftrightarrow> c211_rempty Ind w x"
  by (simp only: c211_pempty.simps(1) c211_rempty.simps(1))

lemma c211_transfer_empty_prop:
  "c211_cempty Prop w (pc_enc Prop w x) \<longleftrightarrow> c211_rempty Prop w x"
proof
  assume L: "c211_cempty Prop w (pc_enc Prop w x)"
  show "c211_rempty Prop w x"
    unfolding c211_rempty.simps(2)
  proof (intro allI impI notI)
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
      and tx: "raw_truth v (raw_T Prop w v x)"
    have "Elem (Opair w v) (pc_enc Prop w x)"
      using vw wv tx by (simp only: pc_prop_pair simp_thms)
    then show False using L unfolding c211_pempty.simps(2) by blast
  qed
next
  assume R: "c211_rempty Prop w x"
  show "c211_cempty Prop w (pc_enc Prop w x)"
    unfolding c211_pempty.simps(2)
  proof (intro allI notI)
    fix j assume jx: "Elem j (pc_enc Prop w x)"
    obtain v where vw: "Elem v raw_W" and wv: "raw_rel w v"
      and tx: "raw_truth v (raw_T Prop w v x)"
      using jx unfolding pc_prop_member by blast
    show False using R vw wv tx unfolding c211_rempty.simps(2) by blast
  qed
qed

lemma c211_transfer_empty_arr:
  assumes ww: "Elem w raw_W" and Fm: "Elem F (raw_D (Arr \<sigma> \<rho>) w)"
    and IH: "\<And>v a. Elem v raw_W \<Longrightarrow> Elem a (raw_D \<rho> v) \<Longrightarrow>
      c211_cempty \<rho> v (pc_enc \<rho> v a) \<longleftrightarrow> c211_rempty \<rho> v a"
  shows "c211_cempty (Arr \<sigma> \<rho>) w (pc_enc (Arr \<sigma> \<rho>) w F) \<longleftrightarrow> c211_rempty (Arr \<sigma> \<rho>) w F"
proof -
  have point: "c211_cempty \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair (Opair w v) (pc_enc \<sigma> v x))) \<longleftrightarrow>
      c211_rempty \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x)"
    if vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (raw_D \<sigma> v)" for v x
  proof -
    have fa: "Elem (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x) (raw_D \<rho> v)"
      by (rule raw_app_type[OF raw_T_type[OF ww vw wv Fm] xm])
    show ?thesis by (simp only: pc_enc_app[OF ww vw wv xm] IH[OF vw fa])
  qed
  have "c211_cempty (Arr \<sigma> \<rho>) w (pc_enc (Arr \<sigma> \<rho>) w F) \<longleftrightarrow>
      (\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> Elem x (paper_D \<sigma> (Snd i)) \<longrightarrow>
        c211_cempty \<rho> (Snd i) (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair i x)))"
    by (simp only: c211_pempty.simps(3))
  also have "\<dots> \<longleftrightarrow> (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_cempty \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair (Opair w v) (pc_enc \<sigma> v x))))"
    by (rule c211_arrow_arg_forall[OF ww, where \<sigma> = \<sigma> and
          P = "\<lambda>v i x. c211_cempty \<rho> v (app (pc_enc (Arr \<sigma> \<rho>) w F) (Opair i x))"])
  also have "\<dots> \<longleftrightarrow> (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_rempty \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x))"
    using point by blast
  also have "\<dots> \<longleftrightarrow> c211_rempty (Arr \<sigma> \<rho>) w F"
    by (simp only: c211_rempty.simps(3))
  finally show ?thesis .
qed

theorem c211_transfer_empty:
  assumes "Elem w raw_W" and "Elem x (raw_D \<tau> w)"
  shows "c211_cempty \<tau> w (pc_enc \<tau> w x) \<longleftrightarrow> c211_rempty \<tau> w x"
  using assms
proof (induction \<tau> arbitrary: w x)
  case Ind
  show ?case by (rule c211_transfer_empty_ind)
next
  case Prop
  show ?case by (rule c211_transfer_empty_prop)
next
  case (Arr \<sigma> \<rho>)
  show ?case by (rule c211_transfer_empty_arr[OF Arr.prems Arr.IH(2)])
qed

subsection \<open>Atoms and atomicity\<close>

theorem c211_transfer_atom:
  assumes ww: "Elem w raw_W" and ym: "Elem y (raw_D \<tau> w)"
  shows "c211_patom pa_Ar Fst Snd paper_D \<tau> w (pc_enc \<tau> w y) \<longleftrightarrow> c211_ratom \<tau> w y"
proof -
  have point: "(c211_cleq \<tau> w (pc_enc \<tau> w z) (pc_enc \<tau> w y) \<and> pc_enc \<tau> w z \<noteq> pc_enc \<tau> w y \<longleftrightarrow>
        c211_cempty \<tau> w (pc_enc \<tau> w z)) \<longleftrightarrow>
      (c211_rleq \<tau> w z y \<and> z \<noteq> y \<longleftrightarrow> c211_rempty \<tau> w z)"
    if zm: "Elem z (raw_D \<tau> w)" for z
    by (simp only: c211_transfer_leq[OF ww zm ym] c211_pc_enc_eq_iff[OF ww zm ym]
        c211_transfer_empty[OF ww zm])
  have "c211_patom pa_Ar Fst Snd paper_D \<tau> w (pc_enc \<tau> w y) \<longleftrightarrow>
      (\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow>
        (c211_cleq \<tau> w z (pc_enc \<tau> w y) \<and> z \<noteq> pc_enc \<tau> w y \<longleftrightarrow> c211_cempty \<tau> w z))"
    by (simp only: c211_patom_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow>
      (c211_cleq \<tau> w (pc_enc \<tau> w z) (pc_enc \<tau> w y) \<and> pc_enc \<tau> w z \<noteq> pc_enc \<tau> w y \<longleftrightarrow>
        c211_cempty \<tau> w (pc_enc \<tau> w z)))"
    by (rule c211_paper_D_forall)
  also have "\<dots> \<longleftrightarrow> (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow>
      (c211_rleq \<tau> w z y \<and> z \<noteq> y \<longleftrightarrow> c211_rempty \<tau> w z))"
    using point by blast
  also have "\<dots> \<longleftrightarrow> c211_ratom \<tau> w y"
    by (simp only: c211_ratom_def)
  finally show ?thesis .
qed

lemma c211_transfer_atomic_point:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D \<tau> w)"
  shows "(c211_cempty \<tau> w (pc_enc \<tau> w x) \<or>
      (\<exists>y. Elem y (paper_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w y \<and>
        c211_cleq \<tau> w y (pc_enc \<tau> w x))) \<longleftrightarrow>
    (c211_rempty \<tau> w x \<or> (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x))"
proof -
  have inner: "(c211_patom pa_Ar Fst Snd paper_D \<tau> w (pc_enc \<tau> w y) \<and>
        c211_cleq \<tau> w (pc_enc \<tau> w y) (pc_enc \<tau> w x)) \<longleftrightarrow>
      (c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x)"
    if ym: "Elem y (raw_D \<tau> w)" for y
    by (simp only: c211_transfer_atom[OF ww ym] c211_transfer_leq[OF ww ym xm])
  have "(\<exists>y. Elem y (paper_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w y \<and>
        c211_cleq \<tau> w y (pc_enc \<tau> w x)) \<longleftrightarrow>
      (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w (pc_enc \<tau> w y) \<and>
        c211_cleq \<tau> w (pc_enc \<tau> w y) (pc_enc \<tau> w x))"
    by (rule c211_paper_D_exists)
  also have "\<dots> \<longleftrightarrow> (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x)"
    using inner by blast
  finally have ex: "(\<exists>y. Elem y (paper_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w y \<and>
        c211_cleq \<tau> w y (pc_enc \<tau> w x)) \<longleftrightarrow>
      (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x)" .
  show ?thesis by (simp only: ex c211_transfer_empty[OF ww xm])
qed

theorem c211_transfer_atomic:
  assumes ww: "Elem w raw_W"
  shows "c211_catomic \<tau> w \<longleftrightarrow> c211_ratomic \<tau> w"
proof -
  have "c211_catomic \<tau> w \<longleftrightarrow>
      (\<forall>x. Elem x (paper_D \<tau> w) \<longrightarrow> c211_cempty \<tau> w x \<or>
        (\<exists>y. Elem y (paper_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w y \<and>
          c211_cleq \<tau> w y x))"
    by (simp only: c211_patomic_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x. Elem x (raw_D \<tau> w) \<longrightarrow> c211_cempty \<tau> w (pc_enc \<tau> w x) \<or>
      (\<exists>y. Elem y (paper_D \<tau> w) \<and> c211_patom pa_Ar Fst Snd paper_D \<tau> w y \<and>
        c211_cleq \<tau> w y (pc_enc \<tau> w x)))"
    by (rule c211_paper_D_forall)
  also have "\<dots> \<longleftrightarrow> (\<forall>x. Elem x (raw_D \<tau> w) \<longrightarrow> c211_rempty \<tau> w x \<or>
      (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x))"
    using c211_transfer_atomic_point[OF ww] by blast
  also have "\<dots> \<longleftrightarrow> c211_ratomic \<tau> w"
    by (simp only: c211_ratomic_def)
  finally show ?thesis .
qed

subsection \<open>Completeness\<close>

lemma c211_transfer_lower_bound:
  assumes ww: "Elem w raw_W" and zm: "Elem z (raw_D \<tau> w)"
    and S: "S \<subseteq> explode (raw_D \<tau> w)"
  shows "(\<forall>y\<in>pc_enc \<tau> w ` S. c211_cleq \<tau> w (pc_enc \<tau> w z) y) \<longleftrightarrow>
    (\<forall>y\<in>S. c211_rleq \<tau> w z y)"
proof -
  have point: "c211_cleq \<tau> w (pc_enc \<tau> w z) (pc_enc \<tau> w y) \<longleftrightarrow> c211_rleq \<tau> w z y"
    if yS: "y \<in> S" for y
  proof -
    have ym: "Elem y (raw_D \<tau> w)" using S yS by (auto simp only: explode_Elem)
    show ?thesis by (rule c211_transfer_leq[OF ww zm ym])
  qed
  show ?thesis using point by auto
qed

lemma c211_transfer_complete_forward:
  assumes ww: "Elem w raw_W" and C: "c211_ccomplete \<tau> w"
  shows "c211_rcomplete \<tau> w"
  unfolding c211_rcomplete_def
proof (intro allI impI)
  fix S assume S: "S \<subseteq> explode (raw_D \<tau> w)"
  have S': "pc_enc \<tau> w ` S \<subseteq> explode (paper_D \<tau> w)"
  proof (rule subsetI)
    fix y assume "y \<in> pc_enc \<tau> w ` S"
    then obtain x where xS: "x \<in> S" and y: "y = pc_enc \<tau> w x" by blast
    have xm: "Elem x (raw_D \<tau> w)" using S xS by (auto simp only: explode_Elem)
    show "y \<in> explode (paper_D \<tau> w)" by (simp only: y explode_Elem pc_enc_type[OF xm])
  qed
  have ex: "\<exists>m'. Elem m' (paper_D \<tau> w) \<and> (\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow>
      ((\<forall>y\<in>pc_enc \<tau> w ` S. c211_cleq \<tau> w z y) \<longleftrightarrow> c211_cleq \<tau> w z m'))"
    by (rule C[unfolded c211_pcomplete_def, rule_format, OF S'])
  obtain m' where m'm: "Elem m' (paper_D \<tau> w)"
    and glb: "\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow>
      ((\<forall>y\<in>pc_enc \<tau> w ` S. c211_cleq \<tau> w z y) \<longleftrightarrow> c211_cleq \<tau> w z m')"
    using ex by (elim exE conjE) (rule that)
  obtain m where mm: "Elem m (raw_D \<tau> w)" and m': "m' = pc_enc \<tau> w m"
    using m'm unfolding pc_D_member by blast
  have point: "(\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow> c211_rleq \<tau> w z m"
    if zm: "Elem z (raw_D \<tau> w)" for z
  proof -
    have "(\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow>
        (\<forall>y\<in>pc_enc \<tau> w ` S. c211_cleq \<tau> w (pc_enc \<tau> w z) y)"
      by (rule sym[OF c211_transfer_lower_bound[OF ww zm S]])
    also have "\<dots> \<longleftrightarrow> c211_cleq \<tau> w (pc_enc \<tau> w z) m'"
      by (rule glb[rule_format, OF pc_enc_type[OF zm]])
    also have "\<dots> \<longleftrightarrow> c211_rleq \<tau> w z m"
      by (simp only: m' c211_transfer_leq[OF ww zm mm])
    finally show ?thesis .
  qed
  show "\<exists>m. Elem m (raw_D \<tau> w) \<and>
      (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow> ((\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow> c211_rleq \<tau> w z m))"
    by (rule exI[of _ m], rule conjI[OF mm], intro allI impI, erule point)
qed

lemma c211_paper_subset_image:
  assumes S': "S' \<subseteq> explode (paper_D \<tau> w)"
  shows "pc_enc \<tau> w ` {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'} = S'"
proof (rule set_eqI)
  fix y
  show "y \<in> pc_enc \<tau> w ` {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'} \<longleftrightarrow> y \<in> S'"
  proof
    assume "y \<in> pc_enc \<tau> w ` {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'}"
    then show "y \<in> S'" by blast
  next
    assume yS: "y \<in> S'"
    then have "Elem y (paper_D \<tau> w)" using S' by (auto simp only: explode_Elem)
    then obtain x where xm: "Elem x (raw_D \<tau> w)" and y: "y = pc_enc \<tau> w x"
      unfolding pc_D_member by blast
    have "x \<in> {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'}"
      using xm yS y by (simp add: explode_Elem)
    then show "y \<in> pc_enc \<tau> w ` {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'}"
      using y by blast
  qed
qed

lemma c211_transfer_complete_backward:
  assumes ww: "Elem w raw_W" and R: "c211_rcomplete \<tau> w"
  shows "c211_ccomplete \<tau> w"
  unfolding c211_pcomplete_def
proof (intro allI impI)
  fix S' assume S': "S' \<subseteq> explode (paper_D \<tau> w)"
  define S where "S = {x \<in> explode (raw_D \<tau> w). pc_enc \<tau> w x \<in> S'}"
  have S: "S \<subseteq> explode (raw_D \<tau> w)" by (auto simp: S_def)
  have image: "pc_enc \<tau> w ` S = S'"
    unfolding S_def by (rule c211_paper_subset_image[OF S'])
  have ex: "\<exists>m. Elem m (raw_D \<tau> w) \<and>
      (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow> ((\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow> c211_rleq \<tau> w z m))"
    by (rule R[unfolded c211_rcomplete_def, rule_format, OF S])
  obtain m where mm: "Elem m (raw_D \<tau> w)"
    and glb: "\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow> ((\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow> c211_rleq \<tau> w z m)"
    using ex by (elim exE conjE) (rule that)
  have point: "(\<forall>y\<in>S'. c211_cleq \<tau> w (pc_enc \<tau> w z) y) \<longleftrightarrow>
      c211_cleq \<tau> w (pc_enc \<tau> w z) (pc_enc \<tau> w m)"
    if zm: "Elem z (raw_D \<tau> w)" for z
  proof -
    have "(\<forall>y\<in>S'. c211_cleq \<tau> w (pc_enc \<tau> w z) y) \<longleftrightarrow> (\<forall>y\<in>S. c211_rleq \<tau> w z y)"
      by (simp only: image[symmetric] c211_transfer_lower_bound[OF ww zm S])
    also have "\<dots> \<longleftrightarrow> c211_rleq \<tau> w z m" by (rule glb[rule_format, OF zm])
    also have "\<dots> \<longleftrightarrow> c211_cleq \<tau> w (pc_enc \<tau> w z) (pc_enc \<tau> w m)"
      by (rule sym[OF c211_transfer_leq[OF ww zm mm]])
    finally show ?thesis .
  qed
  have all: "\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow>
      ((\<forall>y\<in>S'. c211_cleq \<tau> w z y) \<longleftrightarrow> c211_cleq \<tau> w z (pc_enc \<tau> w m))"
    unfolding c211_paper_D_forall by (intro allI impI) (erule point)
  show "\<exists>m'. Elem m' (paper_D \<tau> w) \<and>
      (\<forall>z. Elem z (paper_D \<tau> w) \<longrightarrow> ((\<forall>y\<in>S'. c211_cleq \<tau> w z y) \<longleftrightarrow> c211_cleq \<tau> w z m'))"
    by (rule exI[of _ "pc_enc \<tau> w m"], rule conjI[OF pc_enc_type[OF mm] all])
qed

theorem c211_transfer_complete:
  assumes ww: "Elem w raw_W"
  shows "c211_ccomplete \<tau> w \<longleftrightarrow> c211_rcomplete \<tau> w"
  using c211_transfer_complete_forward[OF ww] c211_transfer_complete_backward[OF ww] by blast

ML \<open>
  val facts = [@{thm c211_pc_enc_eq_iff}, @{thm c211_paper_D_forall}, @{thm c211_paper_D_exists},
    @{thm c211_arrow_arg_forall}, @{thm c211_transfer_leq_ind}, @{thm c211_transfer_leq_prop},
    @{thm c211_transfer_leq_arr}, @{thm c211_transfer_leq}, @{thm c211_transfer_empty_ind},
    @{thm c211_transfer_empty_prop}, @{thm c211_transfer_empty_arr}, @{thm c211_transfer_empty},
    @{thm c211_transfer_atom}, @{thm c211_transfer_atomic_point}, @{thm c211_transfer_atomic},
    @{thm c211_transfer_lower_bound}, @{thm c211_transfer_complete_forward},
    @{thm c211_paper_subset_image}, @{thm c211_transfer_complete_backward},
    @{thm c211_transfer_complete}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-TRANSFER: leq, empty, atom, atomic and complete transfer along pc_enc";
\<close>

end
