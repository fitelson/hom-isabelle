theory Classicism_2_11_Rigidity_Transfer
  imports "Classicism_2_11_Raw_Rigidity.Classicism_2_11_Raw_Rigidity"
    "Classicism_2_11_Transfer.Classicism_2_11_Transfer"
begin

section \<open>Rigid Comprehension fails in the arrow-coded paper model\<close>

text \<open>
  The paper-level readings c211_pcur, c211_prigid and c211_pRC are
  instantiated with the concrete arrows pa_Ar, identities pa_id, carriers
  paper_D and counterpart maps paper_T. Every carrier element is the
  encoding pc_enc of a raw object, arrows out of a world w are the pairs
  (w,v) with raw_rel w v, and encoding commutes with application,
  counterparts and the order. So current truth, rigidity and the order
  transfer to their raw readings, and the raw failure of Rigid
  Comprehension at type t→t (c211_raw_rigid_A0_fails) yields the
  failure of the paper reading at the root.
\<close>

subsection \<open>Small logical congruences\<close>

lemma c211_all_cong:
  assumes "\<And>z. A z \<Longrightarrow> (B z \<longleftrightarrow> C z)"
  shows "(\<forall>z. A z \<longrightarrow> B z) \<longleftrightarrow> (\<forall>z. A z \<longrightarrow> C z)"
  using assms by blast

lemma c211_all2_cong:
  assumes "\<And>v x. A v \<Longrightarrow> B v x \<Longrightarrow> (P v x \<longleftrightarrow> Q v x)" and "\<And>v. C v"
  shows "(\<forall>v x. A v \<longrightarrow> C v \<longrightarrow> B v x \<longrightarrow> P v x) \<longleftrightarrow> (\<forall>v x. A v \<longrightarrow> B v x \<longrightarrow> Q v x)"
  using assms by blast

lemma c211_arrow_forall:
  assumes ww: "Elem w raw_W"
  shows "(\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> P (Snd i) i) \<longleftrightarrow>
    (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> P v (Opair w v))"
proof
  assume L: "\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> P (Snd i) i"
  show "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> P v (Opair w v)"
  proof (intro allI impI)
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    have arrow: "Opair w v \<in> explode pa_Ar"
      by (simp only: explode_Elem pa_arrow_pair ww vw wv simp_thms)
    have "P (Snd (Opair w v)) (Opair w v)" by (rule L[rule_format, OF arrow Fst])
    then show "P v (Opair w v)" by (simp only: Snd)
  qed
next
  assume R: "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> P v (Opair w v)"
  show "\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = w \<longrightarrow> P (Snd i) i"
  proof (intro allI impI)
    fix i assume arrow: "i \<in> explode pa_Ar" and source: "Fst i = w"
    note split = c211_arrow_split[OF arrow]
    have rel: "raw_rel w (Snd i)" using split(4) source by simp
    have i: "Opair w (Snd i) = i" using split(1) source by simp
    have "P (Snd i) (Opair w (Snd i))" using R split(3) rel by blast
    then show "P (Snd i) i" by (simp only: i)
  qed
qed

subsection \<open>R1: current truth\<close>

lemma c211_pcur_enc:
  assumes ww: "Elem w raw_W" and zm: "Elem z (raw_D Prop w)"
  shows "c211_pcur pa_id w (pc_enc (Arr Prop Prop) w F) (pc_enc Prop w z) \<longleftrightarrow>
    raw_truth w (raw_app Prop Prop w F z)"
proof -
  have "app (pc_enc (Arr Prop Prop) w F) (Opair (pa_id w) (pc_enc Prop w z)) =
      pc_enc Prop w (raw_app Prop Prop w F z)"
    using pc_enc_app[OF ww ww raw_rel_refl zm, where b=Prop and F=F]
    by (simp only: pa_id_def raw_T_id)
  then show ?thesis by (simp only: c211_pcur_def pc_prop_truth[OF ww])
qed

theorem c211_pcur_transfer:
  assumes "Elem w raw_W" "Elem F (raw_D (Arr Prop Prop) w)" "Elem z (raw_D Prop w)"
  shows "c211_pcur pa_id w (pc_enc (Arr Prop Prop) w F) (pc_enc Prop w z) \<longleftrightarrow>
    raw_truth w (raw_app Prop Prop w F z)"
  by (rule c211_pcur_enc[OF assms(1,3)])

subsection \<open>R2: rigidity\<close>

lemma c211_rigid_inner:
  assumes vW: "Elem v raw_W" and Xm: "Elem X (raw_D (Arr Prop Prop) v)"
    and zm: "Elem z (raw_D Prop v)"
  shows "(\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = v \<longrightarrow>
      c211_pcur pa_id (Snd i) (paper_T (Arr Prop Prop) i (pc_enc (Arr Prop Prop) v X))
        (paper_T Prop i (pc_enc Prop v z))) \<longleftrightarrow>
    (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow>
      raw_truth u (raw_app Prop Prop u (raw_T (Arr Prop Prop) v u X) (raw_T Prop v u z)))"
proof -
  have point: "c211_pcur pa_id u (paper_T (Arr Prop Prop) (Opair v u) (pc_enc (Arr Prop Prop) v X))
        (paper_T Prop (Opair v u) (pc_enc Prop v z)) \<longleftrightarrow>
      raw_truth u (raw_app Prop Prop u (raw_T (Arr Prop Prop) v u X) (raw_T Prop v u z))"
    if uW: "Elem u raw_W" and vu: "raw_rel v u" for u
    by (simp only: pc_T_enc[OF vW Xm] pc_T_enc[OF vW zm]
        c211_pcur_enc[OF uW raw_T_type[OF vW uW vu zm]])
  show ?thesis
    by (simp only: c211_arrow_forall[OF vW, where P="\<lambda>u i. c211_pcur pa_id u
        (paper_T (Arr Prop Prop) i (pc_enc (Arr Prop Prop) v X)) (paper_T Prop i (pc_enc Prop v z))"])
      (use point in blast)
qed

lemma c211_rigid_point:
  assumes Ym: "Elem Y (raw_D (Arr Prop Prop) raw_root)" and vW: "Elem v raw_W"
    and Xm: "Elem X (raw_D (Arr Prop Prop) v)"
  shows "((\<forall>z. Elem z (paper_D Prop v) \<longrightarrow>
        c211_pcur pa_id v (paper_T (Arr Prop Prop) (Opair raw_root v)
          (pc_enc (Arr Prop Prop) raw_root Y)) z \<longrightarrow>
        (\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = v \<longrightarrow>
          c211_pcur pa_id (Snd i) (paper_T (Arr Prop Prop) i (pc_enc (Arr Prop Prop) v X))
            (paper_T Prop i z))) \<longleftrightarrow>
      c211_pleq pa_Ar Fst Snd paper_D (Arr Prop Prop) v
        (paper_T (Arr Prop Prop) (Opair raw_root v) (pc_enc (Arr Prop Prop) raw_root Y))
        (pc_enc (Arr Prop Prop) v X)) \<longleftrightarrow>
    ((\<forall>z. Elem z (raw_D Prop v) \<longrightarrow>
        raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_root v Y) z) \<longrightarrow>
        (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow>
          raw_truth u (raw_app Prop Prop u (raw_T (Arr Prop Prop) v u X) (raw_T Prop v u z)))) \<longleftrightarrow>
      c211_rleq (Arr Prop Prop) v (raw_T (Arr Prop Prop) raw_root v Y) X)"
proof -
  let ?Yv = "raw_T (Arr Prop Prop) raw_root v Y"
  have Yv: "Elem ?Yv (raw_D (Arr Prop Prop) v)"
    by (rule raw_T_type[OF raw_worlds(1) vW c211_root_rel Ym])
  have T: "paper_T (Arr Prop Prop) (Opair raw_root v) (pc_enc (Arr Prop Prop) raw_root Y) =
      pc_enc (Arr Prop Prop) v ?Yv"
    by (rule pc_T_enc[OF raw_worlds(1) Ym])
  have leq: "c211_pleq pa_Ar Fst Snd paper_D (Arr Prop Prop) v (pc_enc (Arr Prop Prop) v ?Yv)
      (pc_enc (Arr Prop Prop) v X) \<longleftrightarrow> c211_rleq (Arr Prop Prop) v ?Yv X"
    by (rule c211_transfer_leq[OF vW Yv Xm])
  have pt: "(c211_pcur pa_id v (pc_enc (Arr Prop Prop) v ?Yv) (pc_enc Prop v z) \<longrightarrow>
        (\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = v \<longrightarrow>
          c211_pcur pa_id (Snd i) (paper_T (Arr Prop Prop) i (pc_enc (Arr Prop Prop) v X))
            (paper_T Prop i (pc_enc Prop v z)))) \<longleftrightarrow>
      (raw_truth v (raw_app Prop Prop v ?Yv z) \<longrightarrow>
        (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow>
          raw_truth u (raw_app Prop Prop u (raw_T (Arr Prop Prop) v u X) (raw_T Prop v u z))))"
    if zm: "Elem z (raw_D Prop v)" for z
    by (simp only: c211_pcur_enc[OF vW zm] c211_rigid_inner[OF vW Xm zm])
  show ?thesis
    by (simp only: T leq c211_paper_D_forall c211_all_cong[OF pt])
qed

theorem c211_prigid_transfer:
  assumes Ym: "Elem Y (typed_R (Arr Prop Prop))"
  shows "c211_prigid pa_Ar Fst Snd pa_id paper_D paper_T raw_root
      (pc_enc (Arr Prop Prop) raw_root Y) \<longleftrightarrow> c211_rrigid Y"
proof -
  have YD: "Elem Y (raw_D (Arr Prop Prop) raw_root)" using Ym by simp
  define P where "P = (\<lambda>V h X.
    (\<forall>z. Elem z (paper_D Prop V) \<longrightarrow>
        c211_pcur pa_id V (paper_T (Arr Prop Prop) h (pc_enc (Arr Prop Prop) raw_root Y)) z \<longrightarrow>
        (\<forall>i. i \<in> explode pa_Ar \<longrightarrow> Fst i = V \<longrightarrow>
          c211_pcur pa_id (Snd i) (paper_T (Arr Prop Prop) i X) (paper_T Prop i z))) \<longleftrightarrow>
      c211_pleq pa_Ar Fst Snd paper_D (Arr Prop Prop) V
        (paper_T (Arr Prop Prop) h (pc_enc (Arr Prop Prop) raw_root Y)) X)"
  have "c211_prigid pa_Ar Fst Snd pa_id paper_D paper_T raw_root
      (pc_enc (Arr Prop Prop) raw_root Y) \<longleftrightarrow>
    (\<forall>i x. i \<in> explode pa_Ar \<longrightarrow> Fst i = raw_root \<longrightarrow>
      Elem x (paper_D (Arr Prop Prop) (Snd i)) \<longrightarrow> P (Snd i) i x)"
    by (unfold c211_prigid_def P_def) (rule refl)
  also have "\<dots> \<longleftrightarrow> (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      Elem x (raw_D (Arr Prop Prop) v) \<longrightarrow> P v (Opair raw_root v) (pc_enc (Arr Prop Prop) v x))"
    by (rule c211_arrow_arg_forall[OF raw_worlds(1)])
  also have "\<dots> \<longleftrightarrow> c211_rrigid Y"
    unfolding P_def c211_rrigid_def
    by (rule c211_all2_cong, rule c211_rigid_point[OF YD], assumption, assumption,
        rule c211_root_rel)
  finally show ?thesis .
qed

subsection \<open>R3: the paper reading of Rigid Comprehension fails at the root\<close>

lemma c211_rcur1_eqI:
  assumes same: "\<And>z. Elem z (raw_D Prop w) \<Longrightarrow>
    raw_truth w (raw_app Prop Prop w F z) \<longleftrightarrow> raw_truth w (raw_app Prop Prop w G z)"
  shows "c211_rcur [Prop] w F = c211_rcur [Prop] w G"
proof (rule set_eqI)
  fix xs
  show "xs \<in> c211_rcur [Prop] w F \<longleftrightarrow> xs \<in> c211_rcur [Prop] w G"
  proof (cases "xs \<in> c211_tuples [Prop] w")
    case True
    then obtain z ys where xs: "xs = z # ys" and zm: "Elem z (raw_D Prop w)"
      and ys: "ys \<in> c211_tuples [] w"
      unfolding c211_tuples_Cons by blast
    have "ys = []" using ys by simp
    then show ?thesis using same[OF zm] zm by (simp add: xs c211_cur1)
  next
    case False
    then show ?thesis using c211_rcur_tuples by blast
  qed
qed

theorem c211_concrete_pRC_false:
  "\<not> c211_pRC pa_Ar Fst Snd pa_id paper_D paper_T raw_root"
proof
  assume RC: "c211_pRC pa_Ar Fst Snd pa_id paper_D paper_T raw_root"
  let ?x = "pc_enc (Arr Prop Prop) raw_root c211_X0"
  have X0: "Elem c211_X0 (raw_D (Arr Prop Prop) raw_root)"
    using c211_X0_data by simp
  have xm: "Elem ?x (paper_D (Arr Prop Prop) raw_root)" by (rule pc_enc_type[OF X0])
  obtain y where ym: "Elem y (paper_D (Arr Prop Prop) raw_root)"
    and ry: "c211_prigid pa_Ar Fst Snd pa_id paper_D paper_T raw_root y"
    and co: "\<forall>z. Elem z (paper_D Prop raw_root) \<longrightarrow>
      (c211_pcur pa_id raw_root ?x z \<longleftrightarrow> c211_pcur pa_id raw_root y z)"
    using RC[unfolded c211_pRC_def, rule_format, OF xm] by blast
  obtain Y where YD: "Elem Y (raw_D (Arr Prop Prop) raw_root)"
    and y: "y = pc_enc (Arr Prop Prop) raw_root Y"
    using ym unfolding pc_D_member by blast
  have YR: "Elem Y (typed_R (Arr Prop Prop))" using YD by simp
  have "c211_rcur [Prop] raw_root c211_X0 = c211_rcur [Prop] raw_root Y"
  proof (rule c211_rcur1_eqI)
    fix z assume zm: "Elem z (raw_D Prop raw_root)"
    have "c211_pcur pa_id raw_root ?x (pc_enc Prop raw_root z) \<longleftrightarrow>
        c211_pcur pa_id raw_root y (pc_enc Prop raw_root z)"
      using co pc_enc_type[OF zm] by blast
    then show "raw_truth raw_root (raw_app Prop Prop raw_root c211_X0 z) \<longleftrightarrow>
        raw_truth raw_root (raw_app Prop Prop raw_root Y z)"
      by (simp only: y c211_pcur_enc[OF raw_worlds(1) zm])
  qed
  then have "c211_rcur [Prop] raw_root Y = c211_A0" using c211_X0_data by simp
  then have "\<not> c211_rrigid Y" by (rule c211_raw_rigid_A0_fails[OF YR])
  moreover have "c211_rrigid Y" using ry by (simp only: y c211_prigid_transfer[OF YR])
  ultimately show False by blast
qed

ML \<open>
  val facts = [@{thm c211_arrow_forall}, @{thm c211_pcur_enc}, @{thm c211_pcur_transfer},
    @{thm c211_rigid_inner}, @{thm c211_rigid_point}, @{thm c211_prigid_transfer},
    @{thm c211_rcur1_eqI}, @{thm c211_concrete_pRC_false}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-RIGIDITY-TRANSFER: the paper reading of Rigid Comprehension at type t→t fails at the root";
\<close>

end
