theory Classicism_2_11_World_Cases
  imports "Classicism_2_11.Typed_Paper_Model"
begin

section \<open>World and arrow bookkeeping for the concrete action model\<close>

text \<open>
  The concrete frame has a root, an intermediate world, a limit world
  reachable from it, and countably many leaves. The root reaches every
  world, the intermediate world reaches itself and the limit, and every
  other world reaches only itself. Arrows are ordered pairs with source
  Fst and target Snd. Each counterpart map along an arrow sends the
  source carrier onto the target carrier at every type.
\<close>

subsection \<open>Exhaustive world cases\<close>

theorem c211_world_cases:
  assumes ww: "Elem w raw_W"
  shows "w = raw_root \<or> w = raw_middle \<or> w = raw_limit \<or> (\<exists>n. w = raw_leaf n)"
proof -
  have codes: "Nat2nat w = 0 \<or> Nat2nat w = 1 \<or> Nat2nat w = 2 \<or> (\<exists>n. Nat2nat w = n + 3)"
    by presburger
  show ?thesis
    using codes raw_world_eq[OF ww raw_worlds(1)] raw_world_eq[OF ww raw_worlds(2)]
      raw_world_eq[OF ww raw_worlds(3)] raw_world_eq[OF ww raw_worlds(4)]
    by auto
qed

lemma c211_world_exhaust [consumes 1, case_names root middle limit leaf]:
  assumes "Elem w raw_W"
  obtains "w = raw_root" | "w = raw_middle" | "w = raw_limit" | n where "w = raw_leaf n"
  using c211_world_cases[OF assms] by blast

lemma c211_world_carriers:
  assumes ww: "Elem w raw_W"
  shows "raw_D a w = typed_R a \<or> raw_D a w = typed_S a \<or> raw_D a w = typed_M a"
  using ww
proof (cases rule: c211_world_exhaust)
  case root
  then show ?thesis by simp
next
  case middle
  then show ?thesis by simp
next
  case limit
  then show ?thesis by simp
next
  case (leaf n)
  then show ?thesis by simp
qed

subsection \<open>Identity arrows\<close>

lemma c211_identity_data [simp]: "Fst (pa_id w) = w" "Snd (pa_id w) = w"
  by (simp_all only: pa_id_def Fst Snd)

lemma c211_identity_arrow: "Elem w raw_W \<Longrightarrow> pa_id w \<in> explode pa_Ar"
  by (simp add: explode_Elem pa_id_def raw_rel_refl)

lemma c211_root_identity_arrow: "pa_id raw_root \<in> explode pa_Ar"
  by (rule c211_identity_arrow[OF raw_worlds(1)])

subsection \<open>Arrows by source\<close>

lemma c211_arrow_split:
  assumes "h \<in> explode pa_Ar"
  shows "h = Opair (Fst h) (Snd h)" "Elem (Fst h) raw_W" "Elem (Snd h) raw_W"
    "raw_rel (Fst h) (Snd h)"
proof -
  have arrow: "Elem h pa_Ar" using assms by (simp only: explode_Elem)
  show "h = Opair (Fst h) (Snd h)" by (rule sym[OF pa_arrow_data(4)[OF arrow]])
  show "Elem (Fst h) raw_W" by (rule pa_arrow_data(1)[OF arrow])
  show "Elem (Snd h) raw_W" by (rule pa_arrow_data(2)[OF arrow])
  show "raw_rel (Fst h) (Snd h)" by (rule pa_arrow_data(3)[OF arrow])
qed

theorem c211_root_arrows:
  assumes arrow: "h \<in> explode pa_Ar" and origin: "Fst h = raw_root"
  shows "h = Opair raw_root (Snd h) \<and> Elem (Snd h) raw_W"
  using c211_arrow_split[OF arrow] origin by simp

theorem c211_root_arrow_member:
  "Elem w raw_W \<Longrightarrow> Opair raw_root w \<in> explode pa_Ar"
  by (simp add: explode_Elem raw_rel_def)

theorem c211_outgoing_from_root:
  "h \<in> explode pa_Ar \<and> Fst h = raw_root \<longleftrightarrow> (\<exists>w. Elem w raw_W \<and> h = Opair raw_root w)"
  using c211_root_arrows c211_root_arrow_member by (auto simp: Fst)

theorem c211_outgoing_from_middle:
  "h \<in> explode pa_Ar \<and> Fst h = raw_middle \<longleftrightarrow>
    h = pa_id raw_middle \<or> h = Opair raw_middle raw_limit"
proof
  assume "h \<in> explode pa_Ar \<and> Fst h = raw_middle"
  then have arrow: "h \<in> explode pa_Ar" and origin: "Fst h = raw_middle" by blast+
  note split = c211_arrow_split[OF arrow]
  have "Snd h = raw_middle \<or> Snd h = raw_limit"
    using split(4) origin by (auto simp: raw_rel_def)
  then show "h = pa_id raw_middle \<or> h = Opair raw_middle raw_limit"
    using split(1) origin by (auto simp: pa_id_def)
next
  assume "h = pa_id raw_middle \<or> h = Opair raw_middle raw_limit"
  then show "h \<in> explode pa_Ar \<and> Fst h = raw_middle"
    by (auto simp: explode_Elem pa_id_def raw_rel_def Fst)
qed

theorem c211_outgoing_from_limit:
  "h \<in> explode pa_Ar \<and> Fst h = raw_limit \<longleftrightarrow> h = pa_id raw_limit"
proof
  assume "h \<in> explode pa_Ar \<and> Fst h = raw_limit"
  then have arrow: "h \<in> explode pa_Ar" and origin: "Fst h = raw_limit" by blast+
  note split = c211_arrow_split[OF arrow]
  have "Snd h = raw_limit" using split(4) origin by (auto simp: raw_rel_def)
  then show "h = pa_id raw_limit" using split(1) origin by (simp add: pa_id_def)
next
  assume "h = pa_id raw_limit"
  then show "h \<in> explode pa_Ar \<and> Fst h = raw_limit"
    by (simp add: c211_identity_arrow)
qed

theorem c211_outgoing_from_leaf:
  "h \<in> explode pa_Ar \<and> Fst h = raw_leaf n \<longleftrightarrow> h = pa_id (raw_leaf n)"
proof
  assume "h \<in> explode pa_Ar \<and> Fst h = raw_leaf n"
  then have arrow: "h \<in> explode pa_Ar" and origin: "Fst h = raw_leaf n" by blast+
  note split = c211_arrow_split[OF arrow]
  have "Snd h = raw_leaf n" using split(4) origin by (auto simp: raw_rel_def)
  then show "h = pa_id (raw_leaf n)" using split(1) origin by (simp add: pa_id_def)
next
  assume "h = pa_id (raw_leaf n)"
  then show "h \<in> explode pa_Ar \<and> Fst h = raw_leaf n"
    by (simp add: c211_identity_arrow)
qed

subsection \<open>Counterpart maps are onto along every arrow\<close>

lemma c211_paper_T_type:
  assumes arrow: "h \<in> explode pa_Ar" and xm: "Elem x (paper_D a (Fst h))"
  shows "Elem (paper_T a h x) (paper_D a (Snd h))"
proof -
  note split = c211_arrow_split[OF arrow]
  obtain x' where x'm: "Elem x' (raw_D a (Fst h))" and x: "x = pc_enc a (Fst h) x'"
    using xm unfolding pc_D_member by blast
  have "paper_T a h x = pc_enc a (Snd h) (raw_T a (Fst h) (Snd h) x')"
    by (subst split(1), simp only: x pc_T_enc[OF split(2) x'm])
  then show ?thesis
    by (simp only: pc_enc_type[OF raw_T_type[OF split(2,3,4) x'm]])
qed

theorem c211_raw_T_onto_arrows:
  assumes arrow: "h \<in> explode pa_Ar" and ym: "Elem y (paper_D a (Snd h))"
  shows "\<exists>x. Elem x (paper_D a (Fst h)) \<and> paper_T a h x = y"
proof -
  note split = c211_arrow_split[OF arrow]
  obtain y' where y'm: "Elem y' (raw_D a (Snd h))" and y: "y = pc_enc a (Snd h) y'"
    using ym unfolding pc_D_member by blast
  obtain x' where x'm: "Elem x' (raw_D a (Fst h))" and x'y': "raw_T a (Fst h) (Snd h) x' = y'"
    using raw_T_onto[OF split(2,3,4) y'm] by blast
  have image: "paper_T a h (pc_enc a (Fst h) x') = y"
    by (subst split(1), simp only: pc_T_enc[OF split(2) x'm] x'y' y)
  show ?thesis by (rule exI[of _ "pc_enc a (Fst h) x'"], rule conjI[OF pc_enc_type[OF x'm] image])
qed

theorem c211_paper_T_image:
  assumes arrow: "h \<in> explode pa_Ar"
  shows "paper_T a h ` explode (paper_D a (Fst h)) = explode (paper_D a (Snd h))"
proof (rule set_eqI)
  fix y
  show "y \<in> paper_T a h ` explode (paper_D a (Fst h)) \<longleftrightarrow> y \<in> explode (paper_D a (Snd h))"
    using c211_paper_T_type[OF arrow] c211_raw_T_onto_arrows[OF arrow, of y a]
    by (auto simp: explode_Elem)
qed

ML \<open>
  val facts = [@{thm c211_world_cases}, @{thm c211_world_exhaust}, @{thm c211_world_carriers},
    @{thm c211_identity_data(1)}, @{thm c211_identity_data(2)}, @{thm c211_identity_arrow},
    @{thm c211_root_identity_arrow}, @{thm c211_root_arrows}, @{thm c211_root_arrow_member},
    @{thm c211_outgoing_from_root}, @{thm c211_outgoing_from_middle},
    @{thm c211_outgoing_from_limit}, @{thm c211_outgoing_from_leaf},
    @{thm c211_paper_T_type}, @{thm c211_raw_T_onto_arrows}, @{thm c211_paper_T_image}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-WORLD-CASES: concrete worlds, arrows, and onto counterpart maps";
\<close>

end
