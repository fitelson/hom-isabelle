theory Classicism_2_11_Raw_Rigidity
  imports "Classicism_2_11_Lattice.Classicism_2_11_Realization" "Classicism_2_11_Lattice.Classicism_2_11_Raw_Order"
begin

section \<open>Raw failure of Rigid Comprehension at type t→t\<close>

text \<open>
  The source's one-formula reading of Rigid at type t→t, evaluated at the
  root, is
  Rigid Y := □∀X((∀z(Yz → □Xz)) ↔ Y ≤ X).
  Its raw reading c211_rrigid quantifies the outer □ over every world w
  (all worlds are accessible from the root), ∀X over raw_D (t→t) w, and the
  inner □ over the worlds v with raw_rel w v.

  Let a0 be the intermediate proposition (False, False) and A0 the set of
  singleton tuples of root propositions whose intermediate image is a0.
  No Y of type t→t whose current root relation is A0 is Rigid:
  \<^item> Persistence: taking X := Y, reflexivity of ≤ makes Y true at every
    world of every transported z ∈ A0. The propositions (False, False, ∅)
    and (False, False, {n}) both lie in A0, since a finite set is not
    ultrafilter-large, and they take both bit values at leaf n. Hence
    every leaf image of Y is the full relation, and so is its limit image.
  \<^item> Root inextensibility: X := B, the root object with relation A0, whose
    intermediate image has relation {[a0]} and whose terminal images are
    full, makes the left side true. Hence Y ≤ B, so the intermediate
    relation of Y is included in {[a0]}.
  \<^item> At the intermediate world, X := H, the object with relation {[a0]}
    whose limit image is the haecceity of the false bit. The left side
    holds, hence the limit image of Y is included in that singleton,
    contradicting fullness.
\<close>

definition c211_rrigid :: "ZF \<Rightarrow> bool" where
  "c211_rrigid Y \<longleftrightarrow> (\<forall>w X. Elem w raw_W \<longrightarrow> Elem X (raw_D (Arr Prop Prop) w) \<longrightarrow>
    ((\<forall>z. Elem z (raw_D Prop w) \<longrightarrow>
        raw_truth w (raw_app Prop Prop w (raw_T (Arr Prop Prop) raw_root w Y) z) \<longrightarrow>
       (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow>
         raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) w v X) (raw_T Prop w v z))))
    \<longleftrightarrow> c211_rleq (Arr Prop Prop) w (raw_T (Arr Prop Prop) raw_root w Y) X))"

subsection \<open>Ingredients\<close>

definition c211_a0 :: ZF where "c211_a0 = zmiddle (False, False)"

definition c211_A0 :: "ZF list set" where
  "c211_A0 = {xs. \<exists>a. xs = [a] \<and> Elem a (typed_R Prop) \<and> typed_rs Prop a = c211_a0}"

text \<open>Constant and haecceity relations at a terminal world.\<close>

definition c211_tt_const :: "bool \<Rightarrow> ZF" where
  "c211_tt_const b = Lambda typed_two (\<lambda>x. zbit b)"

definition c211_tt_haec :: ZF where
  "c211_tt_haec = Lambda typed_two (\<lambda>x. zbit (x = zbit False))"

lemma c211_tt_const_fun: "Elem (c211_tt_const b) (Fun typed_two typed_two)"
  by (simp add: c211_tt_const_def Elem_Lambda_Fun)

lemma c211_tt_const_type: "Elem (c211_tt_const b) (typed_M (Arr Prop Prop))"
  by (simp only: typed_M.simps c211_tt_const_fun)

lemma c211_tt_const_app: "Elem x typed_two \<Longrightarrow> app (c211_tt_const b) x = zbit b"
  by (simp add: c211_tt_const_def Lambda_app)

lemma c211_tt_haec_type: "Elem c211_tt_haec (typed_M (Arr Prop Prop))"
  by (simp add: c211_tt_haec_def Elem_Lambda_Fun)

lemma c211_tt_haec_false: "app c211_tt_haec (zbit False) = zbit True"
  by (simp add: c211_tt_haec_def Lambda_app)

lemma c211_tt_haec_true: "app c211_tt_haec (zbit True) = zbit False"
  by (simp add: c211_tt_haec_def Lambda_app)

text \<open>Realized intermediate and root objects of type t→t.\<close>

definition c211_mid_obj :: "ZF list set \<Rightarrow> ZF \<Rightarrow> ZF" where
  "c211_mid_obj R U = (SOME S. Elem S (typed_S (Arr Prop Prop)) \<and>
    c211_rcur [Prop] raw_middle S = R \<and> typed_j (Arr Prop Prop) S = U)"

definition c211_root_obj :: "ZF list set \<Rightarrow> ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "c211_root_obj R S N = (SOME X. Elem X (typed_R (Arr Prop Prop)) \<and>
    c211_rcur [Prop] raw_root X = R \<and> typed_rs (Arr Prop Prop) X = S \<and>
    (\<forall>n. typed_rn (Arr Prop Prop) X n = N n))"

lemma c211_mid_obj:
  assumes R: "R \<subseteq> c211_tuples [Prop] raw_middle" and U: "Elem U (typed_M (Arr Prop Prop))"
  shows "Elem (c211_mid_obj R U) (typed_S (Arr Prop Prop)) \<and>
    c211_rcur [Prop] raw_middle (c211_mid_obj R U) = R \<and>
    typed_j (Arr Prop Prop) (c211_mid_obj R U) = U"
proof -
  have U': "Elem U (typed_M (paper_type_vector [Prop] Prop))"
    by (simp only: paper_type_vector.simps U)
  have ex: "\<exists>S. Elem S (typed_S (Arr Prop Prop)) \<and>
      c211_rcur [Prop] raw_middle S = R \<and> typed_j (Arr Prop Prop) S = U"
    using c211_middle_realize[OF R U'] by (simp only: paper_type_vector.simps)
  show ?thesis unfolding c211_mid_obj_def by (rule someI_ex[OF ex])
qed

lemma c211_root_obj:
  assumes R: "R \<subseteq> c211_tuples [Prop] raw_root"
    and S: "Elem S (typed_S (Arr Prop Prop))"
    and N: "\<And>n. Elem (N n) (typed_M (Arr Prop Prop))"
    and compat: "typed_j (Arr Prop Prop) S = ulim N"
  shows "Elem (c211_root_obj R S N) (typed_R (Arr Prop Prop)) \<and>
    c211_rcur [Prop] raw_root (c211_root_obj R S N) = R \<and>
    typed_rs (Arr Prop Prop) (c211_root_obj R S N) = S \<and>
    (\<forall>n. typed_rn (Arr Prop Prop) (c211_root_obj R S N) n = N n)"
proof -
  have S': "Elem S (typed_S (paper_type_vector [Prop] Prop))"
    by (simp only: paper_type_vector.simps S)
  have N': "Elem (N n) (typed_M (paper_type_vector [Prop] Prop))" for n
    by (simp only: paper_type_vector.simps N)
  have compat': "typed_j (paper_type_vector [Prop] Prop) S = ulim N"
    by (simp only: paper_type_vector.simps compat)
  have ex: "\<exists>X. Elem X (typed_R (Arr Prop Prop)) \<and>
      c211_rcur [Prop] raw_root X = R \<and> typed_rs (Arr Prop Prop) X = S \<and>
      (\<forall>n. typed_rn (Arr Prop Prop) X n = N n)"
    using c211_root_realize[OF R S' N' compat'] by (simp only: paper_type_vector.simps)
  show ?thesis unfolding c211_root_obj_def by (rule someI_ex[OF ex])
qed

subsection \<open>Current relations of type t→t\<close>

lemma c211_cur1:
  "[z] \<in> c211_rcur [Prop] w F \<longleftrightarrow>
    Elem z (raw_D Prop w) \<and> raw_truth w (raw_app Prop Prop w F z)"
  by (simp add: c211_rcur_Cons c211_rcur_Nil)

lemma c211_A0_iff: "[z] \<in> c211_A0 \<longleftrightarrow> Elem z (typed_R Prop) \<and> typed_rs Prop z = c211_a0"
  by (simp add: c211_A0_def)

lemma c211_A0_tuples: "c211_A0 \<subseteq> c211_tuples [Prop] raw_root"
  by (auto simp: c211_A0_def c211_tuples_def)

lemma c211_a0_middle: "Elem c211_a0 (raw_D Prop raw_middle)"
  by (simp only: raw_D_worlds c211_a0_def zmiddle_type)

lemma c211_a0_tuples: "{[c211_a0]} \<subseteq> c211_tuples [Prop] raw_middle"
  using c211_a0_middle by (simp add: c211_tuples_def)

lemma c211_tt_true_terminal:
  assumes w: "c211_terminal w" and xm: "Elem x (raw_D Prop w)"
  shows "raw_truth w (raw_app Prop Prop w (c211_tt_const True) x)"
proof -
  have x2: "Elem x typed_two" using xm by (simp only: c211_terminal_simps(1)[OF w] typed_M.simps)
  show ?thesis
    by (simp only: c211_terminal_simps(2,3)[OF w] c211_tt_const_app[OF x2] bit_dec_zbit)
qed

lemma c211_rr_refl: "c211_rleq \<tau> w x x"
  by (induction \<tau> arbitrary: w x) simp_all

lemma c211_ubit_singleton: "\<not> ubit {n}"
  using ubit_cofinite[of "{n}"] by simp

lemma c211_zprop_a0:
  "typed_rs Prop (zprop (False, False, {})) = c211_a0"
  "typed_rs Prop (zprop (False, False, {n})) = c211_a0"
  by (simp_all only: typed_rs_zprop to_middle_triple ubit_empty c211_ubit_singleton c211_a0_def)

subsection \<open>The witness X0 and the auxiliary objects\<close>

definition c211_S0 :: ZF where "c211_S0 = c211_mid_obj {} (c211_tt_const False)"

definition c211_X0 :: ZF where
  "c211_X0 = c211_root_obj c211_A0 c211_S0 (\<lambda>n. c211_tt_const False)"

definition c211_SB :: ZF where "c211_SB = c211_mid_obj {[c211_a0]} (c211_tt_const True)"

definition c211_B :: ZF where
  "c211_B = c211_root_obj c211_A0 c211_SB (\<lambda>n. c211_tt_const True)"

definition c211_H :: ZF where "c211_H = c211_mid_obj {[c211_a0]} c211_tt_haec"

lemma c211_S0_data:
  "Elem c211_S0 (typed_S (Arr Prop Prop)) \<and> c211_rcur [Prop] raw_middle c211_S0 = {} \<and>
    typed_j (Arr Prop Prop) c211_S0 = c211_tt_const False"
  unfolding c211_S0_def by (rule c211_mid_obj[OF empty_subsetI c211_tt_const_type])

lemma c211_X0_data:
  "Elem c211_X0 (typed_R (Arr Prop Prop)) \<and> c211_rcur [Prop] raw_root c211_X0 = c211_A0 \<and>
    typed_rs (Arr Prop Prop) c211_X0 = c211_S0 \<and>
    (\<forall>n. typed_rn (Arr Prop Prop) c211_X0 n = c211_tt_const False)"
proof -
  have compat: "typed_j (Arr Prop Prop) c211_S0 = ulim (\<lambda>n. c211_tt_const False)"
    using c211_S0_data by (simp only: ulim_const)
  show ?thesis unfolding c211_X0_def
    by (rule c211_root_obj[OF c211_A0_tuples conjunct1[OF c211_S0_data] c211_tt_const_type compat])
qed

lemma c211_SB_data:
  "Elem c211_SB (typed_S (Arr Prop Prop)) \<and> c211_rcur [Prop] raw_middle c211_SB = {[c211_a0]} \<and>
    typed_j (Arr Prop Prop) c211_SB = c211_tt_const True"
  unfolding c211_SB_def by (rule c211_mid_obj[OF c211_a0_tuples c211_tt_const_type])

lemma c211_B_data:
  "Elem c211_B (typed_R (Arr Prop Prop)) \<and> c211_rcur [Prop] raw_root c211_B = c211_A0 \<and>
    typed_rs (Arr Prop Prop) c211_B = c211_SB \<and>
    (\<forall>n. typed_rn (Arr Prop Prop) c211_B n = c211_tt_const True)"
proof -
  have compat: "typed_j (Arr Prop Prop) c211_SB = ulim (\<lambda>n. c211_tt_const True)"
    using c211_SB_data by (simp only: ulim_const)
  show ?thesis unfolding c211_B_def
    by (rule c211_root_obj[OF c211_A0_tuples conjunct1[OF c211_SB_data] c211_tt_const_type compat])
qed

lemma c211_H_data:
  "Elem c211_H (typed_S (Arr Prop Prop)) \<and> c211_rcur [Prop] raw_middle c211_H = {[c211_a0]} \<and>
    typed_j (Arr Prop Prop) c211_H = c211_tt_haec"
  unfolding c211_H_def by (rule c211_mid_obj[OF c211_a0_tuples c211_tt_haec_type])

subsection \<open>No Y with root relation A0 is Rigid\<close>

context
  fixes Y :: ZF
  assumes Ym: "Elem Y (typed_R (Arr Prop Prop))"
    and cur: "c211_rcur [Prop] raw_root Y = c211_A0"
    and rig: "c211_rrigid Y"
begin

lemma c211_rr_Y_root: "Elem Y (raw_D (Arr Prop Prop) raw_root)"
  by (simp only: raw_D_worlds Ym)

lemma c211_rr_root_truth:
  assumes zr: "Elem z (raw_D Prop raw_root)"
    and tz: "raw_truth raw_root (raw_app Prop Prop raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) z)"
  shows "Elem z (typed_R Prop) \<and> typed_rs Prop z = c211_a0"
proof -
  have "[z] \<in> c211_rcur [Prop] raw_root Y" using zr tz unfolding raw_T_id c211_cur1 by blast
  then show ?thesis by (simp only: cur c211_A0_iff)
qed

text \<open>Step 1: persistence along every arrow out of the root.\<close>

lemma c211_rr_persist:
  assumes zR: "Elem z (typed_R Prop)" and zs: "typed_rs Prop z = c211_a0" and vW: "Elem v raw_W"
  shows "raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_root v Y) (raw_T Prop raw_root v z))"
proof -
  have rhs: "c211_rleq (Arr Prop Prop) raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) Y"
    by (simp only: raw_T_id c211_rr_refl)
  have lhs: "\<forall>z. Elem z (raw_D Prop raw_root) \<longrightarrow>
      raw_truth raw_root (raw_app Prop Prop raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) z) \<longrightarrow>
      (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
        raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_root v Y) (raw_T Prop raw_root v z)))"
    by (rule iffD2[OF rig[unfolded c211_rrigid_def, rule_format, OF raw_worlds(1) c211_rr_Y_root] rhs])
  have zr: "Elem z (raw_D Prop raw_root)" by (simp only: raw_D_worlds zR)
  have "[z] \<in> c211_rcur [Prop] raw_root Y" by (simp only: cur c211_A0_iff zR zs simp_thms)
  then have tz: "raw_truth raw_root (raw_app Prop Prop raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) z)"
    unfolding raw_T_id c211_cur1 by blast
  have rel: "raw_rel raw_root v" by (simp add: raw_rel_def)
  show ?thesis by (rule lhs[rule_format, OF zr tz vW rel])
qed

lemma c211_rr_leaf_value:
  assumes zs: "typed_rs Prop (zprop (False, False, S)) = c211_a0"
  shows "bit_dec (app (typed_rn (Arr Prop Prop) Y n) (zbit (n \<in> S)))"
  using c211_rr_persist[OF zprop_type zs raw_worlds(4)]
  by (simp only: c211_raw_T_root_leaf typed_rn_zprop snd_conv
      c211_terminal_simps(2,3)[OF c211_terminal_worlds(2)])

lemma c211_rr_leaf_full: "typed_rn (Arr Prop Prop) Y n = c211_tt_const True"
proof -
  have Yn: "Elem (typed_rn (Arr Prop Prop) Y n) (Fun typed_two typed_two)"
    using typed_rn_type[OF Ym, of n] by (simp only: typed_M.simps)
  have f: "bit_dec (app (typed_rn (Arr Prop Prop) Y n) (zbit False))"
    using c211_rr_leaf_value[OF c211_zprop_a0(1), of n] by (simp only: empty_iff)
  have t: "bit_dec (app (typed_rn (Arr Prop Prop) Y n) (zbit True))"
    using c211_rr_leaf_value[OF c211_zprop_a0(2)[of n], of n] by (simp only: singleton_iff simp_thms)
  show ?thesis
  proof (rule typed_graph_ext[OF Yn c211_tt_const_fun])
    fix x assume xm: "Elem x typed_two"
    obtain b where x: "x = zbit b" using zbit_surjective[OF xm] by blast
    have val: "Elem (app (typed_rn (Arr Prop Prop) Y n) x) typed_two"
      by (rule typed_graph_value[OF Yn xm])
    have bd: "bit_dec (app (typed_rn (Arr Prop Prop) Y n) x) = bit_dec (zbit True)"
      using f t by (cases b) (simp_all only: x bit_dec_zbit)
    show "app (typed_rn (Arr Prop Prop) Y n) x = app (c211_tt_const True) x"
      by (simp only: c211_tt_const_app[OF xm] raw_bit_separates[OF val zbit_type bd])
  qed
qed

lemma c211_rr_limit_full:
  "typed_j (Arr Prop Prop) (typed_rs (Arr Prop Prop) Y) = c211_tt_const True"
proof -
  have "typed_rn (Arr Prop Prop) Y = (\<lambda>n. c211_tt_const True)"
    by (rule ext) (rule c211_rr_leaf_full)
  then show ?thesis by (simp only: typed_R_compatible[OF Ym] ulim_const)
qed

text \<open>Step 2: root inextensibility against B.\<close>

lemma c211_rr_below_B: "c211_rleq (Arr Prop Prop) raw_root Y c211_B"
proof -
  note B = c211_B_data and SB = c211_SB_data
  have Br: "Elem c211_B (raw_D (Arr Prop Prop) raw_root)"
    by (simp only: raw_D_worlds conjunct1[OF B])
  have lhs: "\<forall>z. Elem z (raw_D Prop raw_root) \<longrightarrow>
      raw_truth raw_root (raw_app Prop Prop raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) z) \<longrightarrow>
      (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
        raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_root v c211_B) (raw_T Prop raw_root v z)))"
  proof (intro allI impI)
    fix z v
    assume zr: "Elem z (raw_D Prop raw_root)"
      and tz: "raw_truth raw_root (raw_app Prop Prop raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) z)"
      and vW: "Elem v raw_W" and rel: "raw_rel raw_root v"
    have zA: "Elem z (typed_R Prop) \<and> typed_rs Prop z = c211_a0"
      by (rule c211_rr_root_truth[OF zr tz])
    show "raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_root v c211_B) (raw_T Prop raw_root v z))"
      using vW
    proof (cases rule: c211_world_exhaust)
      case root
      have "[z] \<in> c211_rcur [Prop] raw_root c211_B" using B zA by (simp only: c211_A0_iff)
      then show ?thesis unfolding root raw_T_id c211_cur1 by blast
    next
      case middle
      have "[c211_a0] \<in> c211_rcur [Prop] raw_middle c211_SB" using SB by simp
      then have "raw_truth raw_middle (raw_app Prop Prop raw_middle c211_SB c211_a0)"
        unfolding c211_cur1 by blast
      then show ?thesis using B zA by (simp only: middle c211_raw_T_root_middle)
    next
      case limit
      have rl: "raw_rel raw_root raw_limit" by (simp add: raw_rel_def)
      show ?thesis
        unfolding limit c211_raw_T_root_limit[of "Arr Prop Prop"] conjunct1[OF conjunct2[OF conjunct2[OF B]]]
          conjunct2[OF conjunct2[OF SB]]
        by (rule c211_tt_true_terminal[OF c211_terminal_worlds(1)
              raw_T_type[OF raw_worlds(1) raw_worlds(3) rl zr]])
    next
      case (leaf n)
      have rl: "raw_rel raw_root (raw_leaf n)" by (simp add: raw_rel_def)
      show ?thesis
        unfolding leaf c211_raw_T_root_leaf[of "Arr Prop Prop"] conjunct2[OF conjunct2[OF conjunct2[OF B]], rule_format]
        by (rule c211_tt_true_terminal[OF c211_terminal_worlds(2)
              raw_T_type[OF raw_worlds(1) raw_worlds(4) rl zr]])
    qed
  qed
  have "c211_rleq (Arr Prop Prop) raw_root (raw_T (Arr Prop Prop) raw_root raw_root Y) c211_B"
    by (rule iffD1[OF rig[unfolded c211_rrigid_def, rule_format, OF raw_worlds(1) Br] lhs])
  then show ?thesis by (simp only: raw_T_id)
qed

lemma c211_rr_middle_only:
  assumes zm: "Elem z (raw_D Prop raw_middle)"
    and tz: "raw_truth raw_middle (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle Y) z)"
  shows "z = c211_a0"
proof -
  have rm: "raw_rel raw_root raw_middle" by (simp add: raw_rel_def)
  have p: "c211_rleq Prop raw_middle
      (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle Y) z)
      (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle c211_B) z)"
    by (rule c211_rr_below_B[unfolded c211_rleq.simps(3), rule_format, OF raw_worlds(2) rm zm])
  have "raw_truth raw_middle (raw_T Prop raw_middle raw_middle
      (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle c211_B) z))"
    by (rule p[unfolded c211_rleq.simps(2), rule_format, OF raw_worlds(2) raw_rel_refl])
      (simp only: raw_T_id tz)
  then have "raw_truth raw_middle (raw_app Prop Prop raw_middle c211_SB z)"
    using c211_B_data by (simp only: raw_T_id c211_raw_T_root_middle)
  then have "[z] \<in> c211_rcur [Prop] raw_middle c211_SB" using zm unfolding c211_cur1 by blast
  then show ?thesis using c211_SB_data by simp
qed

text \<open>Step 3: the outer □ at the intermediate world, against H.\<close>

lemma c211_rr_contradiction: False
proof -
  note H = c211_H_data
  have Hr: "Elem c211_H (raw_D (Arr Prop Prop) raw_middle)"
    by (simp only: raw_D_worlds conjunct1[OF H])
  have lhs: "\<forall>z. Elem z (raw_D Prop raw_middle) \<longrightarrow>
      raw_truth raw_middle (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle Y) z) \<longrightarrow>
      (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_middle v \<longrightarrow>
        raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_middle v c211_H) (raw_T Prop raw_middle v z)))"
  proof (intro allI impI)
    fix z v
    assume zm: "Elem z (raw_D Prop raw_middle)"
      and tz: "raw_truth raw_middle (raw_app Prop Prop raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle Y) z)"
      and vW: "Elem v raw_W" and rel: "raw_rel raw_middle v"
    have z: "z = c211_a0" by (rule c211_rr_middle_only[OF zm tz])
    have "v = raw_middle \<or> v = raw_limit" using rel by (auto simp: raw_rel_def)
    then show "raw_truth v (raw_app Prop Prop v (raw_T (Arr Prop Prop) raw_middle v c211_H) (raw_T Prop raw_middle v z))"
    proof
      assume v: "v = raw_middle"
      have "[c211_a0] \<in> c211_rcur [Prop] raw_middle c211_H" using H by simp
      then have "raw_truth raw_middle (raw_app Prop Prop raw_middle c211_H c211_a0)"
        unfolding c211_cur1 by blast
      then show ?thesis by (simp only: v z raw_T_id)
    next
      assume v: "v = raw_limit"
      show ?thesis using H
        by (simp only: v z c211_raw_T_middle_limit c211_a0_def typed_j_zmiddle snd_conv
            c211_terminal_simps(2,3)[OF c211_terminal_worlds(1)] c211_tt_haec_false bit_dec_zbit)
    qed
  qed
  have rhs: "c211_rleq (Arr Prop Prop) raw_middle (raw_T (Arr Prop Prop) raw_root raw_middle Y) c211_H"
    by (rule iffD1[OF rig[unfolded c211_rrigid_def, rule_format, OF raw_worlds(2) Hr] lhs])
  have ml: "raw_rel raw_middle raw_limit" by (simp add: raw_rel_def)
  have one: "Elem (zbit True) (raw_D Prop raw_limit)"
    by (simp only: raw_D_worlds typed_M.simps zbit_type)
  have p: "c211_rleq Prop raw_limit
      (raw_app Prop Prop raw_limit (raw_T (Arr Prop Prop) raw_middle raw_limit
        (raw_T (Arr Prop Prop) raw_root raw_middle Y)) (zbit True))
      (raw_app Prop Prop raw_limit (raw_T (Arr Prop Prop) raw_middle raw_limit c211_H) (zbit True))"
    by (rule rhs[unfolded c211_rleq.simps(3), rule_format, OF raw_worlds(3) ml one])
  have yes: "raw_truth raw_limit (raw_T Prop raw_limit raw_limit
      (raw_app Prop Prop raw_limit (raw_T (Arr Prop Prop) raw_middle raw_limit
        (raw_T (Arr Prop Prop) raw_root raw_middle Y)) (zbit True)))"
    by (simp only: raw_T_id c211_raw_T_middle_limit c211_raw_T_root_middle c211_rr_limit_full
        c211_terminal_simps(2,3)[OF c211_terminal_worlds(1)] c211_tt_const_app[OF zbit_type]
        bit_dec_zbit)
  have no: "\<not> raw_truth raw_limit (raw_T Prop raw_limit raw_limit
      (raw_app Prop Prop raw_limit (raw_T (Arr Prop Prop) raw_middle raw_limit c211_H) (zbit True)))"
    using H by (simp only: raw_T_id c211_raw_T_middle_limit
        c211_terminal_simps(2,3)[OF c211_terminal_worlds(1)] c211_tt_haec_true bit_dec_zbit
        simp_thms)
  show False
    using p[unfolded c211_rleq.simps(2), rule_format, OF raw_worlds(3) raw_rel_refl yes] no by blast
qed

end

theorem c211_raw_rigid_A0_fails:
  assumes "Elem Y (typed_R (Arr Prop Prop))" and "c211_rcur [Prop] raw_root Y = c211_A0"
  shows "\<not> c211_rrigid Y"
  using c211_rr_contradiction[OF assms] by blast

theorem c211_raw_RC_failure:
  "\<exists>X0. Elem X0 (typed_R (Arr Prop Prop)) \<and>
    (\<forall>Y. Elem Y (typed_R (Arr Prop Prop)) \<longrightarrow>
      c211_rcur [Prop] raw_root Y = c211_rcur [Prop] raw_root X0 \<longrightarrow> \<not> c211_rrigid Y)"
proof (intro exI[of _ c211_X0] conjI allI impI)
  show "Elem c211_X0 (typed_R (Arr Prop Prop))" using c211_X0_data by blast
next
  fix Y assume Ym: "Elem Y (typed_R (Arr Prop Prop))"
    and same: "c211_rcur [Prop] raw_root Y = c211_rcur [Prop] raw_root c211_X0"
  have "c211_rcur [Prop] raw_root Y = c211_A0" using same c211_X0_data by simp
  then show "\<not> c211_rrigid Y" by (rule c211_raw_rigid_A0_fails[OF Ym])
qed

ML \<open>
  val facts = [@{thm c211_mid_obj}, @{thm c211_root_obj}, @{thm c211_cur1}, @{thm c211_A0_iff},
    @{thm c211_A0_tuples}, @{thm c211_a0_tuples}, @{thm c211_tt_true_terminal}, @{thm c211_rr_refl},
    @{thm c211_zprop_a0(1)}, @{thm c211_zprop_a0(2)}, @{thm c211_S0_data}, @{thm c211_X0_data},
    @{thm c211_SB_data}, @{thm c211_B_data}, @{thm c211_H_data}, @{thm c211_rr_persist},
    @{thm c211_rr_leaf_full}, @{thm c211_rr_limit_full}, @{thm c211_rr_below_B},
    @{thm c211_rr_middle_only}, @{thm c211_rr_contradiction}, @{thm c211_raw_rigid_A0_fails},
    @{thm c211_raw_RC_failure}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-RAW-RIGIDITY: no t→t object with root relation A0 satisfies raw Rigid";
\<close>

end
