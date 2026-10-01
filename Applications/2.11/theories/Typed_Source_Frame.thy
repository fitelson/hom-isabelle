theory Typed_Source_Frame
  imports Verification_Checkpoint
    "Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Data"
begin

definition raw_W :: ZF where "raw_W = HOLZF.Nat"
definition raw_root :: ZF where "raw_root = nat2Nat 0"
definition raw_middle :: ZF where "raw_middle = nat2Nat 1"
definition raw_limit :: ZF where "raw_limit = nat2Nat 2"
definition raw_leaf :: "nat \<Rightarrow> ZF" where "raw_leaf n = nat2Nat (n+3)"

definition raw_rel :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "raw_rel v w \<longleftrightarrow> v=w \<or> v=raw_root \<or> (v=raw_middle \<and> w=raw_limit)"

lemma raw_codes [simp]:
  "Nat2nat raw_root = 0" "Nat2nat raw_middle = 1" "Nat2nat raw_limit = 2"
  "Nat2nat (raw_leaf n) = n+3"
  by (simp_all only: raw_root_def raw_middle_def raw_limit_def raw_leaf_def Nat2nat_nat2Nat)

lemma raw_worlds [simp]:
  "Elem raw_root raw_W" "Elem raw_middle raw_W" "Elem raw_limit raw_W"
  "Elem (raw_leaf n) raw_W"
  by (simp_all only: raw_W_def raw_root_def raw_middle_def raw_limit_def raw_leaf_def
    Elem_nat2Nat_Nat)

lemma raw_distinct [simp]:
  "raw_root \<noteq> raw_middle" "raw_root \<noteq> raw_limit" "raw_middle \<noteq> raw_limit"
  "raw_leaf n \<noteq> raw_root" "raw_leaf n \<noteq> raw_middle" "raw_leaf n \<noteq> raw_limit"
proof -
  show "raw_root \<noteq> raw_middle"
    by (simp only: raw_root_def raw_middle_def inj_eq[OF inj_nat2Nat]; simp)
  show "raw_root \<noteq> raw_limit"
    by (simp only: raw_root_def raw_limit_def inj_eq[OF inj_nat2Nat]; simp)
  show "raw_middle \<noteq> raw_limit"
    by (simp only: raw_middle_def raw_limit_def inj_eq[OF inj_nat2Nat]; simp)
  show "raw_leaf n \<noteq> raw_root"
    by (simp only: raw_leaf_def raw_root_def inj_eq[OF inj_nat2Nat]; simp)
  show "raw_leaf n \<noteq> raw_middle"
    by (simp only: raw_leaf_def raw_middle_def inj_eq[OF inj_nat2Nat]; simp)
  show "raw_leaf n \<noteq> raw_limit"
    by (simp only: raw_leaf_def raw_limit_def inj_eq[OF inj_nat2Nat]; simp)
qed

lemma raw_distinct_reverse [simp]:
  "raw_middle \<noteq> raw_root" "raw_limit \<noteq> raw_root" "raw_limit \<noteq> raw_middle"
  "raw_root \<noteq> raw_leaf n" "raw_middle \<noteq> raw_leaf n" "raw_limit \<noteq> raw_leaf n"
proof -
  show "raw_middle \<noteq> raw_root" by (metis raw_distinct(1))
  show "raw_limit \<noteq> raw_root" by (metis raw_distinct(2))
  show "raw_limit \<noteq> raw_middle" by (metis raw_distinct(3))
  show "raw_root \<noteq> raw_leaf n" by (metis raw_distinct(4))
  show "raw_middle \<noteq> raw_leaf n" by (metis raw_distinct(5))
  show "raw_limit \<noteq> raw_leaf n" by (metis raw_distinct(6))
qed

lemma raw_world_eq:
  assumes "Elem v raw_W" "Elem w raw_W"
  shows "(v=w) = (Nat2nat v = Nat2nat w)"
proof
  assume "v=w"
  then show "Nat2nat v=Nat2nat w" by simp
next
  assume eq: "Nat2nat v=Nat2nat w"
  have vm: "Elem v HOLZF.Nat" and wm: "Elem w HOLZF.Nat"
    using assms by (simp_all only: raw_W_def)
  have "v=nat2Nat (Nat2nat v)" by (rule sym[OF nat2Nat_Nat2nat[OF vm]])
  also have "...=nat2Nat (Nat2nat w)" by (simp only: eq)
  also have "...=w" by (rule nat2Nat_Nat2nat[OF wm])
  finally show "v=w" .
qed

lemma raw_rel_codes:
  assumes "Elem v raw_W" "Elem w raw_W"
  shows "raw_rel v w \<longleftrightarrow> Nat2nat v = Nat2nat w \<or> Nat2nat v=0 \<or>
    (Nat2nat v=1 \<and> Nat2nat w=2)"
  using raw_world_eq[OF assms] raw_world_eq[OF assms(1) raw_worlds(1)]
    raw_world_eq[OF assms(1) raw_worlds(2)] raw_world_eq[OF assms(2) raw_worlds(3)]
  by (simp add: raw_rel_def)

lemma raw_rel_refl: "raw_rel w w"
  by (simp add: raw_rel_def)

lemma raw_rel_trans:
  "raw_rel u v \<Longrightarrow> raw_rel v w \<Longrightarrow> raw_rel u w"
  by (auto simp: raw_rel_def)

theorem raw_frame: "book_ZF_frame raw_W raw_rel raw_root"
  by unfold_locales (auto simp: explode_Elem raw_rel_def)

definition raw_D :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_D a w = (if Nat2nat w=0 then typed_R a
    else if Nat2nat w=1 then typed_S a else typed_M a)"

definition raw_T :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_T a v w x = (if v=w then x else if Nat2nat v=0 then
    (if Nat2nat w=1 then typed_rs a x else if Nat2nat w=2
      then typed_j a (typed_rs a x) else typed_rn a x (Nat2nat w-3))
    else if Nat2nat v=1 \<and> Nat2nat w=2 then typed_j a x else undefined)"

definition raw_app :: "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_app a b w F x = (if Nat2nat w=0 then typed_R_app F x
    else if Nat2nat w=1 then typed_S_app F x else app F x)"

definition raw_truth :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "raw_truth w p = (if Nat2nat w=0 \<or> Nat2nat w=1 then bit_dec (Fst p) else bit_dec p)"

lemma raw_D_worlds [simp]:
  "raw_D a raw_root = typed_R a" "raw_D a raw_middle = typed_S a"
  "raw_D a raw_limit = typed_M a" "raw_D a (raw_leaf n) = typed_M a"
  by (simp_all add: raw_D_def)

theorem raw_D_nonempty: "explode (raw_D a w) \<noteq> {}"
  using typed_R_nonempty[of a] typed_S_nonempty[of a] typed_M_nonempty[of a]
  by (simp add: raw_D_def)

theorem raw_T_type:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W"
    and rel: "raw_rel v w" and xm: "Elem x (raw_D a v)"
  shows "Elem (raw_T a v w x) (raw_D a w)"
  using rel xm
  by (auto simp: raw_D_def raw_T_def raw_world_eq[OF vw ww]
      raw_rel_codes[OF vw ww] split: if_splits
      intro: typed_rs_type typed_rn_type typed_j_type)

theorem raw_T_id: "raw_T a w w x = x"
  by (simp add: raw_T_def)

theorem raw_T_compose:
  assumes uw: "Elem u raw_W" and vw: "Elem v raw_W" and ww: "Elem w raw_W"
    and uv: "raw_rel u v" and vwrel: "raw_rel v w"
  shows "raw_T a u w x = raw_T a v w (raw_T a u v x)"
  using uv vwrel
  by (auto simp: raw_T_def raw_world_eq[OF uw vw] raw_world_eq[OF vw ww]
      raw_world_eq[OF uw ww] raw_rel_codes[OF uw vw] raw_rel_codes[OF vw ww]
      split: if_splits)

lemma typed_ru_surjective:
  assumes "Elem y (typed_M a)"
  shows "\<exists>x. Elem x (typed_R a) \<and> typed_j a (typed_rs a x)=y"
proof -
  obtain z where zm: "Elem z (typed_S a)" and zy: "typed_j a z=y"
    using typed_j_onto[OF assms] by blast
  obtain x where xm: "Elem x (typed_R a)" and xz: "typed_rs a x=z"
    using typed_rs_surjective[OF zm] by blast
  show ?thesis using xm xz zy by blast
qed

theorem raw_T_onto:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W"
    and rel: "raw_rel v w" and ym: "Elem y (raw_D a w)"
  shows "\<exists>x. Elem x (raw_D a v) \<and> raw_T a v w x=y"
  using rel ym typed_rs_surjective[where a=a] typed_rn_surjective[where a=a]
    typed_j_onto[where a=a] typed_ru_surjective[where a=a]
  by (cases "Nat2nat w=2"; auto simp: raw_T_def raw_D_def raw_world_eq[OF vw ww]
      raw_rel_codes[OF vw ww] split: if_splits)

theorem raw_modalized:
  "book_modalized_set (explode raw_W) raw_rel (\<lambda>w. explode (raw_D a w)) (raw_T a)"
  by unfold_locales
    (auto simp: explode_Elem intro: raw_rel_refl raw_rel_trans raw_T_type raw_T_id raw_T_compose)

theorem raw_app_type:
  assumes "Elem F (raw_D (Arr a b) w)" "Elem x (raw_D a w)"
  shows "Elem (raw_app a b w F x) (raw_D b w)"
  using assms
  by (auto simp: raw_app_def raw_D_def split: if_splits
      intro: typed_R_application typed_S_application typed_M_application)

lemma typed_R_application_u:
  assumes fm: "Elem F (typed_R (Arr a b))" and xm: "Elem x (typed_R a)"
  shows "typed_j b (typed_rs b (typed_R_app F x)) =
    app (typed_j (Arr a b) (typed_rs (Arr a b) F)) (typed_j a (typed_rs a x))"
  using typed_R_application_s[OF fm xm]
    typed_S_application_natural[OF typed_rs_type[OF fm] typed_rs_type[OF xm]]
  by simp

lemmas raw_R_app_s = typed_R_application_s[unfolded typed_R.simps typed_rs.simps]
lemmas raw_R_app_n = typed_R_application_n[unfolded typed_R.simps typed_rn.simps]
lemmas raw_R_app_u = typed_R_application_u[unfolded typed_R.simps typed_rs.simps typed_j.simps]
lemmas raw_S_app_u = typed_S_application_natural[unfolded typed_S.simps typed_j.simps]

theorem raw_app_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W"
    and rel: "raw_rel v w" and fm: "Elem F (raw_D (Arr a b) v)"
    and xm: "Elem x (raw_D a v)"
  shows "raw_T b v w (raw_app a b v F x) =
    raw_app a b w (raw_T (Arr a b) v w F) (raw_T a v w x)"
  using rel fm xm
  by (auto simp: raw_T_def raw_D_def raw_app_def raw_world_eq[OF vw ww]
      raw_rel_codes[OF vw ww] split: if_splits
      intro: raw_R_app_s raw_R_app_n raw_R_app_u raw_S_app_u)

theorem raw_app_extensional:
  assumes fm: "Elem F (raw_D (Arr a b) w)" and gm: "Elem G (raw_D (Arr a b) w)"
    and same: "\<And>x. Elem x (raw_D a w) \<Longrightarrow> raw_app a b w F x=raw_app a b w G x"
  shows "F=G"
proof (cases "Nat2nat w=0")
  case True
  show ?thesis
    by (rule typed_R_extensional)
      (use fm gm same True in \<open>simp_all add: raw_D_def raw_app_def\<close>)
next
  case no_root: False
  show ?thesis
  proof (cases "Nat2nat w=1")
    case True
    show ?thesis
      by (rule typed_S_extensional)
        (use fm gm same no_root True in \<open>simp_all add: raw_D_def raw_app_def\<close>)
  next
    case False
    show ?thesis
      by (rule typed_graph_ext[where A="typed_M a" and B="typed_M b" and C="typed_M b"])
        (use fm gm same no_root False in \<open>simp_all add: raw_D_def raw_app_def\<close>)
  qed
qed

section \<open>Propositions are separated by truth at accessible worlds\<close>

lemma raw_truth_root_profile [simp]:
  "raw_truth raw_root (zprop p) = fst p"
  by (simp add: raw_truth_def zprop_def Fst)

lemma raw_truth_root_middle [simp]:
  "raw_truth raw_middle (raw_T Prop raw_root raw_middle (zprop p)) = fst (snd p)"
  by (simp add: raw_truth_def raw_T_def zprop_def Fst Snd raw_world_eq)

lemma raw_truth_root_leaf [simp]:
  "raw_truth (raw_leaf n) (raw_T Prop raw_root (raw_leaf n) (zprop p)) =
    (n \<in> snd (snd p))"
  by (simp add: raw_truth_def raw_T_def zprop_def Fst Snd raw_world_eq)

lemma raw_truth_middle_profile [simp]:
  "raw_truth raw_middle (zmiddle p) = fst p"
  by (simp add: raw_truth_def zmiddle_def Fst)

lemma raw_truth_middle_limit [simp]:
  "raw_truth raw_limit (raw_T Prop raw_middle raw_limit (zmiddle p)) = snd p"
  by (simp add: raw_truth_def raw_T_def zmiddle_def Snd raw_world_eq)

lemma raw_bit_separates:
  assumes "Elem p typed_two" "Elem q typed_two" "bit_dec p = bit_dec q"
  shows "p=q"
proof -
  have ep: "zbit (bit_dec p)=p" and eq: "zbit (bit_dec q)=q"
    using zbit_encode[OF assms(1)] zbit_encode[OF assms(2)]
    by (simp_all only: bit_dec_def)
  have "p=zbit (bit_dec p)" by (rule sym[OF ep])
  also have "...=zbit (bit_dec q)" by (simp only: assms(3))
  also have "...=q" by (rule eq)
  finally show ?thesis .
qed

theorem raw_truth_separates:
  assumes ww: "Elem w raw_W" and pm: "Elem p (raw_D Prop w)"
    and qm: "Elem q (raw_D Prop w)"
    and same: "\<And>v. Elem v raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
      raw_truth v (raw_T Prop w v p) = raw_truth v (raw_T Prop w v q)"
  shows "p=q"
proof (cases "Nat2nat w=0")
  case True
  have wr: "w=raw_root"
    using raw_world_eq[OF ww raw_worlds(1)] True by simp
  have pR: "Elem p (typed_R Prop)" and qR: "Elem q (typed_R Prop)"
    using pm qm by (simp_all add: wr)
  obtain P Q where p: "p=zprop P" and q: "q=zprop Q"
    using zprop_surjective[OF pR] zprop_surjective[OF qR] by blast
  have actual: "fst P=fst Q"
    using same[OF raw_worlds(1)] by (simp add: wr raw_rel_def raw_T_id p q)
  have middle: "fst (snd P)=fst (snd Q)"
    using same[OF raw_worlds(2)] by (simp add: wr raw_rel_def p q)
  have leaves: "snd (snd P)=snd (snd Q)"
  proof (rule set_eqI)
    fix n
    show "n \<in> snd (snd P) \<longleftrightarrow> n \<in> snd (snd Q)"
      using same[OF raw_worlds(4)[of n]] by (simp add: wr raw_rel_def p q)
  qed
  have "P=Q" using actual middle leaves by (simp add: prod_eq_iff)
  then show ?thesis by (simp add: p q)
next
  case no_root: False
  show ?thesis
  proof (cases "Nat2nat w=1")
    case True
    have wm: "w=raw_middle"
      using raw_world_eq[OF ww raw_worlds(2)] True by simp
    have pS: "Elem p (typed_S Prop)" and qS: "Elem q (typed_S Prop)"
      using pm qm by (simp_all add: wm)
    obtain P Q where p: "p=zmiddle P" and q: "q=zmiddle Q"
      using zmiddle_surjective[OF pS] zmiddle_surjective[OF qS] by blast
    have actual: "fst P=fst Q"
      using same[OF raw_worlds(2)] by (simp add: wm raw_rel_def raw_T_id p q)
    have future: "snd P=snd Q"
      using same[OF raw_worlds(3)] by (simp add: wm raw_rel_def p q)
    have "P=Q" using actual future by (simp add: prod_eq_iff)
    then show ?thesis by (simp add: p q)
  next
    case False
    have pM: "Elem p typed_two" and qM: "Elem q typed_two"
      using pm qm no_root False by (simp_all add: raw_D_def)
    have eq: "bit_dec p=bit_dec q"
      using same[OF ww raw_rel_refl] no_root False
      by (simp add: raw_T_id raw_truth_def)
    show ?thesis by (rule raw_bit_separates[OF pM qM eq])
  qed
qed

text \<open>The concrete pointed frame, carriers, counterparts, and natural
  application above discharge structural laws without assuming modelhood.
  Representation as future-subset/future-pair graphs is a separate step.\<close>

end
