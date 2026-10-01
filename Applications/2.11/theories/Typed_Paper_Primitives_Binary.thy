theory Typed_Paper_Primitives_Binary
  imports Typed_Combinators
begin

section \<open>Profile-valued arbitrary binary Boolean operation\<close>

context
  fixes B :: "bool \<Rightarrow> bool \<Rightarrow> bool"
begin

definition ppb_mval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ppb_mval p q = zbit (B (p = Singleton Empty) (q = Singleton Empty))"

definition ppb_m1 :: "ZF \<Rightarrow> ZF" where
  "ppb_m1 p = Lambda typed_two (ppb_mval p)"

definition ppb_m :: ZF where
  "ppb_m = Lambda typed_two ppb_m1"

lemma ppb_mval_type [simp]: "Elem (ppb_mval p q) typed_two"
  by (simp add: ppb_mval_def)

lemma ppb_m1_type: "Elem (ppb_m1 p) (typed_M (Arr Prop Prop))"
  by (simp add: ppb_m1_def Elem_Lambda_Fun)

lemma ppb_m_type: "Elem ppb_m (typed_M (Arr Prop (Arr Prop Prop)))"
  using ppb_m1_type by (simp add: ppb_m_def Elem_Lambda_Fun)

lemma ppb_m1_app [simp]:
  "Elem q typed_two \<Longrightarrow> app (ppb_m1 p) q = ppb_mval p q"
  by (simp add: ppb_m1_def Lambda_app)

lemma ppb_m_app [simp]: "Elem p typed_two \<Longrightarrow> app ppb_m p = ppb_m1 p"
  by (simp add: ppb_m_def Lambda_app)

definition ppb_sval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ppb_sval p q = Opair (ppb_mval (Fst p) (Fst q)) (ppb_mval (Snd p) (Snd q))"

lemma ppb_sval_type: "Elem (ppb_sval p q) (typed_S Prop)"
  by (simp add: ppb_sval_def CartProd Opair)

definition ppb_s1 :: "ZF \<Rightarrow> ZF" where
  "ppb_s1 p = tc_sabs Prop (ppb_sval p) (ppb_m1 (typed_j Prop p))"

definition ppb_s :: ZF where
  "ppb_s = tc_sabs Prop ppb_s1 ppb_m"

lemma ppb_s1_type: "Elem (ppb_s1 p) (typed_S (Arr Prop Prop))"
  unfolding ppb_s1_def
  apply (rule tc_sabs_type[where b=Prop])
  subgoal by (rule ppb_sval_type)
  subgoal by (rule ppb_m1_type)
  subgoal for q
    using typed_j_type[where a=Prop and x=q]
    by (simp add: ppb_sval_def Snd)
  done

lemma ppb_s1_j [simp]: "typed_j (Arr Prop Prop) (ppb_s1 p) = ppb_m1 (typed_j Prop p)"
  by (simp add: ppb_s1_def tc_sabs_def Snd)

lemma ppb_s1_app [simp]:
  "Elem q (typed_S Prop) \<Longrightarrow> typed_S_app (ppb_s1 p) q = ppb_sval p q"
  by (simp add: ppb_s1_def)

lemma ppb_s_type: "Elem ppb_s (typed_S (Arr Prop (Arr Prop Prop)))"
  unfolding ppb_s_def
  apply (rule tc_sabs_type[where b="Arr Prop Prop"])
  subgoal by (rule ppb_s1_type)
  subgoal by (rule ppb_m_type)
  subgoal for p
    using typed_j_type[where a=Prop and x=p]
    by (simp add: ppb_s1_def tc_sabs_def Snd)
  done

lemma ppb_s_j [simp]: "typed_j (Arr Prop (Arr Prop Prop)) ppb_s = ppb_m"
  by (simp add: ppb_s_def tc_sabs_def Snd)

lemma ppb_s_app [simp]:
  "Elem p (typed_S Prop) \<Longrightarrow> typed_S_app ppb_s p = ppb_s1 p"
  by (simp add: ppb_s_def)

definition ppb_rval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ppb_rval p q = Opair (ppb_mval (Fst p) (Fst q))
    (Opair (ppb_mval (Fst (Snd p)) (Fst (Snd q)))
      (typed_seq (\<lambda>n. ppb_mval (typed_rn Prop p n) (typed_rn Prop q n))))"

lemma ppb_rval_type: "Elem (ppb_rval p q) (typed_R Prop)"
  unfolding ppb_rval_def by (rule typed_R_propI) simp_all

lemma ppb_rval_s:
  assumes p: "Elem p (typed_R Prop)" and q: "Elem q (typed_R Prop)"
  shows "typed_rs Prop (ppb_rval p q) = ppb_sval (typed_rs Prop p) (typed_rs Prop q)"
proof -
  have lim: "ulim (\<lambda>n. ppb_mval (typed_rn Prop p n) (typed_rn Prop q n)) =
      ppb_mval (ulim (typed_rn Prop p)) (ulim (typed_rn Prop q))"
    by (rule ulim_binary[where A="explode (typed_M Prop)" and B="explode (typed_M Prop)"
      and f="typed_rn Prop p" and g="typed_rn Prop q" and h=ppb_mval])
      (use typed_M_finite[of Prop] typed_rn_type[OF p] typed_rn_type[OF q]
       in \<open>simp_all add: explode_Elem\<close>)
  have rawlim: "ulim (\<lambda>n. ppb_mval (typed_at (Snd (Snd p)) n) (typed_at (Snd (Snd q)) n)) =
      ppb_mval (ulim (typed_at (Snd (Snd p)))) (ulim (typed_at (Snd (Snd q))))"
    using lim by (simp only: typed_rn.simps typed_rn_functions)
  show ?thesis by (simp add: ppb_rval_def ppb_sval_def Fst Snd rawlim)
qed

lemma ppb_rval_n [simp]:
  "typed_rn Prop (ppb_rval p q) n = ppb_mval (typed_rn Prop p n) (typed_rn Prop q n)"
  by (simp add: ppb_rval_def Fst Snd)

definition ppb_r1 :: "ZF \<Rightarrow> ZF" where
  "ppb_r1 p = tc_rabs Prop (ppb_rval p) (ppb_s1 (typed_rs Prop p))
    (\<lambda>n. ppb_m1 (typed_rn Prop p n))"

lemma ppb_m1_ulim:
  assumes p: "Elem p (typed_R Prop)"
  shows "ulim (\<lambda>n. ppb_m1 (typed_rn Prop p n)) = ppb_m1 (typed_j Prop (typed_rs Prop p))"
proof -
  have "ulim (\<lambda>n. ppb_m1 (typed_rn Prop p n)) = ppb_m1 (ulim (typed_rn Prop p))"
    by (rule ulim_map[where A="explode (typed_M Prop)" and f="typed_rn Prop p" and h=ppb_m1])
      (use typed_M_finite[of Prop] typed_rn_type[OF p] in \<open>simp_all add: explode_Elem\<close>)
  then show ?thesis by (simp only: typed_R_compatible[OF p])
qed

lemma ppb_r1_type:
  assumes p: "Elem p (typed_R Prop)"
  shows "Elem (ppb_r1 p) (typed_R (Arr Prop Prop))"
  unfolding ppb_r1_def
  apply (rule tc_rabs_type[where b=Prop])
  subgoal by (rule ppb_rval_type)
  subgoal by (rule ppb_s1_type)
  subgoal by (rule ppb_m1_type)
  subgoal using ppb_m1_ulim[OF p] by (simp only: ppb_s1_j)
  subgoal for q using ppb_rval_s[OF p, of q]
    by (simp only: ppb_s1_app typed_rs_type)
  subgoal for q n
    using typed_rn_type[where a=Prop and x=q and n=n]
    by (simp only: typed_M.simps ppb_rval_n; simp)
  done

lemma ppb_r1_s [simp]: "typed_rs (Arr Prop Prop) (ppb_r1 p) = ppb_s1 (typed_rs Prop p)"
  by (simp add: ppb_r1_def tc_rabs_def Fst Snd)

lemma ppb_r1_n [simp]: "typed_rn (Arr Prop Prop) (ppb_r1 p) n = ppb_m1 (typed_rn Prop p n)"
  by (simp add: ppb_r1_def tc_rabs_def Fst Snd)

definition ppb_r :: ZF where
  "ppb_r = tc_rabs Prop ppb_r1 ppb_s (\<lambda>_. ppb_m)"

theorem ppb_r_type: "Elem ppb_r (typed_R (Arr Prop (Arr Prop Prop)))"
  unfolding ppb_r_def
  apply (rule tc_rabs_type[where b="Arr Prop Prop"])
  subgoal by (rule ppb_r1_type)
  subgoal by (rule ppb_s_type)
  subgoal by (rule ppb_m_type)
  subgoal by (simp only: ppb_s_j ulim_const)
  subgoal by (simp only: ppb_r1_s ppb_s_app typed_rs_type)
  subgoal for p n
    using typed_rn_type[where a=Prop and x=p and n=n]
    by (simp only: typed_M.simps ppb_r1_n; simp)
  done

theorem ppb_r_apply:
  assumes "Elem p (typed_R Prop)" "Elem q (typed_R Prop)"
  shows "typed_R_app (typed_R_app ppb_r p) q = ppb_rval p q"
  using assms by (simp add: ppb_r_def ppb_r1_def)

text \<open>This proves membership and application of a concrete binary Boolean
  profile. Identification with the source's prescribed function
  graph still requires the source-model transport theorem.\<close>

end

end

