theory Typed_Implication
  imports Typed_Combinators
begin

section \<open>Profile-valued material implication\<close>

definition ti_mval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ti_mval p q = zbit (p = Singleton Empty \<longrightarrow> q = Singleton Empty)"

definition ti_m1 :: "ZF \<Rightarrow> ZF" where
  "ti_m1 p = Lambda typed_two (ti_mval p)"

definition ti_m :: ZF where
  "ti_m = Lambda typed_two ti_m1"

lemma ti_mval_type [simp]: "Elem (ti_mval p q) typed_two"
  by (simp add: ti_mval_def)

lemma ti_m1_type: "Elem (ti_m1 p) (typed_M (Arr Prop Prop))"
  by (simp add: ti_m1_def Elem_Lambda_Fun)

lemma ti_m_type: "Elem ti_m (typed_M (Arr Prop (Arr Prop Prop)))"
  using ti_m1_type by (simp add: ti_m_def Elem_Lambda_Fun)

lemma ti_m1_app [simp]:
  "Elem q typed_two \<Longrightarrow> app (ti_m1 p) q = ti_mval p q"
  by (simp add: ti_m1_def Lambda_app)

lemma ti_m_app [simp]: "Elem p typed_two \<Longrightarrow> app ti_m p = ti_m1 p"
  by (simp add: ti_m_def Lambda_app)

definition ti_sval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ti_sval p q = Opair (ti_mval (Fst p) (Fst q)) (ti_mval (Snd p) (Snd q))"

lemma ti_sval_type: "Elem (ti_sval p q) (typed_S Prop)"
  by (simp add: ti_sval_def CartProd Opair)

definition ti_s1 :: "ZF \<Rightarrow> ZF" where
  "ti_s1 p = tc_sabs Prop (ti_sval p) (ti_m1 (typed_j Prop p))"

definition ti_s :: ZF where
  "ti_s = tc_sabs Prop ti_s1 ti_m"

lemma ti_s1_type: "Elem (ti_s1 p) (typed_S (Arr Prop Prop))"
  unfolding ti_s1_def
  apply (rule tc_sabs_type[where b=Prop])
  subgoal by (rule ti_sval_type)
  subgoal by (rule ti_m1_type)
  subgoal for q
    using typed_j_type[where a=Prop and x=q]
    by (simp add: ti_sval_def Snd)
  done

lemma ti_s1_j [simp]: "typed_j (Arr Prop Prop) (ti_s1 p) = ti_m1 (typed_j Prop p)"
  by (simp add: ti_s1_def tc_sabs_def Snd)

lemma ti_s1_app [simp]:
  "Elem q (typed_S Prop) \<Longrightarrow> typed_S_app (ti_s1 p) q = ti_sval p q"
  by (simp add: ti_s1_def)

lemma ti_s_type: "Elem ti_s (typed_S (Arr Prop (Arr Prop Prop)))"
  unfolding ti_s_def
  apply (rule tc_sabs_type[where b="Arr Prop Prop"])
  subgoal by (rule ti_s1_type)
  subgoal by (rule ti_m_type)
  subgoal for p
    using typed_j_type[where a=Prop and x=p]
    by (simp add: ti_s1_def tc_sabs_def Snd)
  done

lemma ti_s_j [simp]: "typed_j (Arr Prop (Arr Prop Prop)) ti_s = ti_m"
  by (simp add: ti_s_def tc_sabs_def Snd)

lemma ti_s_app [simp]:
  "Elem p (typed_S Prop) \<Longrightarrow> typed_S_app ti_s p = ti_s1 p"
  by (simp add: ti_s_def)

definition ti_rval :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "ti_rval p q = Opair (ti_mval (Fst p) (Fst q))
    (Opair (ti_mval (Fst (Snd p)) (Fst (Snd q)))
      (typed_seq (\<lambda>n. ti_mval (typed_rn Prop p n) (typed_rn Prop q n))))"

lemma ti_rval_type: "Elem (ti_rval p q) (typed_R Prop)"
  unfolding ti_rval_def by (rule typed_R_propI) simp_all

lemma ti_rval_s:
  assumes p: "Elem p (typed_R Prop)" and q: "Elem q (typed_R Prop)"
  shows "typed_rs Prop (ti_rval p q) = ti_sval (typed_rs Prop p) (typed_rs Prop q)"
proof -
  have lim: "ulim (\<lambda>n. ti_mval (typed_rn Prop p n) (typed_rn Prop q n)) =
      ti_mval (ulim (typed_rn Prop p)) (ulim (typed_rn Prop q))"
    by (rule ulim_binary[where A="explode (typed_M Prop)" and B="explode (typed_M Prop)"
      and f="typed_rn Prop p" and g="typed_rn Prop q" and h=ti_mval])
      (use typed_M_finite[of Prop] typed_rn_type[OF p] typed_rn_type[OF q]
       in \<open>simp_all add: explode_Elem\<close>)
  have rawlim: "ulim (\<lambda>n. ti_mval (typed_at (Snd (Snd p)) n) (typed_at (Snd (Snd q)) n)) =
      ti_mval (ulim (typed_at (Snd (Snd p)))) (ulim (typed_at (Snd (Snd q))))"
    using lim by (simp only: typed_rn.simps typed_rn_functions)
  show ?thesis by (simp add: ti_rval_def ti_sval_def Fst Snd rawlim)
qed

lemma ti_rval_n [simp]:
  "typed_rn Prop (ti_rval p q) n = ti_mval (typed_rn Prop p n) (typed_rn Prop q n)"
  by (simp add: ti_rval_def Fst Snd)

definition ti_r1 :: "ZF \<Rightarrow> ZF" where
  "ti_r1 p = tc_rabs Prop (ti_rval p) (ti_s1 (typed_rs Prop p))
    (\<lambda>n. ti_m1 (typed_rn Prop p n))"

lemma ti_m1_ulim:
  assumes p: "Elem p (typed_R Prop)"
  shows "ulim (\<lambda>n. ti_m1 (typed_rn Prop p n)) = ti_m1 (typed_j Prop (typed_rs Prop p))"
proof -
  have "ulim (\<lambda>n. ti_m1 (typed_rn Prop p n)) = ti_m1 (ulim (typed_rn Prop p))"
    by (rule ulim_map[where A="explode (typed_M Prop)" and f="typed_rn Prop p" and h=ti_m1])
      (use typed_M_finite[of Prop] typed_rn_type[OF p] in \<open>simp_all add: explode_Elem\<close>)
  then show ?thesis by (simp only: typed_R_compatible[OF p])
qed

lemma ti_r1_type:
  assumes p: "Elem p (typed_R Prop)"
  shows "Elem (ti_r1 p) (typed_R (Arr Prop Prop))"
  unfolding ti_r1_def
  apply (rule tc_rabs_type[where b=Prop])
  subgoal by (rule ti_rval_type)
  subgoal by (rule ti_s1_type)
  subgoal by (rule ti_m1_type)
  subgoal using ti_m1_ulim[OF p] by (simp only: ti_s1_j)
  subgoal for q using ti_rval_s[OF p, of q]
    by (simp only: ti_s1_app typed_rs_type)
  subgoal for q n
    using typed_rn_type[where a=Prop and x=q and n=n]
    by (simp only: typed_M.simps ti_rval_n; simp)
  done

lemma ti_r1_s [simp]: "typed_rs (Arr Prop Prop) (ti_r1 p) = ti_s1 (typed_rs Prop p)"
  by (simp add: ti_r1_def tc_rabs_def Fst Snd)

lemma ti_r1_n [simp]: "typed_rn (Arr Prop Prop) (ti_r1 p) n = ti_m1 (typed_rn Prop p n)"
  by (simp add: ti_r1_def tc_rabs_def Fst Snd)

definition ti_r :: ZF where
  "ti_r = tc_rabs Prop ti_r1 ti_s (\<lambda>_. ti_m)"

theorem ti_r_type: "Elem ti_r (typed_R (Arr Prop (Arr Prop Prop)))"
  unfolding ti_r_def
  apply (rule tc_rabs_type[where b="Arr Prop Prop"])
  subgoal by (rule ti_r1_type)
  subgoal by (rule ti_s_type)
  subgoal by (rule ti_m_type)
  subgoal by (simp only: ti_s_j ulim_const)
  subgoal by (simp only: ti_r1_s ti_s_app typed_rs_type)
  subgoal for p n
    using typed_rn_type[where a=Prop and x=p and n=n]
    by (simp only: typed_M.simps ti_r1_n; simp)
  done

theorem ti_r_apply:
  assumes "Elem p (typed_R Prop)" "Elem q (typed_R Prop)"
  shows "typed_R_app (typed_R_app ti_r p) q = ti_rval p q"
  using assms by (simp add: ti_r_def ti_r1_def)

text \<open>This proves membership and application of a concrete material
  implication profile. Identification with the source's prescribed function
  graph still requires the source-model transport theorem.\<close>

end
