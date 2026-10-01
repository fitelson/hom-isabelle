theory Typed_Equality
  imports Typed_Proposition_Bridge
begin

section \<open>Actual equality at every type and future coordinate\<close>

definition typed_meq1 :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_meq1 a x = Lambda (typed_M a) (\<lambda>y. zbit (x = y))"

definition typed_meq :: "otype \<Rightarrow> ZF" where
  "typed_meq a = Lambda (typed_M a) (typed_meq1 a)"

lemma typed_meq1_type:
  "Elem (typed_meq1 a x) (typed_M (Arr a Prop))"
  by (simp add: typed_meq1_def Elem_Lambda_Fun)

lemma typed_meq_type:
  "Elem (typed_meq a) (typed_M (Arr a (Arr a Prop)))"
  using typed_meq1_type by (simp add: typed_meq_def Elem_Lambda_Fun)

lemma typed_meq_apply:
  assumes "Elem x (typed_M a)" "Elem y (typed_M a)"
  shows "app (app (typed_meq a) x) y = zbit (x = y)"
  using assms by (simp add: typed_meq_def typed_meq1_def Lambda_app)

definition typed_seqval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_seqval a x y = Opair (zbit (x = y)) (zbit (typed_j a x = typed_j a y))"

definition typed_seq1 :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_seq1 a x = Opair (Lambda (typed_S a) (typed_seqval a x))
    (typed_meq1 a (typed_j a x))"

definition typed_seqeq :: "otype \<Rightarrow> ZF" where
  "typed_seqeq a = Opair (Lambda (typed_S a) (typed_seq1 a)) (typed_meq a)"

lemma typed_seqval_type:
  "Elem (typed_seqval a x y) (typed_S Prop)"
  by (auto simp: typed_seqval_def CartProd Opair)

lemma typed_seq1_type:
  "Elem (typed_seq1 a x) (typed_S (Arr a Prop))"
  using typed_seqval_type[of a x] typed_meq1_type[of a "typed_j a x"]
  by (auto simp: typed_seq1_def typed_compatible_pair Elem_Lambda_Fun
      typed_seqval_def typed_meq1_def Lambda_app Snd
      typed_j_type)

lemma typed_seqeq_type:
  "Elem (typed_seqeq a) (typed_S (Arr a (Arr a Prop)))"
  using typed_seq1_type[of a] typed_meq_type[of a]
  by (auto simp: typed_seqeq_def typed_compatible_pair Elem_Lambda_Fun
      typed_seq1_def typed_meq_def Lambda_app Snd
      typed_j_type)

lemma typed_seqeq_apply:
  assumes "Elem x (typed_S a)" "Elem y (typed_S a)"
  shows "typed_S_app (typed_S_app (typed_seqeq a) x) y = typed_seqval a x y"
  using assms by (simp add: typed_S_app_def typed_seqeq_def typed_seq1_def Fst Lambda_app)

definition typed_reqval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_reqval a x y = Opair (zbit (x = y))
    (Opair (zbit (typed_rs a x = typed_rs a y))
      (typed_seq (\<lambda>n. zbit (typed_rn a x n = typed_rn a y n))))"

lemma typed_reqval_type:
  "Elem (typed_reqval a x y) (typed_R Prop)"
  unfolding typed_reqval_def by (rule typed_R_propI) simp_all

lemma typed_reqval_s:
  assumes xm: "Elem x (typed_R a)" and ym: "Elem y (typed_R a)"
  shows "typed_rs Prop (typed_reqval a x y) =
    typed_seqval a (typed_rs a x) (typed_rs a y)"
proof -
  have lim: "ulim (\<lambda>n. zbit (typed_rn a x n = typed_rn a y n)) =
    zbit (ulim (typed_rn a x) = ulim (typed_rn a y))"
    by (rule ulim_binary[where A="explode (typed_M a)" and B="explode (typed_M a)"
      and f="typed_rn a x" and g="typed_rn a y" and h="\<lambda>u v. zbit (u=v)"])
      (use typed_M_finite[of a] typed_rn_type[OF xm] typed_rn_type[OF ym]
        in \<open>simp_all add: explode_Elem\<close>)
  show ?thesis
    by (simp add: typed_reqval_def typed_seqval_def Fst Snd lim
      typed_R_compatible[OF xm] typed_R_compatible[OF ym])
qed

lemma typed_reqval_n [simp]:
  "typed_rn Prop (typed_reqval a x y) n = zbit (typed_rn a x n = typed_rn a y n)"
  by (simp add: typed_reqval_def Fst Snd)

lemmas typed_reqval_n_raw [simp] = typed_reqval_n[unfolded typed_rn.simps]

lemma typed_meq1_ulim:
  assumes xm: "Elem x (typed_R a)"
  shows "ulim (\<lambda>n. typed_meq1 a (typed_rn a x n)) =
    typed_meq1 a (typed_j a (typed_rs a x))"
proof -
  have "ulim (\<lambda>n. typed_meq1 a (typed_rn a x n)) =
    typed_meq1 a (ulim (typed_rn a x))"
    by (rule ulim_map[where A="explode (typed_M a)" and f="typed_rn a x"
      and h="typed_meq1 a", OF typed_M_finite])
      (use typed_rn_type[OF xm] in \<open>simp add: explode_Elem\<close>)
  then show ?thesis by (simp add: typed_R_compatible[OF xm])
qed

definition typed_req1 :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_req1 a x = Opair (Lambda (typed_R a) (typed_reqval a x))
    (Opair (typed_seq1 a (typed_rs a x))
      (typed_seq (\<lambda>n. typed_meq1 a (typed_rn a x n))))"

lemma typed_req1_type:
  assumes xm: "Elem x (typed_R a)"
  shows "Elem (typed_req1 a x) (typed_R (Arr a Prop))"
proof -
  have seq: "Elem (typed_seq (\<lambda>n. typed_meq1 a (typed_rn a x n)))
    (Fun HOLZF.Nat (typed_M (Arr a Prop)))"
    by (rule typed_seq_type) (rule typed_meq1_type)
  have mid: "Elem (typed_seq1 a (typed_rs a x)) (typed_S (Arr a Prop))"
    by (rule typed_seq1_type)
  have coherent: "typed_j (Arr a Prop) (typed_seq1 a (typed_rs a x)) =
    ulim (\<lambda>n. typed_meq1 a (typed_rn a x n))"
    using typed_meq1_ulim[OF xm] by (simp add: typed_seq1_def Snd)
  show ?thesis
    unfolding typed_req1_def typed_R.simps
    apply (simp only: typed_root_arrow_triple)
    using seq mid coherent typed_reqval_type[of a x]
      typed_reqval_s[OF xm] typed_rs_type typed_rn_type
    by (auto simp: Elem_Lambda_Fun Lambda_app typed_S_app_def typed_seq1_def
      typed_meq1_def Fst)
qed

lemma typed_req1_s [simp]:
  "typed_rs (Arr a Prop) (typed_req1 a x) = typed_seq1 a (typed_rs a x)"
  by (simp add: typed_req1_def Fst Snd)

lemma typed_req1_n [simp]:
  "typed_rn (Arr a Prop) (typed_req1 a x) n = typed_meq1 a (typed_rn a x n)"
  by (simp add: typed_req1_def Fst Snd)

lemmas typed_req1_s_raw [simp] = typed_req1_s[unfolded typed_rs.simps]
lemmas typed_req1_n_raw [simp] = typed_req1_n[unfolded typed_rn.simps]

definition typed_req :: "otype \<Rightarrow> ZF" where
  "typed_req a = Opair (Lambda (typed_R a) (typed_req1 a))
    (Opair (typed_seqeq a) (typed_seq (\<lambda>n. typed_meq a)))"

theorem typed_req_type:
  "Elem (typed_req a) (typed_R (Arr a (Arr a Prop)))"
proof -
  have seq: "Elem (typed_seq (\<lambda>n. typed_meq a))
    (Fun HOLZF.Nat (typed_M (Arr a (Arr a Prop))))"
    by (rule typed_seq_type) (rule typed_meq_type)
  have mid: "Elem (typed_seqeq a) (typed_S (Arr a (Arr a Prop)))"
    by (rule typed_seqeq_type)
  show ?thesis
    unfolding typed_req_def typed_R.simps
    apply (simp only: typed_root_arrow_triple)
    using seq mid typed_req1_type[where a=a] typed_rs_type typed_rn_type
    by (auto simp: Elem_Lambda_Fun Lambda_app typed_S_app_def
      typed_seqeq_def typed_meq_def Fst Snd)
qed

theorem typed_req_apply:
  assumes "Elem x (typed_R a)" "Elem y (typed_R a)"
  shows "typed_R_app (typed_R_app (typed_req a) x) y = typed_reqval a x y"
  using assms by (simp add: typed_R_app_def typed_req_def typed_req1_def Fst Lambda_app)

text \<open>The equality object is proved to inhabit every required
  higher-type carrier. Its current bit is actual ZF equality, and each
  future bit is equality of the corresponding transported objects. This
  is genuine profile-valued identity, not a two-valued collapse or an
  assumption that arbitrary HOL functions admit abstraction.\<close>

end
