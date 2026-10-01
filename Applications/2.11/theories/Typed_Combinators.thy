theory Typed_Combinators
  imports Typed_Proposition_Bridge
begin

section \<open>Explicit compatible abstraction constructors\<close>

definition tc_sabs :: "otype \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_sabs a f G = Opair (Lambda (typed_S a) f) G"

lemma tc_sabs_app [simp]:
  "Elem x (typed_S a) \<Longrightarrow> typed_S_app (tc_sabs a f G) x = f x"
  by (simp add: tc_sabs_def typed_S_app_def Fst Lambda_app)

lemma tc_sabs_j [simp]: "typed_j (Arr a b) (tc_sabs a f G) = G"
  by (simp add: tc_sabs_def Snd)

lemma tc_sabs_type:
  assumes f: "\<And>x. Elem x (typed_S a) \<Longrightarrow> Elem (f x) (typed_S b)"
    and G: "Elem G (typed_M (Arr a b))"
    and nat: "\<And>x. Elem x (typed_S a) \<Longrightarrow> typed_j b (f x) = app G (typed_j a x)"
  shows "Elem (tc_sabs a f G) (typed_S (Arr a b))"
  using f G nat
  by (auto simp: tc_sabs_def typed_compatible_pair Elem_Lambda_Fun Lambda_app)

definition tc_rabs ::
  "otype \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "tc_rabs a f G h = Opair (Lambda (typed_R a) f) (Opair G (typed_seq h))"

lemma tc_rabs_app [simp]:
  "Elem x (typed_R a) \<Longrightarrow> typed_R_app (tc_rabs a f G h) x = f x"
  by (simp add: tc_rabs_def typed_R_app_def Fst Lambda_app)

lemma tc_rabs_s [simp]: "typed_rs (Arr a b) (tc_rabs a f G h) = G"
  by (simp add: tc_rabs_def Fst Snd)

lemma tc_rabs_n [simp]: "typed_rn (Arr a b) (tc_rabs a f G h) n = h n"
  by (simp add: tc_rabs_def Fst Snd)

lemma tc_rabs_type:
  assumes f: "\<And>x. Elem x (typed_R a) \<Longrightarrow> Elem (f x) (typed_R b)"
    and G: "Elem G (typed_S (Arr a b))"
    and h: "\<And>n. Elem (h n) (typed_M (Arr a b))"
    and comp: "typed_j (Arr a b) G = ulim h"
    and ns: "\<And>x. Elem x (typed_R a) \<Longrightarrow>
      typed_rs b (f x) = typed_S_app G (typed_rs a x)"
    and nn: "\<And>x n. Elem x (typed_R a) \<Longrightarrow>
      typed_rn b (f x) n = app (h n) (typed_rn a x n)"
  shows "Elem (tc_rabs a f G h) (typed_R (Arr a b))"
proof -
  have seq: "Elem (typed_seq h) (Fun HOLZF.Nat (typed_M (Arr a b)))"
    by (rule typed_seq_type[where f=h and A="typed_M (Arr a b)"]) (rule h)
  show ?thesis
    unfolding tc_rabs_def typed_R.simps
    apply (simp only: typed_root_arrow_triple)
    using f G seq comp ns nn by (auto simp: Elem_Lambda_Fun Lambda_app)
qed

section \<open>The constant combinator at every type\<close>

context
begin

declare typed_M.simps [simp del] typed_S.simps [simp del] typed_R.simps [simp del]
  typed_j.simps [simp del] typed_rs.simps [simp del] typed_rn.simps [simp del]
  typed_rn_functions [simp del]

definition tc_mK1 :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_mK1 b x = Lambda (typed_M b) (\<lambda>_. x)"

definition tc_mK :: "otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_mK a b = Lambda (typed_M a) (tc_mK1 b)"

lemma tc_mK1_type:
  "Elem x (typed_M a) \<Longrightarrow> Elem (tc_mK1 b x) (typed_M (Arr b a))"
  by (simp add: tc_mK1_def typed_M.simps Elem_Lambda_Fun)

lemma tc_mK_type: "Elem (tc_mK a b) (typed_M (Arr a (Arr b a)))"
  using tc_mK1_type[where a=a and b=b]
  by (simp add: tc_mK_def typed_M.simps Elem_Lambda_Fun)

lemma tc_mK1_app [simp]:
  "Elem y (typed_M b) \<Longrightarrow> app (tc_mK1 b x) y = x"
  by (simp add: tc_mK1_def Lambda_app)

lemma tc_mK_app1 [simp]:
  "Elem x (typed_M a) \<Longrightarrow> app (tc_mK a b) x = tc_mK1 b x"
  by (simp add: tc_mK_def Lambda_app)

definition tc_sK1 :: "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_sK1 a b x = tc_sabs b (\<lambda>_. x) (tc_mK1 b (typed_j a x))"

definition tc_sK :: "otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_sK a b = tc_sabs a (tc_sK1 a b) (tc_mK a b)"

lemma tc_sK1_type:
  assumes xm: "Elem x (typed_S a)"
  shows "Elem (tc_sK1 a b x) (typed_S (Arr b a))"
  unfolding tc_sK1_def
  by (rule tc_sabs_type[where b=a])
    (use xm typed_j_type[OF xm] in
      \<open>auto intro: tc_mK1_type simp: tc_mK1_app typed_j_type\<close>)

lemma tc_sK1_j [simp]:
  "typed_j (Arr b a) (tc_sK1 a b x) = tc_mK1 b (typed_j a x)"
  by (simp add: tc_sK1_def)

lemma tc_sK1_app [simp]:
  "Elem y (typed_S b) \<Longrightarrow> typed_S_app (tc_sK1 a b x) y = x"
  by (simp add: tc_sK1_def)

lemma tc_sK_type: "Elem (tc_sK a b) (typed_S (Arr a (Arr b a)))"
  unfolding tc_sK_def
  by (rule tc_sabs_type[where b="Arr b a"])
    (auto intro: tc_sK1_type tc_mK_type simp: typed_j_type)

lemma tc_sK_j [simp]: "typed_j (Arr a (Arr b a)) (tc_sK a b) = tc_mK a b"
  by (simp add: tc_sK_def)

lemma tc_sK_app1 [simp]:
  "Elem x (typed_S a) \<Longrightarrow> typed_S_app (tc_sK a b) x = tc_sK1 a b x"
  by (simp add: tc_sK_def)

definition tc_rK1 :: "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_rK1 a b x = tc_rabs b (\<lambda>_. x) (tc_sK1 a b (typed_rs a x))
    (\<lambda>n. tc_mK1 b (typed_rn a x n))"

definition tc_rK :: "otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_rK a b = tc_rabs a (tc_rK1 a b) (tc_sK a b) (\<lambda>_. tc_mK a b)"

lemma tc_mK1_ulim:
  assumes xm: "Elem x (typed_R a)"
  shows "ulim (\<lambda>n. tc_mK1 b (typed_rn a x n)) =
    tc_mK1 b (typed_j a (typed_rs a x))"
proof -
  have "ulim (\<lambda>n. tc_mK1 b (typed_rn a x n)) = tc_mK1 b (ulim (typed_rn a x))"
    by (rule ulim_map[where A="explode (typed_M a)" and f="typed_rn a x" and h="tc_mK1 b"])
      (use typed_M_finite[of a] typed_rn_type[OF xm] in \<open>simp_all add: explode_Elem\<close>)
  then show ?thesis by (simp add: typed_R_compatible[OF xm])
qed

lemma tc_rK1_type:
  assumes xm: "Elem x (typed_R a)"
  shows "Elem (tc_rK1 a b x) (typed_R (Arr b a))"
  unfolding tc_rK1_def
  by (rule tc_rabs_type[where b=a])
    (use xm tc_mK1_ulim[OF xm, where b=b] in
      \<open>auto intro: tc_sK1_type tc_mK1_type typed_rs_type typed_rn_type
        simp: typed_rs_type typed_rn_type\<close>)

lemma tc_rK1_s [simp]:
  "typed_rs (Arr b a) (tc_rK1 a b x) = tc_sK1 a b (typed_rs a x)"
  by (simp add: tc_rK1_def)

lemma tc_rK1_n [simp]:
  "typed_rn (Arr b a) (tc_rK1 a b x) n = tc_mK1 b (typed_rn a x n)"
  by (simp add: tc_rK1_def)

lemma tc_rK1_app [simp]:
  "Elem y (typed_R b) \<Longrightarrow> typed_R_app (tc_rK1 a b x) y = x"
  by (simp add: tc_rK1_def)

theorem tc_rK_type: "Elem (tc_rK a b) (typed_R (Arr a (Arr b a)))"
  unfolding tc_rK_def
  by (rule tc_rabs_type[where b="Arr b a"])
    (auto intro: tc_rK1_type tc_sK_type tc_mK_type simp: typed_rs_type typed_rn_type)

theorem tc_rK_apply:
  assumes "Elem x (typed_R a)" "Elem y (typed_R b)"
  shows "typed_R_app (typed_R_app (tc_rK a b) x) y = x"
  using assms by (simp add: tc_rK_def)

text \<open>The K witnesses are actual members of the recursively defined
  function-graph carriers. Each abstraction above has separately proved
  future naturality and terminal ultralimit compatibility.\<close>

section \<open>The substitution combinator at every type\<close>

definition tc_mS2 :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_mS2 a f g = Lambda (typed_M a) (\<lambda>x. app (app f x) (app g x))"

definition tc_mS1 :: "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_mS1 a b f = Lambda (typed_M (Arr a b)) (tc_mS2 a f)"

definition tc_mS :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_mS a b c = Lambda (typed_M (Arr a (Arr b c))) (tc_mS1 a b)"

lemma tc_mS2_type:
  assumes "Elem f (typed_M (Arr a (Arr b c)))" "Elem g (typed_M (Arr a b))"
  shows "Elem (tc_mS2 a f g) (typed_M (Arr a c))"
  using assms unfolding tc_mS2_def
  by (auto simp: typed_M.simps Elem_Lambda_Fun intro: typed_graph_value)

lemma tc_mS1_type:
  assumes "Elem f (typed_M (Arr a (Arr b c)))"
  shows "Elem (tc_mS1 a b f) (typed_M (Arr (Arr a b) (Arr a c)))"
  using tc_mS2_type[where a=a and b=b and c=c and f=f, OF assms]
  by (simp add: tc_mS1_def typed_M.simps Elem_Lambda_Fun)

lemma tc_mS_type:
  "Elem (tc_mS a b c) (typed_M (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))))"
  using tc_mS1_type[where a=a and b=b and c=c]
  by (simp add: tc_mS_def typed_M.simps Elem_Lambda_Fun)

lemma tc_mS2_app [simp]:
  "Elem x (typed_M a) \<Longrightarrow> app (tc_mS2 a f g) x = app (app f x) (app g x)"
  by (simp add: tc_mS2_def Lambda_app)

lemma tc_mS1_app [simp]:
  "Elem g (typed_M (Arr a b)) \<Longrightarrow> app (tc_mS1 a b f) g = tc_mS2 a f g"
  by (simp add: tc_mS1_def Lambda_app)

lemma tc_mS_app1 [simp]:
  "Elem f (typed_M (Arr a (Arr b c))) \<Longrightarrow> app (tc_mS a b c) f = tc_mS1 a b f"
  by (simp add: tc_mS_def Lambda_app)

definition tc_sS2 :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_sS2 a b c f g = tc_sabs a
    (\<lambda>x. typed_S_app (typed_S_app f x) (typed_S_app g x))
    (tc_mS2 a (typed_j (Arr a (Arr b c)) f) (typed_j (Arr a b) g))"

definition tc_sS1 :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_sS1 a b c f = tc_sabs (Arr a b) (tc_sS2 a b c f)
    (tc_mS1 a b (typed_j (Arr a (Arr b c)) f))"

definition tc_sS :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_sS a b c = tc_sabs (Arr a (Arr b c)) (tc_sS1 a b c) (tc_mS a b c)"

lemma tc_sS2_type:
  assumes fm: "Elem f (typed_S (Arr a (Arr b c)))"
    and gm: "Elem g (typed_S (Arr a b))"
  shows "Elem (tc_sS2 a b c f g) (typed_S (Arr a c))"
proof (unfold tc_sS2_def, rule tc_sabs_type)
  show "Elem (typed_S_app (typed_S_app f x) (typed_S_app g x)) (typed_S c)"
    if "Elem x (typed_S a)" for x
    by (rule typed_S_application[where a=b and b=c])
      (rule typed_S_application[OF fm that], rule typed_S_application[OF gm that])
  show "Elem (tc_mS2 a (typed_j (Arr a (Arr b c)) f) (typed_j (Arr a b) g))
      (typed_M (Arr a c))"
    by (rule tc_mS2_type[where b=b]) (rule typed_j_type[OF fm], rule typed_j_type[OF gm])
  fix x assume xm: "Elem x (typed_S a)"
  have fx: "Elem (typed_S_app f x) (typed_S (Arr b c))"
    by (rule typed_S_application[OF fm xm])
  have gx: "Elem (typed_S_app g x) (typed_S b)"
    by (rule typed_S_application[OF gm xm])
  show "typed_j c (typed_S_app (typed_S_app f x) (typed_S_app g x)) =
    app (tc_mS2 a (typed_j (Arr a (Arr b c)) f) (typed_j (Arr a b) g)) (typed_j a x)"
    using typed_S_application_natural[OF fx gx]
      typed_S_application_natural[OF fm xm] typed_S_application_natural[OF gm xm]
    by (simp add: typed_j_type[OF xm])
qed

lemma tc_sS2_j [simp]:
  "typed_j (Arr a c) (tc_sS2 a b c f g) =
    tc_mS2 a (typed_j (Arr a (Arr b c)) f) (typed_j (Arr a b) g)"
  by (simp add: tc_sS2_def)

lemma tc_sS2_app [simp]:
  "Elem x (typed_S a) \<Longrightarrow> typed_S_app (tc_sS2 a b c f g) x =
    typed_S_app (typed_S_app f x) (typed_S_app g x)"
  by (simp add: tc_sS2_def)

lemma tc_sS1_type:
  assumes fm: "Elem f (typed_S (Arr a (Arr b c)))"
  shows "Elem (tc_sS1 a b c f) (typed_S (Arr (Arr a b) (Arr a c)))"
  unfolding tc_sS1_def
  by (rule tc_sabs_type)
    (use fm in \<open>auto intro: tc_sS2_type tc_mS1_type typed_j_type simp: typed_j_type\<close>)

lemma tc_sS1_j [simp]:
  "typed_j (Arr (Arr a b) (Arr a c)) (tc_sS1 a b c f) =
    tc_mS1 a b (typed_j (Arr a (Arr b c)) f)"
  by (simp add: tc_sS1_def)

lemma tc_sS1_app [simp]:
  "Elem g (typed_S (Arr a b)) \<Longrightarrow>
    typed_S_app (tc_sS1 a b c f) g = tc_sS2 a b c f g"
  by (simp add: tc_sS1_def)

lemma tc_sS_type:
  "Elem (tc_sS a b c) (typed_S (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))))"
  unfolding tc_sS_def
  by (rule tc_sabs_type)
    (auto intro: tc_sS1_type tc_mS_type simp: typed_j_type)

lemma tc_sS_j [simp]:
  "typed_j (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) (tc_sS a b c) = tc_mS a b c"
  by (simp add: tc_sS_def)

lemma tc_sS_app1 [simp]:
  "Elem f (typed_S (Arr a (Arr b c))) \<Longrightarrow>
    typed_S_app (tc_sS a b c) f = tc_sS1 a b c f"
  by (simp add: tc_sS_def)

definition tc_rS2 :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_rS2 a b c f g = tc_rabs a
    (\<lambda>x. typed_R_app (typed_R_app f x) (typed_R_app g x))
    (tc_sS2 a b c (typed_rs (Arr a (Arr b c)) f) (typed_rs (Arr a b) g))
    (\<lambda>n. tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n))"

definition tc_rS1 :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "tc_rS1 a b c f = tc_rabs (Arr a b) (tc_rS2 a b c f)
    (tc_sS1 a b c (typed_rs (Arr a (Arr b c)) f))
    (\<lambda>n. tc_mS1 a b (typed_rn (Arr a (Arr b c)) f n))"

definition tc_rS :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "tc_rS a b c = tc_rabs (Arr a (Arr b c)) (tc_rS1 a b c)
    (tc_sS a b c) (\<lambda>_. tc_mS a b c)"

lemma tc_mS2_ulim:
  assumes fm: "Elem f (typed_R (Arr a (Arr b c)))" and gm: "Elem g (typed_R (Arr a b))"
  shows "ulim (\<lambda>n. tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n)) =
    tc_mS2 a (typed_j (Arr a (Arr b c)) (typed_rs (Arr a (Arr b c)) f))
      (typed_j (Arr a b) (typed_rs (Arr a b) g))"
proof -
  have lim: "ulim (\<lambda>n. tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n)) =
    tc_mS2 a (ulim (typed_rn (Arr a (Arr b c)) f)) (ulim (typed_rn (Arr a b) g))"
    by (rule ulim_binary[where A="explode (typed_M (Arr a (Arr b c)))"
      and B="explode (typed_M (Arr a b))" and f="typed_rn (Arr a (Arr b c)) f"
      and g="typed_rn (Arr a b) g" and h="tc_mS2 a"])
      (use typed_M_finite[of "Arr a (Arr b c)"] typed_M_finite[of "Arr a b"]
        typed_rn_type[OF fm] typed_rn_type[OF gm] in \<open>simp_all add: explode_Elem\<close>)
  show ?thesis using lim typed_R_compatible[OF fm] typed_R_compatible[OF gm] by simp
qed

lemma tc_rS2_type:
  assumes fm: "Elem f (typed_R (Arr a (Arr b c)))" and gm: "Elem g (typed_R (Arr a b))"
  shows "Elem (tc_rS2 a b c f g) (typed_R (Arr a c))"
proof (unfold tc_rS2_def, rule tc_rabs_type)
  show "Elem (typed_R_app (typed_R_app f x) (typed_R_app g x)) (typed_R c)"
    if "Elem x (typed_R a)" for x
    by (rule typed_R_application[where a=b and b=c])
      (rule typed_R_application[OF fm that], rule typed_R_application[OF gm that])
  show "Elem (tc_sS2 a b c (typed_rs (Arr a (Arr b c)) f) (typed_rs (Arr a b) g))
      (typed_S (Arr a c))"
    by (rule tc_sS2_type) (rule typed_rs_type[OF fm], rule typed_rs_type[OF gm])
  show "Elem (tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n))
      (typed_M (Arr a c))" for n
    by (rule tc_mS2_type[where b=b]) (rule typed_rn_type[OF fm], rule typed_rn_type[OF gm])
  show "typed_j (Arr a c) (tc_sS2 a b c (typed_rs (Arr a (Arr b c)) f) (typed_rs (Arr a b) g)) =
    ulim (\<lambda>n. tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n))"
    using tc_mS2_ulim[OF fm gm] by (simp only: tc_sS2_j)
  show "typed_rs c (typed_R_app (typed_R_app f x) (typed_R_app g x)) =
    typed_S_app (tc_sS2 a b c (typed_rs (Arr a (Arr b c)) f) (typed_rs (Arr a b) g)) (typed_rs a x)"
    if xm: "Elem x (typed_R a)" for x
    using typed_R_application_s[OF typed_R_application[OF fm xm] typed_R_application[OF gm xm]]
      typed_R_application_s[OF fm xm] typed_R_application_s[OF gm xm]
    by (simp add: typed_rs_type[OF xm])
  show "typed_rn c (typed_R_app (typed_R_app f x) (typed_R_app g x)) n =
    app (tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n)) (typed_rn a x n)"
    if xm: "Elem x (typed_R a)" for x n
    using typed_R_application_n[OF typed_R_application[OF fm xm] typed_R_application[OF gm xm], of n]
      typed_R_application_n[OF fm xm, of n] typed_R_application_n[OF gm xm, of n]
    by (simp add: typed_rn_type[OF xm])
qed

lemma tc_rS2_s [simp]:
  "typed_rs (Arr a c) (tc_rS2 a b c f g) =
    tc_sS2 a b c (typed_rs (Arr a (Arr b c)) f) (typed_rs (Arr a b) g)"
  by (simp add: tc_rS2_def)

lemma tc_rS2_n [simp]:
  "typed_rn (Arr a c) (tc_rS2 a b c f g) n =
    tc_mS2 a (typed_rn (Arr a (Arr b c)) f n) (typed_rn (Arr a b) g n)"
  by (simp add: tc_rS2_def)

lemma tc_rS2_app [simp]:
  "Elem x (typed_R a) \<Longrightarrow> typed_R_app (tc_rS2 a b c f g) x =
    typed_R_app (typed_R_app f x) (typed_R_app g x)"
  by (simp add: tc_rS2_def)

lemma tc_mS1_ulim:
  assumes fm: "Elem f (typed_R (Arr a (Arr b c)))"
  shows "ulim (\<lambda>n. tc_mS1 a b (typed_rn (Arr a (Arr b c)) f n)) =
    tc_mS1 a b (typed_j (Arr a (Arr b c)) (typed_rs (Arr a (Arr b c)) f))"
proof -
  have lim: "ulim (\<lambda>n. tc_mS1 a b (typed_rn (Arr a (Arr b c)) f n)) =
    tc_mS1 a b (ulim (typed_rn (Arr a (Arr b c)) f))"
    by (rule ulim_map[where A="explode (typed_M (Arr a (Arr b c)))"
      and f="typed_rn (Arr a (Arr b c)) f" and h="tc_mS1 a b"])
      (use typed_M_finite[of "Arr a (Arr b c)"] typed_rn_type[OF fm]
        in \<open>simp_all add: explode_Elem\<close>)
  show ?thesis using lim typed_R_compatible[OF fm] by simp
qed

lemma tc_rS1_type:
  assumes fm: "Elem f (typed_R (Arr a (Arr b c)))"
  shows "Elem (tc_rS1 a b c f) (typed_R (Arr (Arr a b) (Arr a c)))"
  unfolding tc_rS1_def
  by (rule tc_rabs_type)
    (use fm tc_mS1_ulim[OF fm] in
      \<open>auto intro: tc_rS2_type tc_sS1_type tc_mS1_type typed_rs_type typed_rn_type
        simp: typed_rs_type typed_rn_type\<close>)

lemma tc_rS1_s [simp]:
  "typed_rs (Arr (Arr a b) (Arr a c)) (tc_rS1 a b c f) =
    tc_sS1 a b c (typed_rs (Arr a (Arr b c)) f)"
  by (simp add: tc_rS1_def)

lemma tc_rS1_n [simp]:
  "typed_rn (Arr (Arr a b) (Arr a c)) (tc_rS1 a b c f) n =
    tc_mS1 a b (typed_rn (Arr a (Arr b c)) f n)"
  by (simp add: tc_rS1_def)

lemma tc_rS1_app [simp]:
  "Elem g (typed_R (Arr a b)) \<Longrightarrow>
    typed_R_app (tc_rS1 a b c f) g = tc_rS2 a b c f g"
  by (simp add: tc_rS1_def)

theorem tc_rS_type:
  "Elem (tc_rS a b c) (typed_R (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))))"
  unfolding tc_rS_def
  by (rule tc_rabs_type)
    (auto intro: tc_rS1_type tc_sS_type tc_mS_type simp: typed_rs_type typed_rn_type)

theorem tc_rS_apply:
  assumes "Elem f (typed_R (Arr a (Arr b c)))" "Elem g (typed_R (Arr a b))"
    "Elem x (typed_R a)"
  shows "typed_R_app (typed_R_app (typed_R_app (tc_rS a b c) f) g) x =
    typed_R_app (typed_R_app f x) (typed_R_app g x)"
  using assms by (simp add: tc_rS_def)

text \<open>These are concrete K and S objects and their application laws
  at every type, not an assertion that arbitrary HOL functions admit
  abstraction in the hierarchy. The independent source-model interpretation
  and its logical soundness remain separate obligations.\<close>

end

declare typed_M.simps [simp] typed_S.simps [simp] typed_R.simps [simp]
  typed_j.simps [simp] typed_rs.simps [simp] typed_rn.simps [simp]
  typed_rn_functions [simp]

end
