theory Typed_Root_Lifts
  imports Typed_Compatible_Lifts Finite_Ultralimit
begin

section \<open>Bounded sequences and their finite-type ultralimits\<close>

definition typed_seq :: "(nat \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "typed_seq f = Lambda HOLZF.Nat (\<lambda>N. f (Nat2nat N))"

definition typed_at :: "ZF \<Rightarrow> nat \<Rightarrow> ZF" where
  "typed_at Q n = app Q (nat2Nat n)"

lemma typed_at_seq [simp]: "typed_at (typed_seq f) n = f n"
  by (simp add: typed_at_def typed_seq_def Lambda_app Elem_nat2Nat_Nat)

lemma typed_at_seq_fun [simp]: "typed_at (typed_seq f) = f"
  by (rule ext) simp

lemma typed_seq_type:
  "(\<And>n. Elem (f n) A) \<Longrightarrow> Elem (typed_seq f) (Fun HOLZF.Nat A)"
  by (simp add: typed_seq_def Elem_Lambda_Fun)

lemma typed_at_type:
  "Elem Q (Fun HOLZF.Nat A) \<Longrightarrow> Elem (typed_at Q n) A"
  unfolding typed_at_def by (rule typed_graph_value) (assumption, rule Elem_nat2Nat_Nat)

lemma typed_ulim_type:
  assumes "\<And>n. Elem (f n) (typed_M a)"
  shows "Elem (ulim f) (typed_M a)"
proof -
  have "ulim f \<in> explode (typed_M a)"
    by (rule ulim_in_carrier[OF typed_M_finite])
      (use assms in \<open>simp add: explode_Elem\<close>)
  then show ?thesis by (simp add: explode_Elem)
qed

lemma typed_ulim_app:
  assumes "\<And>n. Elem (f n) (typed_M (Arr a b))"
    "\<And>n. Elem (x n) (typed_M a)"
  shows "ulim (\<lambda>n. app (f n) (x n)) = app (ulim f) (ulim x)"
  by (rule ulim_binary[where A="explode (typed_M (Arr a b))"
      and B="explode (typed_M a)" and f=f and g=x and h=app])
    (use assms typed_M_finite[of "Arr a b"] typed_M_finite[of a]
      in \<open>simp_all add: explode_Elem\<close>)

section \<open>The exact lifting step needed at a root arrow type\<close>

text \<open>The following lemma is the joint-surjectivity induction step,
  stated with explicit previously constructed argument and result carriers.
  The hypotheses concern only lower types, never the arrow being built.
  The witness is an actual ZF graph on the bounded root argument set.
  No modelhood, logical closure, or target surjectivity is assumed.\<close>

definition typed_root_arrow ::
  "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow>
    (ZF \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow>
    (ZF \<Rightarrow> nat \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> nat \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "typed_root_arrow a b A B sA sB nA nB =
    Sep (CartProd (Fun A B)
      (CartProd (typed_S (Arr a b)) (Fun HOLZF.Nat (typed_M (Arr a b)))))
      (\<lambda>p. typed_j (Arr a b) (Fst (Snd p)) = ulim (typed_at (Snd (Snd p))) \<and>
        (\<forall>x. Elem x A \<longrightarrow>
          sB (app (Fst p) x) = typed_S_app (Fst (Snd p)) (sA x) \<and>
          (\<forall>n. nB (app (Fst p) x) n = app (typed_at (Snd (Snd p)) n) (nA x n))))"

lemma typed_root_arrow_triple:
  "Elem (Opair F (Opair G (typed_seq h))) (typed_root_arrow a b A B sA sB nA nB)
    \<longleftrightarrow> Elem F (Fun A B) \<and> Elem G (typed_S (Arr a b)) \<and>
      Elem (typed_seq h) (Fun HOLZF.Nat (typed_M (Arr a b))) \<and>
      typed_j (Arr a b) G = ulim h \<and>
      (\<forall>x. Elem x A \<longrightarrow> sB (app F x) = typed_S_app G (sA x) \<and>
        (\<forall>n. nB (app F x) n = app (h n) (nA x n)))"
  by (simp add: typed_root_arrow_def Sep CartProd Opair Fst Snd typed_at_seq)

lemma typed_root_arrowE:
  assumes "Elem p (typed_root_arrow a b A B sA sB nA nB)"
  obtains F G Q where "p = Opair F (Opair G Q)"
    "Elem F (Fun A B)" "Elem G (typed_S (Arr a b))"
    "Elem Q (Fun HOLZF.Nat (typed_M (Arr a b)))"
    "typed_j (Arr a b) G = ulim (typed_at Q)"
    "\<And>x. Elem x A \<Longrightarrow> sB (app F x) = typed_S_app G (sA x)"
    "\<And>x n. Elem x A \<Longrightarrow> nB (app F x) n = app (typed_at Q n) (nA x n)"
  using assms that
  by (auto simp: typed_root_arrow_def Sep CartProd Fst Snd)

theorem typed_root_arrow_joint_lift:
  assumes sA_type: "\<And>x. Elem x A \<Longrightarrow> Elem (sA x) (typed_S a)"
    and nA_type: "\<And>x n. Elem x A \<Longrightarrow> Elem (nA x n) (typed_M a)"
    and A_compatible: "\<And>x. Elem x A \<Longrightarrow> typed_j a (sA x) = ulim (nA x)"
    and B_joint: "\<And>y z. Elem y (typed_S b) \<Longrightarrow>
      (\<And>n. Elem (z n) (typed_M b)) \<Longrightarrow> typed_j b y = ulim z \<Longrightarrow>
      \<exists>v. Elem v B \<and> sB v = y \<and> (\<forall>n. nB v n = z n)"
    and G: "Elem G (typed_S (Arr a b))"
    and h: "\<And>n. Elem (h n) (typed_M (Arr a b))"
    and compat: "typed_j (Arr a b) G = ulim h"
  shows "\<exists>F. Elem (Opair F (Opair G (typed_seq h)))
    (typed_root_arrow a b A B sA sB nA nB)"
proof -
  have outputs: "\<exists>v. Elem v B \<and> sB v = typed_S_app G (sA x) \<and>
      (\<forall>n. nB v n = app (h n) (nA x n))" if xm: "Elem x A" for x
  proof -
    have sm: "Elem (typed_S_app G (sA x)) (typed_S b)"
      by (rule typed_S_application[OF G sA_type[OF xm]])
    have nm: "Elem (app (h n) (nA x n)) (typed_M b)" for n
      by (rule typed_M_application[OF h nA_type[OF xm]])
    have coherence: "typed_j b (typed_S_app G (sA x)) =
      ulim (\<lambda>n. app (h n) (nA x n))"
      using typed_S_application_natural[OF G sA_type[OF xm]]
        typed_ulim_app[where a=a and b=b and f=h and x="nA x",
          OF h nA_type[OF xm]] compat
      by (simp add: A_compatible[OF xm])
    show ?thesis by (rule B_joint[OF sm nm coherence])
  qed
  define f where "f x = (SOME v. Elem v B \<and> sB v = typed_S_app G (sA x) \<and>
      (\<forall>n. nB v n = app (h n) (nA x n)))" for x
  have f: "Elem (f x) B \<and> sB (f x) = typed_S_app G (sA x) \<and>
      (\<forall>n. nB (f x) n = app (h n) (nA x n))" if "Elem x A" for x
    unfolding f_def by (rule someI_ex[OF outputs[OF that]])
  have "Elem (Opair (Lambda A f) (Opair G (typed_seq h)))
      (typed_root_arrow a b A B sA sB nA nB)"
    using G h compat f typed_seq_type[OF h]
    by (auto simp: typed_root_arrow_triple Elem_Lambda_Fun Lambda_app)
  then show ?thesis by blast
qed

text \<open>Typed_Root_Hierarchy instantiates this lifting step recursively
  at the concrete root base carriers and proves the individual action
  surjections. The later Typed_Source and Typed_Paper theories perform
  the recoding and independent model proofs. This leaf establishes the
  lifting step, not those downstream results by itself.\<close>

end
