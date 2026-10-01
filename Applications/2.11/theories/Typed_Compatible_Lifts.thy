theory Typed_Compatible_Lifts
  imports Typed_Finite_Hierarchy
begin

section \<open>Surjective lifting through actual function graphs\<close>

definition typed_compatible ::
  "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow>
    (ZF \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "typed_compatible A B C D j k =
    Sep (CartProd (Fun A B) (Fun C D))
      (\<lambda>p. \<forall>x. Elem x A \<longrightarrow>
        k (app (Fst p) x) = app (Snd p) (j x))"

lemma typed_compatible_pair:
  "Elem (Opair F G) (typed_compatible A B C D j k) \<longleftrightarrow>
    Elem F (Fun A B) \<and> Elem G (Fun C D) \<and>
    (\<forall>x. Elem x A \<longrightarrow> k (app F x) = app G (j x))"
  by (simp add: typed_compatible_def Sep CartProd Opair Fst Snd)

lemma typed_compatibleE:
  assumes "Elem p (typed_compatible A B C D j k)"
  obtains F G where "p = Opair F G" "Elem F (Fun A B)"
    "Elem G (Fun C D)"
    "\<And>x. Elem x A \<Longrightarrow> k (app F x) = app G (j x)"
  using assms that
  by (auto simp: typed_compatible_def Sep CartProd Fst Snd)

lemma typed_compatible_finite:
  assumes "finite (explode A)" "finite (explode B)"
    "finite (explode C)" "finite (explode D)"
  shows "finite (explode (typed_compatible A B C D j k))"
  using typed_finite_fun[OF assms(1,2)] typed_finite_fun[OF assms(3,4)]
  by (simp add: typed_compatible_def typed_explode_Sep explode_CartProd_eq)

lemma typed_compatible_lift:
  assumes j_type: "\<And>x. Elem x A \<Longrightarrow> Elem (j x) C"
    and k_onto: "\<And>y. Elem y D \<Longrightarrow> \<exists>b. Elem b B \<and> k b = y"
    and gm: "Elem G (Fun C D)"
  shows "\<exists>F. Elem (Opair F G) (typed_compatible A B C D j k)"
proof -
  define f where "f x = (SOME b. Elem b B \<and> k b = app G (j x))" for x
  have f: "Elem (f x) B \<and> k (f x) = app G (j x)" if "Elem x A" for x
  proof -
    have "Elem (app G (j x)) D"
      by (rule typed_graph_value[OF gm j_type[OF that]])
    then have "\<exists>b. Elem b B \<and> k b = app G (j x)"
      by (rule k_onto)
    then show ?thesis unfolding f_def by (rule someI_ex)
  qed
  have "Elem (Opair (Lambda A f) G) (typed_compatible A B C D j k)"
    using f gm by (auto simp: typed_compatible_pair Elem_Lambda_Fun Lambda_app)
  then show ?thesis by blast
qed

section \<open>The intermediate two-world hierarchy\<close>

fun typed_j :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_j Ind x = x"
| "typed_j Prop x = Snd x"
| "typed_j (Arr a b) x = Snd x"

fun typed_S :: "otype \<Rightarrow> ZF" where
  "typed_S Ind = Singleton Empty"
| "typed_S Prop = CartProd typed_two typed_two"
| "typed_S (Arr a b) = typed_compatible (typed_S a) (typed_S b)
    (typed_M a) (typed_M b) (typed_j a) (typed_j b)"

theorem typed_S_finite: "finite (explode (typed_S a))"
proof (induction a)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by (simp add: explode_CartProd_eq typed_two_def)
next
  case (Arr a b)
  show ?case
    unfolding typed_S.simps
    by (rule typed_compatible_finite[OF Arr.IH(1) Arr.IH(2)
      typed_M_finite typed_M_finite])
qed

theorem typed_j_type:
  "Elem x (typed_S a) \<Longrightarrow> Elem (typed_j a x) (typed_M a)"
proof (induction a arbitrary: x)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by (auto simp: CartProd Snd)
next
  case (Arr a b)
  obtain F G where "x = Opair F G" "Elem G (Fun (typed_M a) (typed_M b))"
    using Arr.prems by (auto elim: typed_compatibleE)
  then show ?case by (simp add: Snd)
qed

theorem typed_j_onto:
  "Elem y (typed_M a) \<Longrightarrow> \<exists>x. Elem x (typed_S a) \<and> typed_j a x = y"
proof (induction a arbitrary: y)
  case Ind
  then show ?case by auto
next
  case Prop
  have "Elem (Opair Empty y) (typed_S Prop)"
    using Prop.prems by (auto simp: CartProd Opair typed_two_def Upair)
  moreover have "typed_j Prop (Opair Empty y) = y" by (simp add: Snd)
  ultimately show ?case by blast
next
  case (Arr a b)
  have gm: "Elem y (Fun (typed_M a) (typed_M b))"
    using Arr.prems by simp
  obtain F where lift:
    "Elem (Opair F y) (typed_compatible (typed_S a) (typed_S b)
      (typed_M a) (typed_M b) (typed_j a) (typed_j b))"
    using typed_compatible_lift[where A="typed_S a" and B="typed_S b"
      and C="typed_M a" and D="typed_M b" and j="typed_j a" and k="typed_j b"
      and G=y, OF typed_j_type Arr.IH(2) gm] by blast
  have "Elem (Opair F y) (typed_S (Arr a b)) \<and>
    typed_j (Arr a b) (Opair F y) = y"
    using lift by (simp add: Snd)
  then show ?case by blast
qed

theorem typed_S_nonempty: "explode (typed_S a) \<noteq> {}"
  using typed_j_onto[OF typed_M_default[of a]]
  by (auto simp: explode_Elem)

definition typed_S_app :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_S_app F x = app (Fst F) x"

lemma typed_S_application:
  assumes "Elem F (typed_S (Arr a b))" "Elem x (typed_S a)"
  shows "Elem (typed_S_app F x) (typed_S b)"
proof -
  obtain G H where "F = Opair G H" "Elem G (Fun (typed_S a) (typed_S b))"
    using assms(1) by (auto elim: typed_compatibleE)
  then show ?thesis
    using typed_graph_value assms(2) by (simp add: typed_S_app_def Fst; blast)
qed

lemma typed_S_application_natural:
  assumes "Elem F (typed_S (Arr a b))" "Elem x (typed_S a)"
  shows "typed_j b (typed_S_app F x) = app (typed_j (Arr a b) F) (typed_j a x)"
  using assms by (auto simp: typed_S_app_def Fst Snd elim: typed_compatibleE)

text \<open>Surjectivity at the argument type ensures that the future graph
  is determined by the current application graph. Thus the pair encoding
  does not introduce extensionally duplicate higher-order objects.\<close>

theorem typed_S_extensional:
  assumes fm: "Elem F (typed_S (Arr a b))"
    and gm: "Elem G (typed_S (Arr a b))"
    and same: "\<And>x. Elem x (typed_S a) \<Longrightarrow> typed_S_app F x = typed_S_app G x"
  shows "F = G"
proof -
  obtain F0 F1 where F: "F = Opair F0 F1"
    and F0: "Elem F0 (Fun (typed_S a) (typed_S b))"
    and F1: "Elem F1 (Fun (typed_M a) (typed_M b))"
    and Fn: "\<And>x. Elem x (typed_S a) \<Longrightarrow>
      typed_j b (app F0 x) = app F1 (typed_j a x)"
    using fm by (auto elim: typed_compatibleE)
  obtain G0 G1 where G: "G = Opair G0 G1"
    and G0: "Elem G0 (Fun (typed_S a) (typed_S b))"
    and G1: "Elem G1 (Fun (typed_M a) (typed_M b))"
    and Gn: "\<And>x. Elem x (typed_S a) \<Longrightarrow>
      typed_j b (app G0 x) = app G1 (typed_j a x)"
    using gm by (auto elim: typed_compatibleE)
  have zero: "F0 = G0"
    by (rule typed_graph_ext[OF F0 G0])
      (use same in \<open>simp add: F G typed_S_app_def Fst\<close>)
  have one: "F1 = G1"
  proof (rule typed_graph_ext[OF F1 G1])
    fix y assume ym: "Elem y (typed_M a)"
    obtain x where xm: "Elem x (typed_S a)" and xy: "typed_j a x = y"
      using typed_j_onto[OF ym] by blast
    show "app F1 y = app G1 y"
      using Fn[OF xm] Gn[OF xm] by (simp add: zero xy)
  qed
  show ?thesis by (simp add: F G zero one)
qed

end
