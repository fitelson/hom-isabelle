theory Typed_Finite_Hierarchy
  imports "HOL-ZF.HOLZF" "Bacon_Base.Bacon_Types"
begin

text \<open>The constant terminal model has an actual ZF set at every
  object-language type. No single HOL carrier is postulated to contain
  its own full function space. This is carrier groundwork, not yet an
  interpretation of the independent Classicism model predicate.\<close>

definition typed_two :: ZF where
  "typed_two = Upair Empty (Singleton Empty)"

fun typed_M :: "otype \<Rightarrow> ZF" where
  "typed_M Ind = Singleton Empty"
| "typed_M Prop = typed_two"
| "typed_M (Arr a b) = Fun (typed_M a) (typed_M b)"

lemma typed_explode_singleton [simp]: "explode (Singleton x) = {x}"
  by (auto simp: explode_Elem Singleton)

lemma typed_explode_upair [simp]: "explode (Upair x y) = {x,y}"
  by (auto simp: explode_Elem Upair)

lemma typed_explode_Sep:
  "explode (Sep A P) = {x \<in> explode A. P x}"
  by (auto simp: explode_Elem Sep)

lemma typed_finite_power:
  assumes "finite (explode A)"
  shows "finite (explode (Power A))"
proof -
  have bound: "explode ` explode (Power A) \<subseteq> Pow (explode A)"
    by (auto simp: explode_Elem Power subset_def)
  have "finite (explode ` explode (Power A))"
    by (rule finite_subset[OF bound]) (simp add: assms)
  then show ?thesis
    using inj_explode by (meson finite_imageD inj_on_subset subset_UNIV)
qed

lemma typed_finite_fun:
  assumes "finite (explode A)" "finite (explode B)"
  shows "finite (explode (Fun A B))"
proof -
  have pair: "finite (explode (CartProd A B))"
    using assms by (simp add: explode_CartProd_eq)
  have pow: "finite (explode (Power (CartProd A B)))"
    by (rule typed_finite_power[OF pair])
  show ?thesis
    using pow by (simp add: Fun_def PFun_def typed_explode_Sep)
qed

lemma typed_graph_value:
  assumes "Elem F (Fun A B)" "Elem x A"
  shows "Elem (app F x) B"
proof -
  obtain f where "F = Lambda A f"
    using Elem_Fun_Lambda[OF assms(1)] by blast
  then show ?thesis
    using assms by (auto simp: Elem_Lambda_Fun Lambda_app)
qed

lemma typed_graph_ext:
  assumes "Elem F (Fun A B)" "Elem G (Fun A C)"
    and "\<And>x. Elem x A \<Longrightarrow> app F x = app G x"
  shows "F = G"
proof -
  obtain f g where fg: "F = Lambda A f" "G = Lambda A g"
    using Elem_Fun_Lambda assms(1,2) by blast
  show ?thesis using assms(3) by (simp add: fg Lambda_ext Lambda_app)
qed

theorem typed_M_finite: "finite (explode (typed_M a))"
  by (induction a) (simp_all add: typed_two_def typed_finite_fun)

fun typed_default :: "otype \<Rightarrow> ZF" where
  "typed_default Ind = Empty"
| "typed_default Prop = Empty"
| "typed_default (Arr a b) = Lambda (typed_M a) (\<lambda>_. typed_default b)"

theorem typed_M_default: "Elem (typed_default a) (typed_M a)"
  by (induction a) (simp_all add: Singleton typed_two_def Upair Elem_Lambda_Fun)

theorem typed_M_nonempty: "explode (typed_M a) \<noteq> {}"
  using typed_M_default[of a] by (auto simp: explode_Elem)

lemma typed_M_application:
  "Elem F (typed_M (Arr a b)) \<Longrightarrow> Elem x (typed_M a) \<Longrightarrow>
    Elem (app F x) (typed_M b)"
  by (auto intro: typed_graph_value)

lemma typed_M_abstraction:
  "(\<And>x. Elem x (typed_M a) \<Longrightarrow> Elem (f x) (typed_M b)) \<Longrightarrow>
    Elem (Lambda (typed_M a) f) (typed_M (Arr a b))"
  by (simp add: Elem_Lambda_Fun)

lemma typed_two_distinct: "Empty \<noteq> Singleton Empty"
  by (metis Singleton_nonEmpty)

end
