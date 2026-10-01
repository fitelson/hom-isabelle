theory Typed_Root_Hierarchy
  imports Typed_Root_Lifts
begin

section \<open>Concrete recursive root carriers\<close>

fun typed_rs :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_rs Ind x = x"
| "typed_rs Prop x = Opair (Fst (Snd x)) (ulim (typed_at (Snd (Snd x))))"
| "typed_rs (Arr a b) x = Fst (Snd x)"

fun typed_rn :: "otype \<Rightarrow> ZF \<Rightarrow> nat \<Rightarrow> ZF" where
  "typed_rn Ind x n = x"
| "typed_rn Prop x n = typed_at (Snd (Snd x)) n"
| "typed_rn (Arr a b) x n = typed_at (Snd (Snd x)) n"

lemma typed_rn_functions [simp]:
  "typed_rn Ind x = (\<lambda>n. x)"
  "typed_rn Prop x = typed_at (Snd (Snd x))"
  "typed_rn (Arr a b) x = typed_at (Snd (Snd x))"
  by (rule ext, simp)+

fun typed_R :: "otype \<Rightarrow> ZF" where
  "typed_R Ind = Singleton Empty"
| "typed_R Prop = CartProd typed_two (CartProd typed_two (Fun HOLZF.Nat typed_two))"
| "typed_R (Arr a b) = typed_root_arrow a b (typed_R a) (typed_R b)
    (typed_rs a) (typed_rs b) (typed_rn a) (typed_rn b)"

lemma typed_R_propE:
  assumes "Elem p (typed_R Prop)"
  obtains a b Q where "p = Opair a (Opair b Q)"
    "Elem a typed_two" "Elem b typed_two" "Elem Q (Fun HOLZF.Nat typed_two)"
  using assms that by (auto simp: CartProd)

lemma typed_R_propI:
  "Elem a typed_two \<Longrightarrow> Elem b typed_two \<Longrightarrow>
    (\<And>n. Elem (h n) typed_two) \<Longrightarrow>
    Elem (Opair a (Opair b (typed_seq h))) (typed_R Prop)"
  using typed_seq_type[of h typed_two]
  by (auto simp: CartProd)

theorem typed_rs_type:
  assumes xm: "Elem x (typed_R a)"
  shows "Elem (typed_rs a x) (typed_S a)"
proof (cases a)
  case Ind
  then show ?thesis using xm by simp
next
  case Prop
  obtain r s Q where shape: "x = Opair r (Opair s Q)"
    and sm: "Elem s typed_two" and qm: "Elem Q (Fun HOLZF.Nat typed_two)"
    using xm Prop by (auto simp: CartProd)
  have lim: "Elem (ulim (typed_at Q)) typed_two"
    using typed_ulim_type[where a=Prop, of "typed_at Q"] typed_at_type[OF qm]
    by simp
  show ?thesis using sm lim by (auto simp: Prop shape Fst Snd CartProd)
next
  case (Arr b c)
  then show ?thesis using xm
    by (auto simp: Fst Snd elim: typed_root_arrowE)
qed

theorem typed_rn_type:
  assumes xm: "Elem x (typed_R a)"
  shows "Elem (typed_rn a x n) (typed_M a)"
proof (cases a)
  case Ind
  then show ?thesis using xm by simp
next
  case Prop
  then show ?thesis using xm typed_at_type
    by (auto simp: Fst Snd CartProd)
next
  case (Arr b c)
  then show ?thesis using xm typed_at_type
    by (auto simp: Fst Snd elim: typed_root_arrowE)
qed

theorem typed_R_compatible:
  assumes xm: "Elem x (typed_R a)"
  shows "typed_j a (typed_rs a x) = ulim (typed_rn a x)"
proof (cases a)
  case Ind
  then show ?thesis by simp
next
  case Prop
  then show ?thesis by (simp add: Snd)
next
  case (Arr b c)
  then show ?thesis using xm
    by (auto simp: Fst Snd elim: typed_root_arrowE)
qed

text \<open>This is the simultaneous all-type surjectivity theorem. A
  compatible intermediate object and a complete terminal sequence are
  lifted together, not just separately along each individual arrow.\<close>

theorem typed_R_joint_surjective:
  assumes ym: "Elem y (typed_S a)"
    and hm: "\<And>n. Elem (h n) (typed_M a)"
    and compat: "typed_j a y = ulim h"
  shows "\<exists>x. Elem x (typed_R a) \<and> typed_rs a x = y \<and>
    (\<forall>n. typed_rn a x n = h n)"
  using ym hm compat
proof (induction a arbitrary: y h)
  case Ind
  have y: "y = Empty" using Ind.prems(1) by (simp add: Singleton)
  have h: "h n = Empty" for n using Ind.prems(2)[of n] by (simp add: Singleton)
  show ?case by (rule exI[of _ Empty]) (simp add: Singleton y h)
next
  case Prop
  obtain s u where y: "y = Opair s u" and s: "Elem s typed_two"
    and u: "Elem u typed_two"
    using Prop.prems(1) by (auto simp: CartProd)
  have h: "Elem (h n) typed_two" for n using Prop.prems(2) by simp
  have limit: "u = ulim h" using Prop.prems(3) by (simp add: y Snd)
  let ?x = "Opair Empty (Opair s (typed_seq h))"
  have member: "Elem ?x (typed_R Prop)"
    by (rule typed_R_propI[OF _ s h]) (simp add: typed_two_def Upair)
  show ?case
    by (rule exI[of _ ?x], rule conjI[OF member]) (simp add: y limit Fst Snd)
next
  case (Arr a b)
  obtain F where fm:
    "Elem (Opair F (Opair y (typed_seq h))) (typed_root_arrow a b
      (typed_R a) (typed_R b) (typed_rs a) (typed_rs b) (typed_rn a) (typed_rn b))"
    using typed_root_arrow_joint_lift[where a=a and b=b
      and A="typed_R a" and B="typed_R b" and sA="typed_rs a" and sB="typed_rs b"
      and nA="typed_rn a" and nB="typed_rn b" and G=y and h=h,
      OF typed_rs_type typed_rn_type
      typed_R_compatible Arr.IH(2) Arr.prems(1) Arr.prems(2) Arr.prems(3)] by blast
  show ?case
    by (rule exI[of _ "Opair F (Opair y (typed_seq h))"])
      (simp add: fm Fst Snd)
qed

theorem typed_rs_surjective:
  assumes "Elem y (typed_S a)"
  shows "\<exists>x. Elem x (typed_R a) \<and> typed_rs a x = y"
proof -
  have m: "Elem (typed_j a y) (typed_M a)" by (rule typed_j_type[OF assms])
  have c: "typed_j a y = ulim (\<lambda>n. typed_j a y)" by simp
  show ?thesis using typed_R_joint_surjective[OF assms m c] by blast
qed

theorem typed_R_nonempty: "explode (typed_R a) \<noteq> {}"
proof -
  obtain y where "Elem y (typed_S a)"
    using typed_S_nonempty[of a] by (auto simp: explode_Elem)
  then obtain x where "Elem x (typed_R a)"
    using typed_rs_surjective by blast
  then show ?thesis by (auto simp: explode_Elem)
qed

theorem typed_rn_surjective:
  assumes "Elem v (typed_M a)"
  shows "\<exists>x. Elem x (typed_R a) \<and> typed_rn a x n = v"
proof -
  obtain y where ym: "Elem y (typed_S a)" and jy: "typed_j a y = v"
    using typed_j_onto[OF assms] by blast
  have c: "typed_j a y = ulim (\<lambda>n. v)" by (simp add: jy)
  obtain x where "Elem x (typed_R a)" "\<forall>n. typed_rn a x n = v"
    using typed_R_joint_surjective[OF ym assms c] by blast
  then show ?thesis by blast
qed

definition typed_R_app :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_R_app F x = app (Fst F) x"

theorem typed_R_application:
  assumes "Elem F (typed_R (Arr a b))" "Elem x (typed_R a)"
  shows "Elem (typed_R_app F x) (typed_R b)"
  using assms typed_graph_value
  by (auto simp: typed_R_app_def Fst Snd elim: typed_root_arrowE)

theorem typed_R_application_s:
  assumes "Elem F (typed_R (Arr a b))" "Elem x (typed_R a)"
  shows "typed_rs b (typed_R_app F x) =
    typed_S_app (typed_rs (Arr a b) F) (typed_rs a x)"
  using assms by (auto simp: typed_R_app_def Fst Snd elim: typed_root_arrowE)

theorem typed_R_application_n:
  assumes "Elem F (typed_R (Arr a b))" "Elem x (typed_R a)"
  shows "typed_rn b (typed_R_app F x) n =
    app (typed_rn (Arr a b) F n) (typed_rn a x n)"
  using assms by (auto simp: typed_R_app_def Fst Snd elim: typed_root_arrowE)

theorem typed_R_extensional:
  assumes fm: "Elem F (typed_R (Arr a b))"
    and gm: "Elem G (typed_R (Arr a b))"
    and same: "\<And>x. Elem x (typed_R a) \<Longrightarrow> typed_R_app F x = typed_R_app G x"
  shows "F = G"
proof -
  obtain F0 FS FQ where F: "F = Opair F0 (Opair FS FQ)"
    and F0: "Elem F0 (Fun (typed_R a) (typed_R b))"
    and FS: "Elem FS (typed_S (Arr a b))"
    and FQ: "Elem FQ (Fun HOLZF.Nat (typed_M (Arr a b)))"
    using fm by (auto elim: typed_root_arrowE)
  obtain G0 GS GQ where G: "G = Opair G0 (Opair GS GQ)"
    and G0: "Elem G0 (Fun (typed_R a) (typed_R b))"
    and GS: "Elem GS (typed_S (Arr a b))"
    and GQ: "Elem GQ (Fun HOLZF.Nat (typed_M (Arr a b)))"
    using gm by (auto elim: typed_root_arrowE)
  have zero: "F0 = G0"
    by (rule typed_graph_ext[OF F0 G0])
      (use same in \<open>simp add: F G typed_R_app_def Fst\<close>)
  have middle: "FS = GS"
  proof (rule typed_S_extensional[OF FS GS])
    fix y assume ym: "Elem y (typed_S a)"
    obtain x where xm: "Elem x (typed_R a)" and xy: "typed_rs a x = y"
      using typed_rs_surjective[OF ym] by blast
    show "typed_S_app FS y = typed_S_app GS y"
      using typed_R_application_s[OF fm xm] typed_R_application_s[OF gm xm]
        same[OF xm] by (simp add: F G Fst Snd xy)
  qed
  have point: "typed_at FQ n = typed_at GQ n" for n
  proof (rule typed_graph_ext)
    show "Elem (typed_at FQ n) (Fun (typed_M a) (typed_M b))"
      using typed_at_type[OF FQ, of n] by simp
    show "Elem (typed_at GQ n) (Fun (typed_M a) (typed_M b))"
      using typed_at_type[OF GQ, of n] by simp
    fix y assume ym: "Elem y (typed_M a)"
    obtain x where xm: "Elem x (typed_R a)" and xy: "typed_rn a x n = y"
      using typed_rn_surjective[OF ym, of n] by blast
    show "app (typed_at FQ n) y = app (typed_at GQ n) y"
      using typed_R_application_n[OF fm xm, of n]
        typed_R_application_n[OF gm xm, of n] same[OF xm]
      by (simp add: F G Fst Snd xy)
  qed
  have terminal: "FQ = GQ"
  proof (rule typed_graph_ext[OF FQ GQ])
    fix N assume N: "Elem N HOLZF.Nat"
    show "app FQ N = app GQ N"
      using point[of "Nat2nat N"] by (simp add: typed_at_def N)
  qed
  show ?thesis by (simp add: F G zero middle terminal)
qed

text \<open>This leaf gives actual all-type carriers, natural application
  and onto action maps. Typed_Source_Model and Typed_Paper_Model separately
  prove the future-set/future-graph model identifications; carrier construction
  alone must not be counted as those modelhood or validity results.\<close>

end
