theory Typed_Quantifier
  imports Typed_Proposition_Bridge
begin

section \<open>Own-domain universal quantification in the actual typed carriers\<close>

definition bit_dec :: "ZF \<Rightarrow> bool" where
  "bit_dec z \<longleftrightarrow> z = Singleton Empty"

lemma bit_dec_zbit [simp]: "bit_dec (zbit b) = b"
  by (simp add: bit_dec_def)

definition typed_mallval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_mallval a P = zbit (\<forall>x. Elem x (typed_M a) \<longrightarrow> bit_dec (app P x))"

definition typed_mall :: "otype \<Rightarrow> ZF" where
  "typed_mall a = Lambda (typed_M (Arr a Prop)) (typed_mallval a)"

lemma typed_mallval_type [simp]: "Elem (typed_mallval a P) typed_two"
  by (simp add: typed_mallval_def)

theorem typed_mall_type:
  "Elem (typed_mall a) (typed_M (Arr (Arr a Prop) Prop))"
  by (simp add: typed_mall_def Elem_Lambda_Fun)

lemma typed_mall_app:
  assumes "Elem P (typed_M (Arr a Prop))"
  shows "app (typed_mall a) P = typed_mallval a P"
  using assms by (simp add: typed_mall_def Lambda_app)

theorem typed_mall_truth:
  assumes "Elem P (typed_M (Arr a Prop))"
  shows "bit_dec (app (typed_mall a) P) =
    (\<forall>x. Elem x (typed_M a) \<longrightarrow> bit_dec (app P x))"
  by (simp add: typed_mall_app[OF assms] typed_mallval_def)

text \<open>The terminal universal operation is a map on a finite carrier
  of predicate objects. Consequently it commutes with the same finite
  ultralimit used by the root hierarchy. The operation itself quantifies
  over the entire terminal argument carrier, not a selected subset.\<close>

lemma typed_mall_ulim:
  assumes pm: "\<And>n. Elem (P n) (typed_M (Arr a Prop))"
  shows "ulim (\<lambda>n. app (typed_mall a) (P n)) = app (typed_mall a) (ulim P)"
proof (rule ulim_map[where A="explode (typed_M (Arr a Prop))"
      and f=P and h="app (typed_mall a)"])
  show "finite (explode (typed_M (Arr a Prop)))" by (rule typed_M_finite)
  fix n show "P n \<in> explode (typed_M (Arr a Prop))"
    using pm[of n] by (simp add: explode_Elem)
qed

definition typed_sallval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_sallval a P = Opair
    (zbit (\<forall>x. Elem x (typed_S a) \<longrightarrow> bit_dec (Fst (typed_S_app P x))))
    (app (typed_mall a) (typed_j (Arr a Prop) P))"

definition typed_sall :: "otype \<Rightarrow> ZF" where
  "typed_sall a = Opair
    (Lambda (typed_S (Arr a Prop)) (typed_sallval a)) (typed_mall a)"

lemma typed_sallval_type:
  assumes pm: "Elem P (typed_S (Arr a Prop))"
  shows "Elem (typed_sallval a P) (typed_S Prop)"
proof -
  have jm: "Elem (typed_j (Arr a Prop) P) (typed_M (Arr a Prop))"
    by (rule typed_j_type[OF pm])
  have out: "Elem (app (typed_mall a) (typed_j (Arr a Prop) P)) (typed_M Prop)"
    by (rule typed_M_application[OF typed_mall_type jm])
  show ?thesis using out by (simp add: typed_sallval_def CartProd Opair)
qed

theorem typed_sall_type:
  "Elem (typed_sall a) (typed_S (Arr (Arr a Prop) Prop))"
proof -
  have graph: "Elem (Lambda (typed_S (Arr a Prop)) (typed_sallval a))
    (Fun (typed_S (Arr a Prop)) (typed_S Prop))"
    using typed_sallval_type[where a=a] by (simp add: Elem_Lambda_Fun)
  show ?thesis
    using graph typed_mall_type[where a=a]
    by (simp add: typed_sall_def typed_compatible_pair typed_sallval_def
        Lambda_app Snd)
qed

lemma typed_sall_app:
  assumes "Elem P (typed_S (Arr a Prop))"
  shows "typed_S_app (typed_sall a) P = typed_sallval a P"
  using assms by (simp add: typed_S_app_def typed_sall_def Fst Lambda_app)

lemma typed_sall_future [simp]:
  "typed_j (Arr (Arr a Prop) Prop) (typed_sall a) = typed_mall a"
  by (simp add: typed_sall_def Snd)

lemma typed_sall_snd [simp]: "Snd (typed_sall a) = typed_mall a"
  by (simp add: typed_sall_def Snd)

theorem typed_sall_truth:
  assumes "Elem P (typed_S (Arr a Prop))"
  shows "bit_dec (Fst (typed_S_app (typed_sall a) P)) =
    (\<forall>x. Elem x (typed_S a) \<longrightarrow> bit_dec (Fst (typed_S_app P x)))"
  by (simp add: typed_sall_app[OF assms] typed_sallval_def Fst)

theorem typed_sall_limit_truth:
  assumes pm: "Elem P (typed_S (Arr a Prop))"
  shows "bit_dec (Snd (typed_S_app (typed_sall a) P)) =
    (\<forall>x. Elem x (typed_M a) \<longrightarrow>
      bit_dec (app (typed_j (Arr a Prop) P) x))"
  using typed_mall_truth[OF typed_j_type[OF pm]]
  by (simp add: typed_sall_app[OF pm] typed_sallval_def Snd)

definition typed_rallval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_rallval a P = Opair
    (zbit (\<forall>x. Elem x (typed_R a) \<longrightarrow> bit_dec (Fst (typed_R_app P x))))
    (Opair (Fst (typed_sallval a (typed_rs (Arr a Prop) P)))
      (typed_seq (\<lambda>n. app (typed_mall a) (typed_rn (Arr a Prop) P n))))"

definition typed_rall :: "otype \<Rightarrow> ZF" where
  "typed_rall a = Opair
    (Lambda (typed_R (Arr a Prop)) (typed_rallval a))
    (Opair (typed_sall a) (typed_seq (\<lambda>n. typed_mall a)))"

lemma typed_rallval_type:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "Elem (typed_rallval a P) (typed_R Prop)"
proof -
  have leaf: "Elem (app (typed_mall a) (typed_rn (Arr a Prop) P n)) typed_two" for n
    using typed_M_application[OF typed_mall_type typed_rn_type[OF pm, of n]] by simp
  show ?thesis
    unfolding typed_rallval_def typed_sallval_def
    by (simp only: Fst) (rule typed_R_propI, rule zbit_type, rule zbit_type, rule leaf)
qed

lemma typed_rallval_middle:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "typed_rs Prop (typed_rallval a P) =
    typed_S_app (typed_sall a) (typed_rs (Arr a Prop) P)"
proof -
  have sm: "Elem (typed_rs (Arr a Prop) P) (typed_S (Arr a Prop))"
    by (rule typed_rs_type[OF pm])
  have leaf: "Elem (typed_rn (Arr a Prop) P n) (typed_M (Arr a Prop))" for n
    by (rule typed_rn_type[OF pm])
  have lim: "ulim (\<lambda>n. app (typed_mall a) (typed_rn (Arr a Prop) P n)) =
    app (typed_mall a) (typed_j (Arr a Prop) (typed_rs (Arr a Prop) P))"
    using typed_mall_ulim[where a=a and P="typed_rn (Arr a Prop) P", OF leaf]
      typed_R_compatible[OF pm] by simp
  have app_raw: "typed_S_app (typed_sall a) (Fst (Snd P)) =
    typed_sallval a (Fst (Snd P))"
    using typed_sall_app[where a=a and P="typed_rs (Arr a Prop) P", OF sm]
    by (simp only: typed_rs.simps)
  have lim_raw: "ulim (\<lambda>n. app (typed_mall a) (typed_at (Snd (Snd P)) n)) =
    app (typed_mall a) (Snd (Fst (Snd P)))"
    using lim by (simp only: typed_rn.simps typed_rs.simps typed_j.simps)
  show ?thesis
    by (simp add: typed_rallval_def app_raw typed_sallval_def Fst Snd lim_raw)
qed

lemma typed_rallval_leaf:
  "typed_rn Prop (typed_rallval a P) n =
    app (typed_mall a) (typed_rn (Arr a Prop) P n)"
  by (simp add: typed_rallval_def Snd)

theorem typed_rall_type:
  "Elem (typed_rall a) (typed_R (Arr (Arr a Prop) Prop))"
proof -
  have graph: "Elem (Lambda (typed_R (Arr a Prop)) (typed_rallval a))
    (Fun (typed_R (Arr a Prop)) (typed_R Prop))"
    using typed_rallval_type[where a=a] by (simp add: Elem_Lambda_Fun)
  have seq: "Elem (typed_seq (\<lambda>n. typed_mall a))
    (Fun HOLZF.Nat (typed_M (Arr (Arr a Prop) Prop)))"
    by (rule typed_seq_type) (rule typed_mall_type)
  have mem: "Elem
    (Opair (Lambda (typed_R (Arr a Prop)) (typed_rallval a))
      (Opair (typed_sall a) (typed_seq (\<lambda>n. typed_mall a))))
    (typed_root_arrow (Arr a Prop) Prop (typed_R (Arr a Prop)) (typed_R Prop)
      (typed_rs (Arr a Prop)) (typed_rs Prop)
      (typed_rn (Arr a Prop)) (typed_rn Prop))"
    using graph seq typed_sall_type[where a=a]
      typed_rallval_middle[where a=a] typed_rallval_leaf[where a=a]
    by (simp add: typed_root_arrow_triple Lambda_app)
  show ?thesis using mem by (simp only: typed_rall_def typed_R.simps)
qed

lemma typed_rall_app:
  assumes "Elem P (typed_R (Arr a Prop))"
  shows "typed_R_app (typed_rall a) P = typed_rallval a P"
  using assms by (simp add: typed_R_app_def typed_rall_def Fst Lambda_app)

lemma typed_rall_middle [simp]:
  "typed_rs (Arr (Arr a Prop) Prop) (typed_rall a) = typed_sall a"
  by (simp add: typed_rall_def Fst Snd)

lemma typed_rall_leaf [simp]:
  "typed_rn (Arr (Arr a Prop) Prop) (typed_rall a) n = typed_mall a"
  by (simp add: typed_rall_def Snd)

theorem typed_rall_truth:
  assumes "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (Fst (typed_R_app (typed_rall a) P)) =
    (\<forall>x. Elem x (typed_R a) \<longrightarrow> bit_dec (Fst (typed_R_app P x)))"
  by (simp add: typed_rall_app[OF assms] typed_rallval_def Fst)

theorem typed_rall_middle_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (Fst (typed_rs Prop (typed_R_app (typed_rall a) P))) =
    (\<forall>x. Elem x (typed_S a) \<longrightarrow>
      bit_dec (Fst (typed_S_app (typed_rs (Arr a Prop) P) x)))"
  by (simp only: typed_rall_app[OF pm] typed_rallval_middle[OF pm];
    rule typed_sall_truth[OF typed_rs_type[OF pm]])

theorem typed_rall_leaf_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (typed_rn Prop (typed_R_app (typed_rall a) P) n) =
    (\<forall>x. Elem x (typed_M a) \<longrightarrow>
      bit_dec (app (typed_rn (Arr a Prop) P n) x))"
  by (simp only: typed_rall_app[OF pm] typed_rallval_leaf;
    rule typed_mall_truth[OF typed_rn_type[OF pm, of n]])

theorem typed_rall_limit_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (typed_j Prop (typed_rs Prop (typed_R_app (typed_rall a) P))) =
    (\<forall>x. Elem x (typed_M a) \<longrightarrow>
      bit_dec (app (typed_j (Arr a Prop) (typed_rs (Arr a Prop) P)) x))"
  using typed_sall_limit_truth[OF typed_rs_type[OF pm]]
  by (simp only: typed_rall_app[OF pm] typed_rallval_middle[OF pm] typed_j.simps)

text \<open>These are actual members of all three recursively constructed
  carriers, with full own-domain universal truth at every coordinate.
  No modelhood premise was assumed. Identification with the independent
  source-language quantifier interpretation remains a separate bridge.\<close>

ML \<open>
  val facts = [@{thm typed_mall_type}, @{thm typed_sall_type}, @{thm typed_rall_type},
    @{thm typed_mall_ulim}, @{thm typed_mall_truth}, @{thm typed_sall_truth},
    @{thm typed_sall_limit_truth}, @{thm typed_rall_truth},
    @{thm typed_rall_middle_truth}, @{thm typed_rall_leaf_truth},
    @{thm typed_rall_limit_truth}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "TYPED-QUANTIFIER: 11 clean endpoints; genuine carrier membership and own-domain truth";
\<close>

end
