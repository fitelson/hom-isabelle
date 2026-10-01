theory Typed_Paper_Primitives_Existential
  imports Typed_Quantifier
begin

section \<open>Own-domain existential quantification in the actual typed carriers\<close>

definition typed_mexval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_mexval a P = zbit (\<exists>x. Elem x (typed_M a) \<and> bit_dec (app P x))"

definition typed_mex :: "otype \<Rightarrow> ZF" where
  "typed_mex a = Lambda (typed_M (Arr a Prop)) (typed_mexval a)"

lemma typed_mexval_type [simp]: "Elem (typed_mexval a P) typed_two"
  by (simp add: typed_mexval_def)

theorem typed_mex_type:
  "Elem (typed_mex a) (typed_M (Arr (Arr a Prop) Prop))"
  by (simp add: typed_mex_def Elem_Lambda_Fun)

lemma typed_mex_app:
  assumes "Elem P (typed_M (Arr a Prop))"
  shows "app (typed_mex a) P = typed_mexval a P"
  using assms by (simp add: typed_mex_def Lambda_app)

theorem typed_mex_truth:
  assumes "Elem P (typed_M (Arr a Prop))"
  shows "bit_dec (app (typed_mex a) P) =
    (\<exists>x. Elem x (typed_M a) \<and> bit_dec (app P x))"
  by (simp add: typed_mex_app[OF assms] typed_mexval_def)

text \<open>The terminal existential operation is a map on a finite carrier
  of predicate objects. Consequently it commutes with the same finite
  ultralimit used by the root hierarchy. The operation itself quantifies
  over the entire terminal argument carrier, not a selected subset.\<close>

lemma typed_mex_ulim:
  assumes pm: "\<And>n. Elem (P n) (typed_M (Arr a Prop))"
  shows "ulim (\<lambda>n. app (typed_mex a) (P n)) = app (typed_mex a) (ulim P)"
proof (rule ulim_map[where A="explode (typed_M (Arr a Prop))"
      and f=P and h="app (typed_mex a)"])
  show "finite (explode (typed_M (Arr a Prop)))" by (rule typed_M_finite)
  fix n show "P n \<in> explode (typed_M (Arr a Prop))"
    using pm[of n] by (simp add: explode_Elem)
qed

definition typed_sexval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_sexval a P = Opair
    (zbit (\<exists>x. Elem x (typed_S a) \<and> bit_dec (Fst (typed_S_app P x))))
    (app (typed_mex a) (typed_j (Arr a Prop) P))"

definition typed_sex :: "otype \<Rightarrow> ZF" where
  "typed_sex a = Opair
    (Lambda (typed_S (Arr a Prop)) (typed_sexval a)) (typed_mex a)"

lemma typed_sexval_type:
  assumes pm: "Elem P (typed_S (Arr a Prop))"
  shows "Elem (typed_sexval a P) (typed_S Prop)"
proof -
  have jm: "Elem (typed_j (Arr a Prop) P) (typed_M (Arr a Prop))"
    by (rule typed_j_type[OF pm])
  have out: "Elem (app (typed_mex a) (typed_j (Arr a Prop) P)) (typed_M Prop)"
    by (rule typed_M_application[OF typed_mex_type jm])
  show ?thesis using out by (simp add: typed_sexval_def CartProd Opair)
qed

theorem typed_sex_type:
  "Elem (typed_sex a) (typed_S (Arr (Arr a Prop) Prop))"
proof -
  have graph: "Elem (Lambda (typed_S (Arr a Prop)) (typed_sexval a))
    (Fun (typed_S (Arr a Prop)) (typed_S Prop))"
    using typed_sexval_type[where a=a] by (simp add: Elem_Lambda_Fun)
  show ?thesis
    using graph typed_mex_type[where a=a]
    by (simp add: typed_sex_def typed_compatible_pair typed_sexval_def
        Lambda_app Snd)
qed

lemma typed_sex_app:
  assumes "Elem P (typed_S (Arr a Prop))"
  shows "typed_S_app (typed_sex a) P = typed_sexval a P"
  using assms by (simp add: typed_S_app_def typed_sex_def Fst Lambda_app)

lemma typed_sex_future [simp]:
  "typed_j (Arr (Arr a Prop) Prop) (typed_sex a) = typed_mex a"
  by (simp add: typed_sex_def Snd)

lemma typed_sex_snd [simp]: "Snd (typed_sex a) = typed_mex a"
  by (simp add: typed_sex_def Snd)

theorem typed_sex_truth:
  assumes "Elem P (typed_S (Arr a Prop))"
  shows "bit_dec (Fst (typed_S_app (typed_sex a) P)) =
    (\<exists>x. Elem x (typed_S a) \<and> bit_dec (Fst (typed_S_app P x)))"
  by (simp add: typed_sex_app[OF assms] typed_sexval_def Fst)

theorem typed_sex_limit_truth:
  assumes pm: "Elem P (typed_S (Arr a Prop))"
  shows "bit_dec (Snd (typed_S_app (typed_sex a) P)) =
    (\<exists>x. Elem x (typed_M a) \<and>
      bit_dec (app (typed_j (Arr a Prop) P) x))"
  using typed_mex_truth[OF typed_j_type[OF pm]]
  by (simp add: typed_sex_app[OF pm] typed_sexval_def Snd)

definition typed_rexval :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "typed_rexval a P = Opair
    (zbit (\<exists>x. Elem x (typed_R a) \<and> bit_dec (Fst (typed_R_app P x))))
    (Opair (Fst (typed_sexval a (typed_rs (Arr a Prop) P)))
      (typed_seq (\<lambda>n. app (typed_mex a) (typed_rn (Arr a Prop) P n))))"

definition typed_rex :: "otype \<Rightarrow> ZF" where
  "typed_rex a = Opair
    (Lambda (typed_R (Arr a Prop)) (typed_rexval a))
    (Opair (typed_sex a) (typed_seq (\<lambda>n. typed_mex a)))"

lemma typed_rexval_type:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "Elem (typed_rexval a P) (typed_R Prop)"
proof -
  have leaf: "Elem (app (typed_mex a) (typed_rn (Arr a Prop) P n)) typed_two" for n
    using typed_M_application[OF typed_mex_type typed_rn_type[OF pm, of n]] by simp
  show ?thesis
    unfolding typed_rexval_def typed_sexval_def
    by (simp only: Fst) (rule typed_R_propI, rule zbit_type, rule zbit_type, rule leaf)
qed

lemma typed_rexval_middle:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "typed_rs Prop (typed_rexval a P) =
    typed_S_app (typed_sex a) (typed_rs (Arr a Prop) P)"
proof -
  have sm: "Elem (typed_rs (Arr a Prop) P) (typed_S (Arr a Prop))"
    by (rule typed_rs_type[OF pm])
  have leaf: "Elem (typed_rn (Arr a Prop) P n) (typed_M (Arr a Prop))" for n
    by (rule typed_rn_type[OF pm])
  have lim: "ulim (\<lambda>n. app (typed_mex a) (typed_rn (Arr a Prop) P n)) =
    app (typed_mex a) (typed_j (Arr a Prop) (typed_rs (Arr a Prop) P))"
    using typed_mex_ulim[where a=a and P="typed_rn (Arr a Prop) P", OF leaf]
      typed_R_compatible[OF pm] by simp
  have app_raw: "typed_S_app (typed_sex a) (Fst (Snd P)) =
    typed_sexval a (Fst (Snd P))"
    using typed_sex_app[where a=a and P="typed_rs (Arr a Prop) P", OF sm]
    by (simp only: typed_rs.simps)
  have lim_raw: "ulim (\<lambda>n. app (typed_mex a) (typed_at (Snd (Snd P)) n)) =
    app (typed_mex a) (Snd (Fst (Snd P)))"
    using lim by (simp only: typed_rn.simps typed_rs.simps typed_j.simps)
  show ?thesis
    by (simp add: typed_rexval_def app_raw typed_sexval_def Fst Snd lim_raw)
qed

lemma typed_rexval_leaf:
  "typed_rn Prop (typed_rexval a P) n =
    app (typed_mex a) (typed_rn (Arr a Prop) P n)"
  by (simp add: typed_rexval_def Snd)

theorem typed_rex_type:
  "Elem (typed_rex a) (typed_R (Arr (Arr a Prop) Prop))"
proof -
  have graph: "Elem (Lambda (typed_R (Arr a Prop)) (typed_rexval a))
    (Fun (typed_R (Arr a Prop)) (typed_R Prop))"
    using typed_rexval_type[where a=a] by (simp add: Elem_Lambda_Fun)
  have seq: "Elem (typed_seq (\<lambda>n. typed_mex a))
    (Fun HOLZF.Nat (typed_M (Arr (Arr a Prop) Prop)))"
    by (rule typed_seq_type) (rule typed_mex_type)
  have mem: "Elem
    (Opair (Lambda (typed_R (Arr a Prop)) (typed_rexval a))
      (Opair (typed_sex a) (typed_seq (\<lambda>n. typed_mex a))))
    (typed_root_arrow (Arr a Prop) Prop (typed_R (Arr a Prop)) (typed_R Prop)
      (typed_rs (Arr a Prop)) (typed_rs Prop)
      (typed_rn (Arr a Prop)) (typed_rn Prop))"
    using graph seq typed_sex_type[where a=a]
      typed_rexval_middle[where a=a] typed_rexval_leaf[where a=a]
    by (simp add: typed_root_arrow_triple Lambda_app)
  show ?thesis using mem by (simp only: typed_rex_def typed_R.simps)
qed

lemma typed_rex_app:
  assumes "Elem P (typed_R (Arr a Prop))"
  shows "typed_R_app (typed_rex a) P = typed_rexval a P"
  using assms by (simp add: typed_R_app_def typed_rex_def Fst Lambda_app)

lemma typed_rex_middle [simp]:
  "typed_rs (Arr (Arr a Prop) Prop) (typed_rex a) = typed_sex a"
  by (simp add: typed_rex_def Fst Snd)

lemma typed_rex_leaf [simp]:
  "typed_rn (Arr (Arr a Prop) Prop) (typed_rex a) n = typed_mex a"
  by (simp add: typed_rex_def Snd)

theorem typed_rex_truth:
  assumes "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (Fst (typed_R_app (typed_rex a) P)) =
    (\<exists>x. Elem x (typed_R a) \<and> bit_dec (Fst (typed_R_app P x)))"
  by (simp add: typed_rex_app[OF assms] typed_rexval_def Fst)

theorem typed_rex_middle_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (Fst (typed_rs Prop (typed_R_app (typed_rex a) P))) =
    (\<exists>x. Elem x (typed_S a) \<and>
      bit_dec (Fst (typed_S_app (typed_rs (Arr a Prop) P) x)))"
  by (simp only: typed_rex_app[OF pm] typed_rexval_middle[OF pm];
    rule typed_sex_truth[OF typed_rs_type[OF pm]])

theorem typed_rex_leaf_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (typed_rn Prop (typed_R_app (typed_rex a) P) n) =
    (\<exists>x. Elem x (typed_M a) \<and>
      bit_dec (app (typed_rn (Arr a Prop) P n) x))"
  by (simp only: typed_rex_app[OF pm] typed_rexval_leaf;
    rule typed_mex_truth[OF typed_rn_type[OF pm, of n]])

theorem typed_rex_limit_truth:
  assumes pm: "Elem P (typed_R (Arr a Prop))"
  shows "bit_dec (typed_j Prop (typed_rs Prop (typed_R_app (typed_rex a) P))) =
    (\<exists>x. Elem x (typed_M a) \<and>
      bit_dec (app (typed_j (Arr a Prop) (typed_rs (Arr a Prop) P)) x))"
  using typed_sex_limit_truth[OF typed_rs_type[OF pm]]
  by (simp only: typed_rex_app[OF pm] typed_rexval_middle[OF pm] typed_j.simps)

text \<open>These are actual members of all three recursively constructed
  carriers, with full own-domain existential truth at every coordinate.
  No modelhood premise was assumed. Identification with the independent
  source-language quantifier interpretation remains a separate bridge.\<close>

ML \<open>
  val facts = [@{thm typed_mex_type}, @{thm typed_sex_type}, @{thm typed_rex_type},
    @{thm typed_mex_ulim}, @{thm typed_mex_truth}, @{thm typed_sex_truth},
    @{thm typed_sex_limit_truth}, @{thm typed_rex_truth},
    @{thm typed_rex_middle_truth}, @{thm typed_rex_leaf_truth},
    @{thm typed_rex_limit_truth}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "TYPED-EXISTENTIAL: 11 clean endpoints; genuine carrier membership and own-domain truth";
\<close>

end
