theory Typed_Proposition_Bridge
  imports Typed_Root_Hierarchy Classicism_Rigidity_Component
begin

section \<open>Native Boolean profiles and the actual typed carriers\<close>

definition zbit :: "bool \<Rightarrow> ZF" where
  "zbit b = (if b then Singleton Empty else Empty)"

lemma zbit_type [simp]: "Elem (zbit b) typed_two"
  by (simp add: zbit_def typed_two_def Upair)

lemma zbit_inject [simp]: "zbit b = zbit c \<longleftrightarrow> b = c"
  by (cases b; cases c) (simp_all add: zbit_def typed_two_distinct Singleton_nonEmpty)

lemma zbit_decode [simp]: "(zbit b = Singleton Empty) = b"
  by (cases b) (simp_all add: zbit_def typed_two_distinct)

lemma zbit_encode:
  assumes "Elem x typed_two"
  shows "zbit (x = Singleton Empty) = x"
  using assms by (auto simp: typed_two_def Upair zbit_def)

lemma zbit_surjective:
  assumes "Elem x typed_two"
  shows "\<exists>b. zbit b = x"
  by (rule exI[of _ "x = Singleton Empty"]) (rule zbit_encode[OF assms])

definition zmiddle :: "middle_prop \<Rightarrow> ZF" where
  "zmiddle p = Opair (zbit (fst p)) (zbit (snd p))"

definition zprop :: "root_prop \<Rightarrow> ZF" where
  "zprop p = Opair (zbit (fst p))
    (Opair (zbit (fst (snd p))) (typed_seq (\<lambda>n. zbit (n \<in> snd (snd p)))))"

lemma zmiddle_type [simp]: "Elem (zmiddle p) (typed_S Prop)"
  by (simp add: zmiddle_def CartProd Opair)

lemma zprop_type [simp]: "Elem (zprop p) (typed_R Prop)"
  unfolding zprop_def by (rule typed_R_propI) simp_all

lemma zmiddle_inject [simp]: "zmiddle p = zmiddle q \<longleftrightarrow> p = q"
  by (simp add: zmiddle_def Opair prod_eq_iff)

definition unzprop :: "ZF \<Rightarrow> root_prop" where
  "unzprop x = (Fst x = Singleton Empty,
    Fst (Snd x) = Singleton Empty,
    {n. typed_at (Snd (Snd x)) n = Singleton Empty})"

lemma unzprop_zprop [simp]: "unzprop (zprop p) = p"
  by (simp add: unzprop_def zprop_def Fst Snd)

lemma zprop_inject [simp]: "zprop p = zprop q \<longleftrightarrow> p = q"
proof
  assume eq: "zprop p = zprop q"
  have "unzprop (zprop p) = unzprop (zprop q)" by (rule arg_cong[OF eq])
  then show "p = q" by simp
next
  assume "p = q"
  then show "zprop p = zprop q" by simp
qed

lemma zprop_unzprop:
  assumes xm: "Elem x (typed_R Prop)"
  shows "zprop (unzprop x) = x"
proof -
  obtain a b Q where shape: "x = Opair a (Opair b Q)"
    and am: "Elem a typed_two" and bm: "Elem b typed_two"
    and qm: "Elem Q (Fun HOLZF.Nat typed_two)"
    using typed_R_propE[OF xm] by blast
  have point: "zbit (typed_at Q n = Singleton Empty) = typed_at Q n" for n
  proof (rule zbit_encode)
    show "Elem (typed_at Q n) typed_two"
      by (rule typed_at_type[where Q=Q and A=typed_two and n=n, OF qm])
  qed
  have seq:
    "typed_seq (\<lambda>n. zbit (typed_at Q n = Singleton Empty)) = Q"
  proof (rule typed_graph_ext[where A=HOLZF.Nat and B=typed_two and C=typed_two])
    show "Elem (typed_seq (\<lambda>n. zbit (typed_at Q n = Singleton Empty)))
        (Fun HOLZF.Nat typed_two)"
      by (rule typed_seq_type) simp
    show "Elem Q (Fun HOLZF.Nat typed_two)" by (rule qm)
    fix N assume nm: "Elem N HOLZF.Nat"
    show "app (typed_seq (\<lambda>n. zbit (typed_at Q n = Singleton Empty))) N = app Q N"
      using point[of "Nat2nat N"]
      by (simp add: typed_seq_def Lambda_app typed_at_def nm)
  qed
  show ?thesis using zbit_encode[OF am] zbit_encode[OF bm]
    by (simp add: unzprop_def zprop_def shape Fst Snd seq)
qed

theorem zprop_surjective:
  assumes "Elem x (typed_R Prop)"
  shows "\<exists>p. zprop p = x"
  by (rule exI[of _ "unzprop x"]) (rule zprop_unzprop[OF assms])

theorem zprop_carrier:
  "range zprop = explode (typed_R Prop)"
proof (rule set_eqI)
  fix x
  show "x \<in> range zprop \<longleftrightarrow> x \<in> explode (typed_R Prop)"
  proof
    assume "x \<in> range zprop"
    then obtain p where "x = zprop p" by blast
    then show "x \<in> explode (typed_R Prop)"
      using zprop_type[of p] by (simp only: explode_Elem)
  next
    assume "x \<in> explode (typed_R Prop)"
    then have "Elem x (typed_R Prop)" by (simp only: explode_Elem)
    from zprop_surjective[OF this] show "x \<in> range zprop" by blast
  qed
qed

theorem zmiddle_surjective:
  assumes "Elem x (typed_S Prop)"
  shows "\<exists>p. zmiddle p = x"
proof -
  obtain a b where x: "x = Opair a b"
    and am: "Elem a typed_two" and bm: "Elem b typed_two"
    using assms by (auto simp: CartProd)
  show ?thesis
    by (rule exI[of _ "(a = Singleton Empty, b = Singleton Empty)"])
      (simp add: zmiddle_def x zbit_encode[OF am] zbit_encode[OF bm])
qed

section \<open>Commutation with the same ultrafilter and action maps\<close>

lemma ulim_zbit: "ulim (\<lambda>n. zbit (f n)) = zbit (ulim f)"
  by (rule ulim_map[where A="UNIV::bool set" and f=f and h=zbit]) simp_all

lemma ulim_zbit_ubit:
  "ulim (\<lambda>n. zbit (n \<in> S)) = zbit (ubit S)"
  by (simp add: ulim_zbit ulim_ubit)

lemma typed_j_zmiddle [simp]:
  "typed_j Prop (zmiddle p) = zbit (snd p)"
  by (simp add: zmiddle_def Snd)

theorem typed_rs_zprop [simp]:
  "typed_rs Prop (zprop p) = zmiddle (to_middle p)"
  by (simp add: zprop_def zmiddle_def to_middle_def Fst Snd ulim_zbit_ubit)

theorem typed_rn_zprop [simp]:
  "typed_rn Prop (zprop p) n = zbit (n \<in> snd (snd p))"
  by (simp add: zprop_def Fst Snd)

theorem typed_limit_zprop:
  "ulim (typed_rn Prop (zprop p)) = zbit (ubit (snd (snd p)))"
  by (simp add: zprop_def Snd ulim_zbit_ubit)

section \<open>Transported normalization and rigidity-fiber facts\<close>

theorem typed_normalization_action_failure:
  "typed_rs Prop (zprop (Inf_class.Inf norm_fiber)) \<noteq>
    typed_rs Prop (zprop norm_q)"
  using normalization_does_not_preserve_fiber
  by (simp only: typed_rs_zprop zmiddle_inject; simp)

theorem typed_zero_fiber_bridge:
  "p \<in> zero_fiber \<longleftrightarrow>
    typed_rs Prop (zprop p) = zmiddle (\<bottom>::middle_prop)"
  by (simp only: zero_fiber_def mem_Collect_eq typed_rs_zprop zmiddle_inject)

text \<open>The native root and intermediate proposition carriers are now
  identified bijectively with the proposition carriers of the actual ZF
  hierarchy, and the action squares commute. The last two results transfer
  the checked normalization calculation and the defining zero fiber.
  No assertion is made here that the native complete lattice order is the
  independently defined source-language Boolean order, or that the property
  rigidity predicates already interpret the source formulas. Those are
  additional semantic bridge obligations, not consequences of a carrier
  bijection alone.\<close>

ML \<open>
  val facts = [@{thm zprop_surjective}, @{thm zprop_inject},
    @{thm zmiddle_surjective}, @{thm zmiddle_inject},
    @{thm ulim_zbit_ubit}, @{thm typed_rs_zprop}, @{thm typed_rn_zprop},
    @{thm typed_normalization_action_failure}, @{thm typed_zero_fiber_bridge}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "TYPED-PROPOSITION-BRIDGE: native profiles and typed carriers; semantic interface still separate";
\<close>

end
