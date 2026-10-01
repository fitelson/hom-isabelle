theory Finite_Ultralimit
  imports Classicism_Normalization_Core
begin

section \<open>Ultralimits with finite carrier sets\<close>

text \<open>No finite type-class constraint is used. The ambient HOL types may
  be infinite; finiteness is a hypothesis on the particular carrier set.
  Outside the eventually constant sequences the choice operation below is
  unspecified. All its uses are guarded by explicit eventuality or finite
  carrier hypotheses. These are building blocks, not an all-type model.\<close>

definition ulim :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "ulim f = (SOME a. eventually (\<lambda>n. f n = a) norm_U)"

lemma norm_eventually_bex_finite:
  assumes "finite A"
  shows "eventually (\<lambda>n. \<exists>a\<in>A. P n a) norm_U \<longleftrightarrow>
    (\<exists>a\<in>A. eventually (\<lambda>n. P n a) norm_U)"
  using assms
  by (induction A rule: finite_induct)
     (simp_all add: norm_U.proper norm_U.eventually_disj_iff)

lemma finite_carrier_eventually_constant:
  assumes fin: "finite A" and val: "\<And>n. f n \<in> A"
  shows "\<exists>a\<in>A. eventually (\<lambda>n. f n = a) norm_U"
proof -
  have ev: "eventually (\<lambda>n. \<exists>a\<in>A. f n = a) norm_U"
  proof (rule eventuallyI)
    fix n
    show "\<exists>a\<in>A. f n = a"
      by (rule bexI[where x="f n"]) (simp_all add: val)
  qed
  show ?thesis
    using ev
    by (simp only: norm_eventually_bex_finite[where A=A and
          P="\<lambda>n a. f n = a", OF fin])
qed

lemma eventually_constant_unique:
  assumes a: "eventually (\<lambda>n. f n = a) norm_U"
      and b: "eventually (\<lambda>n. f n = b) norm_U"
  shows "a = b"
proof -
  have "eventually (\<lambda>n. a = b) norm_U"
    using a b by eventually_elim simp
  then show ?thesis by (simp add: norm_U.proper)
qed

lemma ulim_eqI:
  assumes ev: "eventually (\<lambda>n. f n = a) norm_U"
  shows "ulim f = a"
proof -
  have "eventually (\<lambda>n. f n = ulim f) norm_U"
    unfolding ulim_def by (rule someI[where x=a]) (rule ev)
  from eventually_constant_unique[OF this ev] show ?thesis .
qed

lemma ulim_const [simp]: "ulim (\<lambda>n. a) = a"
  by (rule ulim_eqI) simp

lemma eventually_eq_ulim:
  assumes "finite A" "\<And>n. f n \<in> A"
  shows "eventually (\<lambda>n. f n = ulim f) norm_U"
proof -
  have ex: "\<exists>a\<in>A. eventually (\<lambda>n. f n = a) norm_U"
    by (rule finite_carrier_eventually_constant[where A=A and f=f, OF assms])
  obtain a where "a \<in> A" and ev: "eventually (\<lambda>n. f n = a) norm_U"
    using ex by blast
  from ulim_eqI[OF ev] ev show ?thesis by simp
qed

lemma ulim_in_carrier:
  assumes "finite A" "\<And>n. f n \<in> A"
  shows "ulim f \<in> A"
proof -
  have ex: "\<exists>a\<in>A. eventually (\<lambda>n. f n = a) norm_U"
    by (rule finite_carrier_eventually_constant[where A=A and f=f, OF assms])
  obtain a where a: "a \<in> A" and ev: "eventually (\<lambda>n. f n = a) norm_U"
    using ex by blast
  show ?thesis using a ulim_eqI[OF ev] by simp
qed

lemma ulim_eventual_cong:
  assumes fin: "finite A" and val: "\<And>n. f n \<in> A"
      and eq: "eventually (\<lambda>n. f n = g n) norm_U"
  shows "ulim f = ulim g"
proof -
  have "eventually (\<lambda>n. g n = ulim f) norm_U"
    using eventually_eq_ulim[where A=A and f=f, OF fin val] eq by eventually_elim simp
  from ulim_eqI[OF this] show ?thesis by simp
qed

section \<open>Operations and application\<close>

lemma ulim_map:
  assumes fin: "finite A" and val: "\<And>n. f n \<in> A"
  shows "ulim (\<lambda>n. h (f n)) = h (ulim f)"
proof (rule ulim_eqI)
  show "eventually (\<lambda>n. h (f n) = h (ulim f)) norm_U"
    using eventually_eq_ulim[where A=A and f=f, OF fin val] by eventually_elim simp
qed

lemma ulim_binary:
  assumes fa: "finite A" and va: "\<And>n. f n \<in> A"
      and fb: "finite B" and vb: "\<And>n. g n \<in> B"
  shows "ulim (\<lambda>n. h (f n) (g n)) = h (ulim f) (ulim g)"
proof (rule ulim_eqI)
  show "eventually (\<lambda>n. h (f n) (g n) = h (ulim f) (ulim g)) norm_U"
    using eventually_eq_ulim[where A=A and f=f, OF fa va]
      eventually_eq_ulim[where A=B and f=g, OF fb vb]
    by eventually_elim simp
qed

lemma ulim_application:
  assumes ff: "finite F" and vf: "\<And>n. f n \<in> F"
      and fa: "finite A" and va: "\<And>n. x n \<in> A"
  shows "ulim (\<lambda>n. f n (x n)) = (ulim f) (ulim x)"
  by (rule ulim_binary[where A=F and B=A and f=f and g=x and
        h="\<lambda>h a. h a", OF ff vf fa va])

lemma ulim_function_pointwise:
  assumes "finite F" "\<And>n. f n \<in> F"
  shows "(ulim f) x = ulim (\<lambda>n. f n x)"
  using ulim_map[where A=F and f=f and h="\<lambda>h. h x", OF assms] by simp

lemma ulim_function_extensional:
  assumes "finite F" "\<And>n. f n \<in> F"
  shows "ulim f = (\<lambda>x. ulim (\<lambda>n. f n x))"
  by (rule ext) (rule ulim_function_pointwise[where F=F and f=f, OF assms])

text \<open>The next results require only a finite argument carrier and a
  finite value carrier. They do not assume that the total ambient functions
  belong to a finite set: their values outside the argument carrier may vary
  freely. The limit is therefore expressed pointwise on that carrier.\<close>

lemma eventually_uniform_finite_carrier:
  assumes fa: "finite A" and fb: "finite B"
      and val: "\<And>n x. x \<in> A \<Longrightarrow> f n x \<in> B"
  shows "eventually (\<lambda>n. \<forall>x\<in>A. f n x = ulim (\<lambda>m. f m x)) norm_U"
proof (rule eventually_ball_finite[OF fa])
  show "\<forall>x\<in>A. eventually (\<lambda>n. f n x = ulim (\<lambda>m. f m x)) norm_U"
  proof (intro ballI)
    fix x assume x: "x \<in> A"
    show "eventually (\<lambda>n. f n x = ulim (\<lambda>m. f m x)) norm_U"
      by (rule eventually_eq_ulim[where A=B and f="\<lambda>n. f n x", OF fb])
         (rule val[OF x])
  qed
qed

lemma ulim_application_on_carriers:
  assumes fa: "finite A" and fb: "finite B"
      and val: "\<And>n x. x \<in> A \<Longrightarrow> f n x \<in> B"
      and arg: "\<And>n. x n \<in> A"
  shows "ulim (\<lambda>n. f n (x n)) = ulim (\<lambda>n. f n (ulim x))"
proof (rule ulim_eqI)
  have inside: "ulim x \<in> A"
    by (rule ulim_in_carrier[where A=A and f=x, OF fa arg])
  have ev: "eventually (\<lambda>n. f n (ulim x) = ulim (\<lambda>m. f m (ulim x))) norm_U"
    by (rule eventually_eq_ulim[where A=B and f="\<lambda>n. f n (ulim x)", OF fb])
       (rule val[OF inside])
  show "eventually (\<lambda>n. f n (x n) = ulim (\<lambda>m. f m (ulim x))) norm_U"
    using eventually_eq_ulim[where A=A and f=x, OF fa arg] ev by eventually_elim simp
qed

section \<open>Finite quantifier commutation\<close>

lemma ulim_bool_iff: "ulim P \<longleftrightarrow> eventually P norm_U"
proof (cases "eventually P norm_U")
  case True
  have "ulim P = True"
    by (rule ulim_eqI) (use True in simp)
  with True show ?thesis by simp
next
  case False
  have "eventually (\<lambda>n. \<not> P n) norm_U"
    using False by (simp add: norm_U.eventually_not_iff)
  then have "ulim P = False" by (intro ulim_eqI) simp
  with False show ?thesis by simp
qed

lemma ulim_ubit: "ulim (\<lambda>n. n \<in> A) = ubit A"
  by (simp add: ulim_bool_iff ubit_def)

lemma ulim_ball_finite:
  assumes "finite A"
  shows "ulim (\<lambda>n. \<forall>x\<in>A. P n x) = (\<forall>x\<in>A. ulim (\<lambda>n. P n x))"
  by (simp add: ulim_bool_iff eventually_ball_finite_distrib[OF assms])

lemma ulim_bex_finite:
  assumes "finite A"
  shows "ulim (\<lambda>n. \<exists>x\<in>A. P n x) = (\<exists>x\<in>A. ulim (\<lambda>n. P n x))"
  by (simp add: ulim_bool_iff norm_eventually_bex_finite[OF assms])

lemma ulim_finite_carrier_all:
  assumes fa: "finite A" and fb: "finite B"
      and val: "\<And>n x. x \<in> A \<Longrightarrow> f n x \<in> B"
  shows "ulim (\<lambda>n. \<forall>x\<in>A. R x (f n x)) =
    (\<forall>x\<in>A. R x (ulim (\<lambda>n. f n x)))"
proof -
  have point: "ulim (\<lambda>n. R x (f n x)) = R x (ulim (\<lambda>n. f n x))"
    if "x \<in> A" for x
    by (rule ulim_map[where A=B and f="\<lambda>n. f n x" and h="R x", OF fb])
       (rule val[OF that])
  show ?thesis using ulim_ball_finite[where A=A and P="\<lambda>n x. R x (f n x)", OF fa]
    point by simp
qed

lemma ulim_finite_carrier_ex:
  assumes fa: "finite A" and fb: "finite B"
      and val: "\<And>n x. x \<in> A \<Longrightarrow> f n x \<in> B"
  shows "ulim (\<lambda>n. \<exists>x\<in>A. R x (f n x)) =
    (\<exists>x\<in>A. R x (ulim (\<lambda>n. f n x)))"
proof -
  have point: "ulim (\<lambda>n. R x (f n x)) = R x (ulim (\<lambda>n. f n x))"
    if "x \<in> A" for x
    by (rule ulim_map[where A=B and f="\<lambda>n. f n x" and h="R x", OF fb])
       (rule val[OF that])
  show ?thesis using ulim_bex_finite[where A=A and P="\<lambda>n x. R x (f n x)", OF fa]
    point by simp
qed

section \<open>Audit endpoints\<close>

ML \<open>
  val facts = [@{thm finite_carrier_eventually_constant},
    @{thm eventually_constant_unique}, @{thm ulim_eqI}, @{thm ulim_const},
    @{thm eventually_eq_ulim}, @{thm ulim_in_carrier},
    @{thm ulim_eventual_cong}, @{thm ulim_map}, @{thm ulim_binary},
    @{thm ulim_application}, @{thm ulim_function_pointwise},
    @{thm ulim_function_extensional}, @{thm eventually_uniform_finite_carrier},
    @{thm ulim_application_on_carriers}, @{thm ulim_bool_iff},
    @{thm ulim_ubit}, @{thm ulim_ball_finite}, @{thm ulim_bex_finite},
    @{thm ulim_finite_carrier_all}, @{thm ulim_finite_carrier_ex}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "FINITE-ULTRALIMIT: 20 clean endpoints; finite-carrier building blocks only";
\<close>

end
