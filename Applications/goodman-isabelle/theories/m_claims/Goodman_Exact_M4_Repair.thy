theory Goodman_Exact_M4_Repair
  imports Goodman_Exact_M6_Repair Goodman_Exact_Generic_Fun_Prime
begin

section \<open>A nonconstant proper view of every exact fun′ proposition\<close>

lemma gi_exact_M4_variation_square_nonzero:
  "pp_e_child_variation \<circ> pp_e_child_variation \<noteq> (\<lambda>P. {})"
proof
  assume equal: "pp_e_child_variation \<circ> pp_e_child_variation = (\<lambda>P. {})"
  let ?p = "pp_e_child_variation_preimage (pp_e_child_variation_preimage UNIV)"
  have at_preimage: "(pp_e_child_variation \<circ> pp_e_child_variation) ?p = {}"
    using fun_cong[OF equal, of "?p"] by simp
  have "(UNIV :: pp_sem_prop) = {}"
    using at_preimage by (simp only: comp_apply pp_e_child_variation_preimage_right_inverse)
  then show False by simp
qed

lemma gi_exact_M4_variation_square_in_stock:
  "pp_e_child_variation \<circ> pp_e_child_variation \<in> pp_e_exact_operator_stock"
  by (rule pp_e_exact_operator_stock_compose[OF pp_e_child_variation_in_exact_stock
    pp_e_child_variation_in_exact_stock])

theorem gi_exact_M4_nonconstant_proper_view:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<exists>w. w \<noteq> [] \<and> pp_view w r \<noteq> {} \<and> pp_view w r \<noteq> UNIV"
proof -
  have free: "gi_M3_free_for_stock pp_e_exact_operator_stock r"
    using fp by (simp only: gi_exact_M3_fun_prime_iff_free)
  have nonempty: "(pp_e_child_variation \<circ> pp_e_child_variation) r \<noteq> {}"
    using free gi_exact_M4_variation_square_in_stock gi_exact_M4_variation_square_nonzero
    unfolding gi_M3_free_for_stock_def by blast
  obtain i where i: "i \<in> pp_e_child_variation (pp_e_child_variation r)"
    using nonempty by (auto simp only: comp_apply)
  obtain n where n: "n # i \<in> pp_e_child_variation r"
    using i unfolding pp_e_child_variation_def by blast
  obtain a b where yes: "a # n # i \<in> r" and no: "b # n # i \<notin> r"
    using n unfolding pp_e_child_variation_def by blast
  have present: "[a] \<in> pp_view (n # i) r" using yes by (simp add: pp_view_def)
  have absent: "[b] \<notin> pp_view (n # i) r" using no by (simp add: pp_view_def)
  have nonzero: "pp_view (n # i) r \<noteq> {}" using present by blast
  have nontop: "pp_view (n # i) r \<noteq> UNIV" using absent by blast
  show ?thesis by (rule exI[where x="n # i"]) (use nonzero nontop in simp)
qed

section \<open>A fresh one-letter branch hides the copied seed from that view\<close>

lemma gi_exact_M4_fresh_letter:
  obtains b :: nat where "b \<notin> set w"
proof -
  let ?b = "Suc (Max (insert 0 (set w)))"
  have fresh: "?b \<notin> set w"
  proof
    assume member: "?b \<in> set w"
    have "?b \<le> Max (insert 0 (set w))" by (rule Max_ge) (use member in auto)
    then show False by simp
  qed
  show thesis by (rule that[OF fresh])
qed

lemma gi_exact_M4_disjoint_lift_empty_view:
  assumes nonempty: "w \<noteq> []" and fresh: "b \<notin> set w"
  shows "pp_view w (pp_lift [b] r) = {}"
proof (rule pp_view_lift_incomparable_suffixes)
  show "\<nexists>k. w = k @ [b]"
  proof
    assume "\<exists>k. w = k @ [b]"
    then obtain k where "w = k @ [b]" by blast
    then have "b \<in> set w" by simp
    then show False using fresh by contradiction
  qed
  show "\<nexists>k. [b] = k @ w"
  proof
    assume "\<exists>k. [b] = k @ w"
    then obtain k where equation: "[b] = k @ w" by blast
    have subset: "set w \<subseteq> {b}" using arg_cong[OF equation, of set] by auto
    have member: "hd w \<in> set w" by (rule hd_in_set[OF nonempty])
    have "hd w \<in> {b}" by (rule subsetD[OF subset member])
    then have xb: "hd w = b" by simp
    have "b \<in> set w" using member by (simp only: xb)
    then show False using fresh by contradiction
  qed
qed

lemma gi_exact_M4_lift_fun_prime:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "pp_e_exact_fun_prime (pp_lift [b] r)"
proof (rule gi_exact_M6_fun_prime_preimage[where i="[b]"])
  show "pp_e_exact_fun_prime (pp_view [b] (pp_lift [b] r))" using fp by simp
qed

theorem gi_exact_M4_no_recovery_from_lift:
  assumes nonempty: "w \<noteq> []" and fresh: "b \<notin> set w"
    and nonzero: "pp_view w r \<noteq> {}" and nontop: "pp_view w r \<noteq> UNIV"
    and stock: "F \<in> pp_e_exact_operator_stock"
  shows "F (pp_lift [b] r) \<noteq> r"
proof
  assume recovers: "F (pp_lift [b] r) = r"
  have equivariant: "pp_equivariant_operator F" by (rule pp_e_exact_operator_stock_equivariant[OF stock])
  have action: "pp_view w (F (pp_lift [b] r)) = F (pp_view w (pp_lift [b] r))"
    using equivariant unfolding pp_equivariant_operator_def by blast
  have empty: "pp_view w (pp_lift [b] r) = {}"
    by (rule gi_exact_M4_disjoint_lift_empty_view[OF nonempty fresh])
  have collapse: "pp_view w r = F {}" using action by (simp only: recovers empty)
  have extreme: "F {} = {} \<or> F {} = UNIV" by (rule gi_exact_M6_pure_empty_extreme[OF stock])
  show False using collapse extreme nonzero nontop by blast
qed

lemma gi_exact_M4_no_recovery_excludes_reversible_image:
  assumes no_recovery: "\<And>F. F \<in> pp_e_exact_operator_stock \<Longrightarrow> F p \<noteq> r"
  shows "\<not> (\<exists>Z\<in>pp_e_exact_G. p = Z r)"
proof
  assume image: "\<exists>Z\<in>pp_e_exact_G. p = Z r"
  then obtain Z where reversible: "Z \<in> pp_e_exact_G" and p: "p = Z r" by blast
  obtain W where ws: "W \<in> pp_e_exact_operator_stock" and inverse: "W \<circ> Z = id"
    using reversible unfolding pp_e_exact_G_def pp_e_exact_reversible_def by blast
  have recovery: "W p = r" using fun_cong[OF inverse, of r] by (simp add: p)
  show False using no_recovery[OF ws] recovery by contradiction
qed

section \<open>The exact-stock M4 construction, with its choice of branch explicit\<close>

theorem gi_exact_M4_lift_witness:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<exists>b. pp_e_exact_fun_prime (pp_lift [b] r) \<and>
    (\<forall>F\<in>pp_e_exact_operator_stock. F (pp_lift [b] r) \<noteq> r) \<and>
    \<not> (\<exists>Z\<in>pp_e_exact_G. pp_lift [b] r = Z r)"
proof -
  obtain w where nonempty: "w \<noteq> []" and nonzero: "pp_view w r \<noteq> {}"
    and nontop: "pp_view w r \<noteq> UNIV"
    using gi_exact_M4_nonconstant_proper_view[OF fp] by blast
  obtain b where fresh: "b \<notin> set w" by (rule gi_exact_M4_fresh_letter)
  have pfree: "pp_e_exact_fun_prime (pp_lift [b] r)" by (rule gi_exact_M4_lift_fun_prime[OF fp])
  have no_recovery: "F (pp_lift [b] r) \<noteq> r" if fs: "F \<in> pp_e_exact_operator_stock" for F
    by (rule gi_exact_M4_no_recovery_from_lift[OF nonempty fresh nonzero nontop fs])
  have outside: "\<not> (\<exists>Z\<in>pp_e_exact_G. pp_lift [b] r = Z r)"
    by (rule gi_exact_M4_no_recovery_excludes_reversible_image; rule no_recovery; assumption)
  show ?thesis by (rule exI[where x=b]) (use pfree no_recovery outside in blast)
qed

corollary gi_exact_M4_fun_prime_outside_reversible_orbit:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "\<exists>p. pp_e_exact_fun_prime p \<and> (\<forall>F\<in>pp_e_exact_operator_stock. F p \<noteq> r) \<and>
    \<not> (\<exists>Z\<in>pp_e_exact_G. p = Z r)"
proof -
  obtain b where witness: "pp_e_exact_fun_prime (pp_lift [b] r) \<and>
    (\<forall>F\<in>pp_e_exact_operator_stock. F (pp_lift [b] r) \<noteq> r) \<and>
    \<not> (\<exists>Z\<in>pp_e_exact_G. pp_lift [b] r = Z r)"
    using gi_exact_M4_lift_witness[OF fp] by blast
  show ?thesis by (rule exI[where x="pp_lift [b] r"], rule witness)
qed

corollary gi_exact_M4_actual_generic_seed_witness:
  "\<exists>b. pp_e_exact_fun_prime (pp_lift [b] pp_e_generic_raw_seed) \<and>
    (\<forall>F\<in>pp_e_exact_operator_stock. F (pp_lift [b] pp_e_generic_raw_seed) \<noteq> pp_e_generic_raw_seed) \<and>
    \<not> (\<exists>Z\<in>pp_e_exact_G. pp_lift [b] pp_e_generic_raw_seed = Z pp_e_generic_raw_seed)"
  by (rule gi_exact_M4_lift_witness[OF gi_exact_generic_raw_seed_fun_prime])

corollary gi_native_M4_fun_prime_outside_reversible_orbit:
  assumes rich: "sg_rich G" and fp: "gi_stock_fun_prime (gi_exact_native_operator_stock G) r"
  shows "\<exists>p. gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<and>
    (\<forall>F\<in>gi_exact_native_operator_stock G. F p \<noteq> r) \<and>
    \<not> (\<exists>Z\<in>gi_stock_group (gi_exact_native_operator_stock G). p = Z r)"
proof -
  have original: "pp_e_exact_fun_prime r" using fp by (simp only: gi_exact_native_fun_prime_iff[OF rich])
  obtain p where free: "pp_e_exact_fun_prime p"
    and no_recovery: "\<forall>F\<in>pp_e_exact_operator_stock. F p \<noteq> r"
    and outside: "\<not> (\<exists>Z\<in>pp_e_exact_G. p = Z r)"
    using gi_exact_M4_fun_prime_outside_reversible_orbit[OF original] by blast
  have native_free: "gi_stock_fun_prime (gi_exact_native_operator_stock G) p"
    using free by (simp only: gi_exact_native_fun_prime_iff[OF rich])
  have native_recovery: "\<forall>F\<in>gi_exact_native_operator_stock G. F p \<noteq> r"
    using no_recovery by (simp only: gi_exact_native_operator_stock_eq[OF rich])
  have native_outside: "\<not> (\<exists>Z\<in>gi_stock_group (gi_exact_native_operator_stock G). p = Z r)"
    using outside by (simp add: gi_exact_native_group_eq[OF rich])
  show ?thesis by (rule exI[where x=p]) (use native_free native_recovery native_outside in blast)
qed

text \<open>
  Unlike the older conditional M4 proof, this construction requires no
  fixed-r all-view QSS premise. It applies to each fun′ proposition in
  the complete exact closed-logical stock and to the actual generic seed.

  The copy branch is chosen fresh after finding a nonconstant nonempty
  view of r by applying child variation twice. We do not assert that
  a fixed branch such as [0] works for every r. The witness is stronger
  than failure of a reversible-orbit description: no pure operator can
  recover r from the chosen lifted proposition at all.

  These are exact-stock semantic results, not a proof of the source's
  underspecified multiple-fundamental selection proposal and not a PP
  consistency theorem.
\<close>

end
