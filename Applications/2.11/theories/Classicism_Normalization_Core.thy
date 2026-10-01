theory Classicism_Normalization_Core
  imports "HOL-Nonstandard_Analysis.Free_Ultrafilter" "HOL-Library.Product_Order"
begin

unbundle lattice_syntax

section \<open>The concrete propositional algebra and normalization failure\<close>

text \<open>A root proposition has an actual bit, an intermediate bit, and a
  sequence of terminal bits. The ultrafilter determines its limit bit.
  This theory verifies this algebraic component; it does not by itself
  instantiate the all-type Classicism action-model interface.\<close>

definition norm_U :: "nat filter" where
  "norm_U = (SOME U. freeultrafilter U)"

lemma norm_U_free: "freeultrafilter norm_U"
  unfolding norm_U_def
  by (rule someI_ex) (rule freeultrafilter_Ex, simp)

interpretation norm_U: freeultrafilter norm_U
  by (rule norm_U_free)

type_synonym root_prop = "bool \<times> bool \<times> nat set"
type_synonym middle_prop = "bool \<times> bool"

definition ubit :: "nat set \<Rightarrow> bool" where
  "ubit A \<longleftrightarrow> eventually (\<lambda>n. n \<in> A) norm_U"

lemma ubit_empty [simp]: "\<not> ubit {}"
  using norm_U.proper by (simp add: ubit_def)

lemma ubit_UNIV [simp]: "ubit UNIV"
  by (simp add: ubit_def)

lemma ubit_Compl [simp]: "ubit (- A) = (\<not> ubit A)"
  by (simp add: ubit_def norm_U.eventually_not_iff)

lemma ubit_Int [simp]: "ubit (A \<inter> B) = (ubit A \<and> ubit B)"
  by (simp add: ubit_def eventually_conj_iff)

lemma ubit_Un [simp]: "ubit (A \<union> B) = (ubit A \<or> ubit B)"
  by (simp add: ubit_def norm_U.eventually_disj_iff)

lemma ubit_cofinite: "finite A \<Longrightarrow> ubit (- A)"
  unfolding ubit_def by (rule norm_U.finite') simp

definition to_middle :: "root_prop \<Rightarrow> middle_prop" where
  "to_middle p = (fst (snd p), ubit (snd (snd p)))"

lemma to_middle_triple [simp]:
  "to_middle (a,b,S) = (b, ubit S)"
  by (simp add: to_middle_def)

lemma to_middle_bot [simp]: "to_middle \<bottom> = \<bottom>"
  by (simp add: to_middle_def bot_prod_def)

lemma to_middle_top [simp]: "to_middle \<top> = \<top>"
  by (simp add: to_middle_def top_prod_def)

lemma to_middle_inf:
  "to_middle (p \<sqinter> q) = to_middle p \<sqinter> to_middle q"
  by (cases p; cases q; auto simp: to_middle_def)

lemma to_middle_sup:
  "to_middle (p \<squnion> q) = to_middle p \<squnion> to_middle q"
  by (cases p; cases q; auto simp: to_middle_def)

lemma to_middle_compl:
  "to_middle (- p) = - to_middle p"
  by (cases p; auto simp: to_middle_def)

lemma to_middle_surjective: "surj to_middle"
proof (rule surjI)
  fix y :: middle_prop
  show "to_middle (False, fst y, if snd y then UNIV else {}) = y"
    by (cases y) auto
qed

definition norm_w :: root_prop where
  "norm_w = (False, True, {})"

definition norm_q :: root_prop where
  "norm_q = (False, False, UNIV)"

definition norm_fiber :: "root_prop set" where
  "norm_fiber = {p. to_middle p = to_middle norm_q}"

lemma norm_fiber_triple [simp]:
  "(a,b,S) \<in> norm_fiber \<longleftrightarrow> (\<not> b \<and> ubit S)"
  by (simp add: norm_fiber_def norm_q_def)

lemma norm_fiber_nonempty: "norm_fiber \<noteq> {}"
proof -
  have "norm_q \<in> norm_fiber" by (simp add: norm_fiber_def)
  then show ?thesis by blast
qed

lemma norm_cofinite_member:
  "(False,False,UNIV - {n}) \<in> norm_fiber"
  using ubit_cofinite[of "{n}"] by (simp only: finite_insert finite.emptyI norm_fiber_triple Compl_eq_Diff_UNIV) simp

lemma norm_fiber_lower_bound_bottom:
  assumes lb: "\<And>p. p \<in> norm_fiber \<Longrightarrow> x \<le> p"
  shows "x = \<bottom>"
proof -
  obtain a b S where x: "x = (a,b,S)"
    by (cases x) auto
  have basic: "(False,False,UNIV::nat set) \<in> norm_fiber" by simp
  have ab: "\<not> a \<and> \<not> b"
    using lb[OF basic] by (simp add: x)
  have "S = {}"
  proof (rule ccontr)
    assume "S \<noteq> {}"
    then obtain n where n: "n \<in> S" by blast
    have "S \<subseteq> UNIV - {n}"
      using lb[OF norm_cofinite_member[of n]] by (simp add: x)
    with n show False by blast
  qed
  with ab show ?thesis by (simp add: x bot_prod_def)
qed

theorem normalization_fiber_Inf_bottom: "Inf norm_fiber = (\<bottom>::root_prop)"
  by (rule norm_fiber_lower_bound_bottom) (rule Inf_lower)

theorem normalization_does_not_preserve_fiber:
  "to_middle (Inf norm_fiber) \<noteq> to_middle norm_q"
  by (simp add: normalization_fiber_Inf_bottom norm_q_def bot_prod_def)

theorem normalization_meet_not_in_fiber: "Inf norm_fiber \<notin> norm_fiber"
  using normalization_does_not_preserve_fiber
  by (simp add: norm_fiber_def)

definition ba_atom :: "'a::bounded_lattice_bot \<Rightarrow> bool" where
  "ba_atom a \<longleftrightarrow> a \<noteq> \<bottom> \<and> (\<forall>b. b \<le> a \<longrightarrow> b = \<bottom> \<or> b = a)"

lemma norm_w_atom: "ba_atom norm_w"
  unfolding ba_atom_def norm_w_def
  by (auto simp: less_eq_prod_def prod_eq_iff bot_prod_def)

lemma norm_q_middle_atom: "ba_atom (to_middle norm_q)"
  unfolding ba_atom_def norm_q_def
  by (auto simp: less_eq_prod_def prod_eq_iff bot_prod_def)

theorem normalized_middle_not_atom:
  "\<not> ba_atom (to_middle (Inf norm_fiber))"
  by (simp add: normalization_fiber_Inf_bottom ba_atom_def)

section \<open>Audit of the established scope\<close>

ML \<open>
  val facts = [@{thm norm_U_free}, @{thm to_middle_surjective},
    @{thm to_middle_inf}, @{thm to_middle_sup}, @{thm to_middle_compl},
    @{thm normalization_fiber_Inf_bottom},
    @{thm normalization_does_not_preserve_fiber},
    @{thm normalization_meet_not_in_fiber},
    @{thm norm_w_atom}, @{thm norm_q_middle_atom},
    @{thm normalized_middle_not_atom}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "NORMALIZATION-CORE: 11 clean endpoints; propositional component only";
\<close>

end
