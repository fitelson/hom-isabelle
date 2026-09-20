theory Bacon_PP_Goodman_Granularity
  imports
    
    "Goodman_Legacy_T9_Infinitude.Bacon_PP_Goodman_T9_Infinitude"
    "HOL-Library.Countable_Set_Type"
begin

unbundle cardinal_syntax

section \<open>Goodman Attack 2: granularity and the reversible operators\<close>

text \<open>
  Goodman asks whether an independently motivated principle about the grain of
  propositions can show that every pure reversible unary operator is uniformly
  truth-preserving or uniformly truth-flipping.  The first results identify the
  exact semantic content of that proposal without identifying propositions that
  merely have the same truth value.
\<close>

definition pp_truth_fibre_congruence ::
    "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool"
where
  "pp_truth_fibre_congruence holds Z \<longleftrightarrow>
    (\<forall>p q. holds p = holds q \<longrightarrow> holds (Z p) = holds (Z q))"

definition pp_sem_truth_preserving ::
    "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool"
where
  "pp_sem_truth_preserving holds Z \<longleftrightarrow>
    (\<forall>p. holds (Z p) = holds p)"

definition pp_sem_truth_flipping ::
    "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool"
where
  "pp_sem_truth_flipping holds Z \<longleftrightarrow>
    (\<forall>p. holds (Z p) = (\<not> holds p))"

theorem pp_surjective_truth_fibre_congruence_imp_uniform:
  assumes surjective: "surj Z"
    and true_proposition: "holds t"
    and false_proposition: "\<not> holds f"
    and congruence: "pp_truth_fibre_congruence holds Z"
  shows
    "pp_sem_truth_preserving holds Z \<or>
      pp_sem_truth_flipping holds Z"
proof -
  have same_true:
      "\<And>p. holds p \<Longrightarrow> holds (Z p) = holds (Z t)"
    using congruence true_proposition
    unfolding pp_truth_fibre_congruence_def by blast
  have same_false:
      "\<And>p. \<not> holds p \<Longrightarrow> holds (Z p) = holds (Z f)"
    using congruence false_proposition
    unfolding pp_truth_fibre_congruence_def by blast
  have different_outputs: "holds (Z t) \<noteq> holds (Z f)"
  proof
    assume equal: "holds (Z t) = holds (Z f)"
    obtain p where t_Zp: "t = Z p"
      using surjective by (rule surjE)
    have Zp: "Z p = t" using t_Zp by simp
    obtain q where f_Zq: "f = Z q"
      using surjective by (rule surjE)
    have Zq: "Z q = f" using f_Zq by simp
    have p_class:
        "holds (Z p) = holds (Z t) \<or>
          holds (Z p) = holds (Z f)"
      using same_true[of p] same_false[of p] by blast
    have q_class:
        "holds (Z q) = holds (Z t) \<or>
          holds (Z q) = holds (Z f)"
      using same_true[of q] same_false[of q] by blast
    show False
      using p_class q_class equal Zp Zq
        true_proposition false_proposition by simp
  qed
  show ?thesis
  proof (cases "holds (Z t)")
    case True
    then have false_output: "\<not> holds (Z f)"
      using different_outputs by simp
    have preserving: "\<And>p. holds (Z p) = holds p"
    proof -
      fix p
      show "holds (Z p) = holds p"
      proof (cases "holds p")
        case True_p: True
        show ?thesis
          using same_true[OF True_p] True True_p by simp
      next
        case False_p: False
        show ?thesis
          using same_false[OF False_p] false_output False_p by simp
      qed
    qed
    show ?thesis
      unfolding pp_sem_truth_preserving_def using preserving by blast
  next
    case False
    then have true_output: "holds (Z f)"
      using different_outputs by simp
    have flipping: "\<And>p. holds (Z p) = (\<not> holds p)"
    proof -
      fix p
      show "holds (Z p) = (\<not> holds p)"
      proof (cases "holds p")
        case True_p: True
        show ?thesis
          using same_true[OF True_p] False True_p by simp
      next
        case False_p: False
        show ?thesis
          using same_false[OF False_p] true_output False_p by simp
      qed
    qed
    show ?thesis
      unfolding pp_sem_truth_flipping_def using flipping by blast
  qed
qed

corollary pp_bijective_truth_fibre_congruence_imp_uniform:
  assumes "bij Z"
    and "holds t"
    and "\<not> holds f"
    and "pp_truth_fibre_congruence holds Z"
  shows
    "pp_sem_truth_preserving holds Z \<or>
      pp_sem_truth_flipping holds Z"
proof (rule pp_surjective_truth_fibre_congruence_imp_uniform)
  show "surj Z"
    using assms(1) unfolding bij_def by blast
  show "holds t" by (rule assms(2))
  show "\<not> holds f" by (rule assms(3))
  show "pp_truth_fibre_congruence holds Z" by (rule assms(4))
qed

definition pp_fregean_granularity :: "('p \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_fregean_granularity holds \<longleftrightarrow>
    (\<forall>p q. holds p = holds q \<longrightarrow> p = q)"

lemma pp_fregean_granularity_imp_truth_fibre_congruence:
  assumes "pp_fregean_granularity holds"
  shows "pp_truth_fibre_congruence holds Z"
  using assms
  unfolding pp_fregean_granularity_def
    pp_truth_fibre_congruence_def by blast

corollary pp_fregean_granularity_imp_uniform:
  assumes "pp_fregean_granularity holds"
    and "bij Z"
    and "holds t"
    and "\<not> holds f"
  shows
    "pp_sem_truth_preserving holds Z \<or>
      pp_sem_truth_flipping holds Z"
proof (rule pp_bijective_truth_fibre_congruence_imp_uniform)
  show "bij Z" by (rule assms(2))
  show "holds t" by (rule assms(3))
  show "\<not> holds f" by (rule assms(4))
  show "pp_truth_fibre_congruence holds Z"
    using assms(1)
    by (rule pp_fregean_granularity_imp_truth_fibre_congruence)
qed

theorem pp_fregean_granularity_excludes_third_proposition:
  assumes fregean: "pp_fregean_granularity holds"
    and true_proposition: "holds t"
    and false_proposition: "\<not> holds f"
    and distinct_true: "r \<noteq> t"
    and distinct_false: "r \<noteq> f"
  shows False
proof (cases "holds r")
  case True
  have "r = t"
    using fregean True true_proposition
    unfolding pp_fregean_granularity_def by blast
  then show False using distinct_true by contradiction
next
  case False
  have "r = f"
    using fregean False false_proposition
    unfolding pp_fregean_granularity_def by blast
  then show False using distinct_false by contradiction
qed

text \<open>
  The Fregean Axiom is therefore too strong for Goodman's problem.  It yields
  TU, but it also eliminates the required third proposition before PP enters.
  Functionality alone does not have either consequence, as the following
  finite counterexample records.
\<close>

definition pp_split_truth :: "bool \<times> bool \<Rightarrow> bool" where
  "pp_split_truth p = fst p"

definition pp_split_invertible ::
    "bool \<times> bool \<Rightarrow> bool \<times> bool"
where
  "pp_split_invertible p =
    ((if snd p then fst p else \<not> fst p), snd p)"

lemma pp_split_invertible_involution:
  "pp_split_invertible (pp_split_invertible p) = p"
  by (cases p) (simp add: pp_split_invertible_def)

lemma pp_split_invertible_bijective:
  "bij pp_split_invertible"
proof (rule bijI)
  show "inj pp_split_invertible"
  proof (rule injI)
    fix p q
    assume equality: "pp_split_invertible p = pp_split_invertible q"
    have
      "pp_split_invertible (pp_split_invertible p) =
        pp_split_invertible (pp_split_invertible q)"
      using equality by simp
    then show "p = q"
      by (simp add: pp_split_invertible_involution)
  qed
  show "surj pp_split_invertible"
    by (rule surjI[of pp_split_invertible pp_split_invertible])
      (rule pp_split_invertible_involution)
qed

lemma pp_split_invertible_not_truth_fibre_congruent:
  "\<not> pp_truth_fibre_congruence
    pp_split_truth pp_split_invertible"
  unfolding pp_truth_fibre_congruence_def
    pp_split_truth_def pp_split_invertible_def
  by (intro notI) (drule spec[of _ "(True, True)"];
      drule spec[of _ "(True, False)"]; simp)

lemma pp_split_invertible_not_truth_uniform:
  "\<not> pp_sem_truth_preserving pp_split_truth pp_split_invertible
    \<and>
   \<not> pp_sem_truth_flipping pp_split_truth pp_split_invertible"
  unfolding pp_sem_truth_preserving_def pp_sem_truth_flipping_def
    pp_split_truth_def pp_split_invertible_def
  by auto

text \<open>
  Thus the truth-value partition being a congruence for the action of the
  reversible operators suffices for TU.  This does not yet derive TU: on the
  two-cell partition it is precisely the substantive claim that a reversible
  operator cannot split either truth fibre.  Functionality and Modalized
  Functionality do not state this claim.
\<close>

subsection \<open>QLN reduces TU to one noncontingency claim\<close>

definition pp_sem_agreement_noncontingent ::
    "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow>
      (('p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
      ('p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> bool"
where
  "pp_sem_agreement_noncontingent necessary neg agree Z r \<longleftrightarrow>
    necessary (agree Z r) \<or> necessary (neg (agree Z r))"

theorem pp_QLN_truth_uniform_iff_agreement_noncontingent:
  fixes holds :: "'p \<Rightarrow> bool"
    and necessary :: "'p \<Rightarrow> bool"
    and neg :: "'p \<Rightarrow> 'p"
    and agree :: "('p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'p"
  assumes agreement_truth:
      "\<And>p. holds (agree Z p) \<longleftrightarrow> (holds (Z p) = holds p)"
    and negation_truth: "\<And>p. holds (neg p) \<longleftrightarrow> (\<not> holds p)"
    and agreement_QLN:
      "necessary (agree Z r) \<longleftrightarrow> (\<forall>p. holds (agree Z p))"
    and disagreement_QLN:
      "necessary (neg (agree Z r)) \<longleftrightarrow>
        (\<forall>p. holds (neg (agree Z p)))"
  shows
    "pp_sem_agreement_noncontingent necessary neg agree Z r \<longleftrightarrow>
      (pp_sem_truth_preserving holds Z \<or>
        pp_sem_truth_flipping holds Z)"
proof -
  have preserving:
      "(\<forall>p. holds (agree Z p)) \<longleftrightarrow>
        pp_sem_truth_preserving holds Z"
    using agreement_truth
    unfolding pp_sem_truth_preserving_def by simp
  have flipping:
      "(\<forall>p. holds (neg (agree Z p))) \<longleftrightarrow>
        pp_sem_truth_flipping holds Z"
    using agreement_truth negation_truth
    unfolding pp_sem_truth_flipping_def by simp
  show ?thesis
    unfolding pp_sem_agreement_noncontingent_def
    using agreement_QLN disagreement_QLN preserving flipping
    by blast
qed

text \<open>
  For the object-language instance, \<open>agree Z p\<close> is
  \<open>Z p \<longleftrightarrow> p\<close>.  Its operator and its pointwise negation are closed
  logical constructions from a pure \<open>Z\<close>.  Full unary QLN therefore says that
  their values at a fundamental proposition \<open>r\<close> are necessary exactly when
  the corresponding conditions hold of every proposition.  The theorem shows
  that Attack 2 has a sharp remaining premise:

  \[
    \<forall>Z\<in>G\;\bigl(\Box(Zr\leftrightarrow r)\lor
      \Box\neg(Zr\leftrightarrow r)\bigr).
  \]

  Proving this is sufficient for TU.  It is not a consequence of reversibility
  alone: Goodman's rebuilt M5 operator supplies the contrary pattern in the
  PP-free theory.
\<close>

subsection \<open>A cardinal granularity ceiling\<close>

theorem pp_attack2_kind_sized_group_refutes_attack3:
  assumes exponential_lower_bound: "|Pow K| \<le>o |G|"
    and kind_sized_group: "|G| \<le>o |K|"
  shows False
proof -
  have powerset_below_kinds: "|Pow K| \<le>o |K|"
    using exponential_lower_bound kind_sized_group
    by (rule ordLeq_transitive)
  have kinds_below_powerset: "|K| <o |Pow K|"
    by (rule card_of_Pow)
  show False
    using kinds_below_powerset powerset_below_kinds
      not_ordLess_ordLeq by blast
qed

theorem pp_attack2_kind_bounded_descriptions_refute_attack3:
  fixes describe :: "'g \<Rightarrow> 'd"
  assumes descriptions_injective: "inj_on describe G"
    and descriptions_in: "describe ` G \<subseteq> D"
    and description_space_kind_sized: "|D| \<le>o |K|"
    and exponential_lower_bound: "|Pow K| \<le>o |G|"
  shows False
proof -
  have group_below_descriptions: "|G| \<le>o |D|"
  proof -
    have "\<exists>f. inj_on f G \<and> f ` G \<subseteq> D"
      using descriptions_injective descriptions_in by blast
    then show ?thesis
      using card_of_ordLeq[of G D] by simp
  qed
  have kind_sized_group: "|G| \<le>o |K|"
    using group_below_descriptions description_space_kind_sized
    by (rule ordLeq_transitive)
  show False
    using exponential_lower_bound kind_sized_group
    by (rule pp_attack2_kind_sized_group_refutes_attack3)
qed

corollary pp_attack2_countable_group_refutes_attack3:
  assumes infinite_kinds: "infinite K"
    and countable_group: "countable G"
    and exponential_lower_bound: "|Pow K| \<le>o |G|"
  shows False
proof -
  have group_below_nat: "|G| \<le>o |UNIV :: nat set|"
    using countable_group
    unfolding countable_card_of_nat .
  have nat_below_kinds: "|UNIV :: nat set| \<le>o |K|"
    using infinite_kinds
    unfolding infinite_iff_card_of_nat .
  have kind_sized_group: "|G| \<le>o |K|"
    using group_below_nat nat_below_kinds
    by (rule ordLeq_transitive)
  show False
    using exponential_lower_bound kind_sized_group
    by (rule pp_attack2_kind_sized_group_refutes_attack3)
qed

text \<open>
  The second theorem is the useful cardinal form of the granularity route.
  Once Attack 3 has supplied \<open>|Pow K| \<le>o |G|\<close>, it is enough that every
  pure reversible operator have a unique description drawn from a stock no
  larger than the kinds.  No classification of the individual operators is
  then required.  Finite strings over an infinite set of kinds are the
  intended granularity instance, since that description space has the same
  cardinality as the kinds.

  This explains both the promise and the limitation of syntactic granularity.
  Bacon's exact closed-logical stock is countable because closed terms are
  finite.  The countable-group corollary therefore shows that Bacon's exact
  stock cannot realize the Attack 3 package once PC and L2 produce its
  exponential lower bound.  But the object theory contains only the forward
  Purity schema; it does not say that every entity satisfying \<open>Pure\<close> is
  denoted by a closed logical term.  A model of PP may therefore enlarge the
  extension of \<open>Pure\<close>, and deriving the countability premise from CEV+
  would need an additional completeness principle for purity.
\<close>

end
