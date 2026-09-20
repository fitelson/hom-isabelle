theory Bacon_PP_Purity_Operator
  imports 
    "Goodman_Exact_Legacy_01.Bacon_PP_MSet"
begin

section \<open>The purity operator at type \<open>(t \<rightarrow> t) \<rightarrow> t\<close>\<close>

text \<open>
  \<open>Bacon_PP_MSet\<close> formalizes Bacon's local unary function space and its action, and
  shows that its invariant elements are exactly the classifiers.  This theory asks the
  next question up: what is the semantic value of the purity predicate for unary
  propositional operators, and is that value itself invariant?

  The answer is that PP is not obstructed semantically.  The natural value of
  \<open>Pure\<^bsub>t \<rightarrow> t\<^esub>\<close> in the word-action M-set is the operator that sends a local unary
  function \<open>F\<close> to the set of worlds at which the local view of \<open>F\<close> is invariant,
  and that operator is equivariant, hence invariant, hence pure.  It is also
  necessitated: purity, when true, is necessarily true.

  This localizes the difficulty in Goodman's question precisely.  The obstruction is
  not that the purity operator fails to be invariant.  It is that the purity operator
  must additionally lie in a Henkin domain small enough for the Recombination witness
  to escape every proper classifier index, while enlarging the language by a name for
  the purity operator enlarges that domain.  \<open>Bacon_PP_TypeCoherence\<close> shows, from the
  other side, that this operator is not Pure-free definable, so the enlargement is
  genuine.
\<close>

subsection \<open>The operator and its equivariance\<close>

definition pp_purity_operator ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_purity_operator F =
    {i. pp_fun_invariant (pp_fun_view i F)}"

lemma pp_purity_operator_membership:
  "i \<in> pp_purity_operator F \<longleftrightarrow>
    pp_fun_invariant (pp_fun_view i F)"
  by (simp add: pp_purity_operator_def)

theorem pp_purity_operator_root:
  "pp_root_true (pp_purity_operator F) \<longleftrightarrow>
    pp_fun_invariant F"
  by (simp add: pp_root_true_def pp_purity_operator_membership)

text \<open>
  Equivariance: the value of the purity operator at the \<open>j\<close>-view of \<open>F\<close> is the
  \<open>j\<close>-view of its value at \<open>F\<close>.  This is the exact analogue, one type up, of
  \<open>pp_equivariant_operator\<close>.
\<close>

theorem pp_purity_operator_equivariant:
  "pp_view j (pp_purity_operator F) =
    pp_purity_operator (pp_fun_view j F)"
proof (rule set_eqI)
  fix i
  have "i \<in> pp_view j (pp_purity_operator F) \<longleftrightarrow>
      pp_fun_invariant (pp_fun_view (i @ j) F)"
    by (simp add: pp_view_def pp_purity_operator_membership)
  also have "... \<longleftrightarrow>
      pp_fun_invariant (pp_fun_view i (pp_fun_view j F))"
    by (simp add: pp_fun_view_compose)
  also have "... \<longleftrightarrow>
      i \<in> pp_purity_operator (pp_fun_view j F)"
    by (simp add: pp_purity_operator_membership)
  finally show
      "i \<in> pp_view j (pp_purity_operator F) \<longleftrightarrow>
       i \<in> pp_purity_operator (pp_fun_view j F)" .
qed

subsection \<open>Purity is necessitated\<close>

lemma pp_fun_invariant_view:
  assumes invariant: "pp_fun_invariant G"
  shows "pp_fun_invariant (pp_fun_view i G)"
proof -
  have "pp_fun_view i G = G"
    using invariant unfolding pp_fun_invariant_def by blast
  then show ?thesis
    using invariant by simp
qed

theorem pp_purity_operator_necessitated:
  "pp_purity_operator F = pp_sem_box (pp_purity_operator F)"
proof
  show "pp_purity_operator F \<subseteq> pp_sem_box (pp_purity_operator F)"
  proof
    fix i
    assume i_pure: "i \<in> pp_purity_operator F"
    have invariant: "pp_fun_invariant (pp_fun_view i F)"
      using i_pure by (simp add: pp_purity_operator_membership)
    have "k @ i \<in> pp_purity_operator F" for k
    proof -
      have "pp_fun_view (k @ i) F =
          pp_fun_view k (pp_fun_view i F)"
        by (simp add: pp_fun_view_compose)
      moreover have
          "pp_fun_invariant (pp_fun_view k (pp_fun_view i F))"
        using invariant by (rule pp_fun_invariant_view)
      ultimately show ?thesis
        by (simp add: pp_purity_operator_membership)
    qed
    then show "i \<in> pp_sem_box (pp_purity_operator F)"
      by (auto simp: pp_sem_box_accessible_iff pp_accessible_def)
  qed
next
  show "pp_sem_box (pp_purity_operator F) \<subseteq> pp_purity_operator F"
    by (rule pp_sem_box_T)
qed

subsection \<open>Purity of Pure holds in the word-action M-set\<close>

text \<open>
  The action on an operator \<open>H\<close> of type \<open>(t \<rightarrow> t) \<rightarrow> t\<close> is computed exactly as at
  one type lower: apply \<open>H\<close> to a preimage of the argument under the action at
  \<open>t \<rightarrow> t\<close>, then take the view of the result.  The foundational theory
  \<open>Bacon_PP_MSet\<close> now proves that \<open>pp_fun_lift i F\<close> is such a preimage
  inside Bacon's restricted function domain whenever \<open>F\<close> belongs to that domain.
\<close>

definition pp_second_order_view ::
    "pp_word \<Rightarrow>
      ((pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop) \<Rightarrow>
      ((pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop)" where
  "pp_second_order_view i H =
    (\<lambda>F. pp_view i (H (pp_fun_lift i F)))"

definition pp_second_order_invariant ::
    "((pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_second_order_invariant H \<longleftrightarrow>
    (\<forall>i. pp_second_order_view i H = H)"

definition pp_second_order_equivariant ::
    "((pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_second_order_equivariant H \<longleftrightarrow>
    (\<forall>i F. pp_view i (H F) = H (pp_fun_view i F))"

lemma pp_second_order_equivariant_invariant:
  assumes equivariant: "pp_second_order_equivariant H"
  shows "pp_second_order_invariant H"
proof (unfold pp_second_order_invariant_def, intro allI)
  fix i
  show "pp_second_order_view i H = H"
  proof (rule ext)
    fix F
    have "pp_second_order_view i H F =
        pp_view i (H (pp_fun_lift i F))"
      by (simp add: pp_second_order_view_def)
    also have "... = H (pp_fun_view i (pp_fun_lift i F))"
      using equivariant
      unfolding pp_second_order_equivariant_def by blast
    also have "... = H F"
      by simp
    finally show "pp_second_order_view i H F = H F" .
  qed
qed

theorem pp_purity_operator_second_order_equivariant:
  "pp_second_order_equivariant pp_purity_operator"
  unfolding pp_second_order_equivariant_def
  by (rule allI)+ (rule pp_purity_operator_equivariant)

theorem pp_purity_of_pure_holds_in_word_action:
  "pp_second_order_invariant pp_purity_operator"
  using pp_purity_operator_second_order_equivariant
  by (rule pp_second_order_equivariant_invariant)

text \<open>
  Hence the target PP instance is true in the full word-action M-set: the purity
  predicate for unary propositional operators is itself pure.  Recall that
  \<open>pp_root_unary_recombination S R\<close> holds exactly when \<open>pp_orbit R \<subseteq> S\<close> fails or
  \<open>S = UNIV\<close>.  With the full function domain the stock of classifier indices is all of
  \<open>Pow (Pow pp_word)\<close>, and no single \<open>R\<close> can escape every proper index, so
  Recombination fails there.  The consistency question is therefore exactly the
  question whether the domains can be cut down to a stock small enough for a
  Recombination witness while still containing the purity operator.
\<close>

lemma pp_orbit_not_UNIV:
  "pp_orbit R \<noteq> UNIV"
proof
  assume full: "pp_orbit R = UNIV"
  have surjective: "\<exists>i. pp_view i R = P" for P
  proof -
    have "P \<in> pp_orbit R" using full by simp
    then show ?thesis by (auto simp: pp_orbit_def)
  qed
  let ?D = "{i. i \<notin> pp_view i R}"
  obtain j where j: "pp_view j R = ?D"
    using surjective by blast
  have "j \<in> ?D \<longleftrightarrow> j \<notin> pp_view j R"
    by simp
  then show False
    using j by blast
qed

theorem pp_full_stock_has_no_recombination_witness:
  "\<not> (\<forall>S. pp_root_unary_recombination S R)"
proof
  assume all_recombine: "\<forall>S. pp_root_unary_recombination S R"
  obtain Q where Q_outside: "Q \<notin> pp_orbit R"
    using pp_orbit_not_UNIV by blast
  let ?S = "UNIV - {Q}"
  have orbit_inside: "pp_orbit R \<subseteq> ?S"
    using Q_outside by blast
  have proper: "?S \<noteq> UNIV" by blast
  have "pp_root_unary_recombination ?S R"
    using all_recombine by blast
  then show False
    using orbit_inside proper
    by (simp add: pp_root_unary_recombination_iff)
qed

end
