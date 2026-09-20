theory Goodman_Exact_L2_Transfer
  imports Goodman_Exact_Stock_Legacy_02.Bacon_PP_ZF_Exact_L2_Child_Variation
    Goodman_Integration_Logical_Stock.Goodman_Exact_Stock_Correspondence
begin

section \<open>The complete native closed-logical unary stock as raw operators\<close>

definition gi_exact_native_operator_stock :: "sgcontext \<Rightarrow> pp_e_operator set" where
  "gi_exact_native_operator_stock G =
    pp_e_raw_operator ` gi_exact_native_logical_denotations G (Arr Prop Prop)"

theorem gi_exact_native_operator_stock_eq:
  assumes rich: "sg_rich G"
  shows "gi_exact_native_operator_stock G = pp_e_exact_operator_stock"
  by (simp only: gi_exact_native_operator_stock_def pp_e_exact_operator_stock_def
    gi_exact_logical_denotation_sets_equal[OF rich] pp_e_closed_unary_denotations_def)

lemma gi_exact_native_operator_stockI:
  assumes logical: "gb_closed_logical G (Arr Prop Prop) A"
  shows "pp_e_raw_operator (gi_exact_native_closed_den G A) \<in> gi_exact_native_operator_stock G"
  using logical unfolding gi_exact_native_operator_stock_def gi_exact_native_logical_denotations_def by blast

lemma gi_exact_native_operator_stockE:
  assumes member: "F \<in> gi_exact_native_operator_stock G"
  obtains A where "gb_closed_logical G (Arr Prop Prop) A"
    "F = pp_e_raw_operator (gi_exact_native_closed_den G A)"
  using member unfolding gi_exact_native_operator_stock_def gi_exact_native_logical_denotations_def by blast

lemma gi_exact_native_operator_stock_countable:
  "sg_rich G \<Longrightarrow> countable (gi_exact_native_operator_stock G)"
  by (simp only: gi_exact_native_operator_stock_eq; rule pp_e_exact_operator_stock_countable)

lemma gi_exact_native_identity_in_stock:
  "sg_rich G \<Longrightarrow> id \<in> gi_exact_native_operator_stock G"
  by (simp only: gi_exact_native_operator_stock_eq; rule pp_e_exact_identity_in_stock)

lemma gi_exact_native_operator_stock_compose:
  "sg_rich G \<Longrightarrow> F \<in> gi_exact_native_operator_stock G \<Longrightarrow>
    H \<in> gi_exact_native_operator_stock G \<Longrightarrow> F \<circ> H \<in> gi_exact_native_operator_stock G"
  by (simp only: gi_exact_native_operator_stock_eq; rule pp_e_exact_operator_stock_compose; assumption)

text \<open>
  The preceding equality is about actual operator values, not just truth
  at the root. Native witnesses range over every closed logical term,
  not merely the image of a translation. The local-identity-saturated
  Pure predicate is a distinct object; its relation to the object-language
  L2 formula requires the additional semantic bridge, not just this set
  equality.
\<close>

section \<open>Stock-parametric definitions of Goodman's semantic principles\<close>

definition gi_stock_fun_prime :: "('p \<Rightarrow> 'p) set \<Rightarrow> 'p \<Rightarrow> bool" where
  "gi_stock_fun_prime S p \<longleftrightarrow>
    (\<forall>F\<in>S. \<forall>H\<in>S. F p = H p \<longrightarrow> F = H)"

definition gi_stock_reversible :: "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool" where
  "gi_stock_reversible S Z \<longleftrightarrow>
    Z \<in> S \<and> (\<exists>W\<in>S. Z \<circ> W = id \<and> W \<circ> Z = id)"

definition gi_stock_group :: "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) set" where
  "gi_stock_group S = {Z. gi_stock_reversible S Z}"

definition gi_stock_same_kind ::
  "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool" where
  "gi_stock_same_kind S X Y \<longleftrightarrow> (\<exists>Z\<in>gi_stock_group S. X = Y \<circ> Z)"

definition gi_stock_L2_pair ::
  "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool" where
  "gi_stock_L2_pair S X Y \<longleftrightarrow>
    X \<in> S \<and> Y \<in> S \<and>
    (\<forall>p q. gi_stock_fun_prime S p \<longrightarrow> gi_stock_fun_prime S q \<longrightarrow>
      X p = Y q \<longrightarrow> gi_stock_same_kind S X Y)"

definition gi_stock_L2 :: "('p \<Rightarrow> 'p) set \<Rightarrow> bool" where
  "gi_stock_L2 S \<longleftrightarrow> (\<forall>X\<in>S. \<forall>Y\<in>S. gi_stock_L2_pair S X Y)"

definition gi_stock_strong_L2_pair ::
  "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool" where
  "gi_stock_strong_L2_pair S X Y \<longleftrightarrow>
    X \<in> S \<and> Y \<in> S \<and>
    (\<forall>p q. gi_stock_fun_prime S p \<longrightarrow> gi_stock_fun_prime S q \<longrightarrow>
      X p = Y q \<longrightarrow> (\<exists>Z\<in>gi_stock_group S. X = Y \<circ> Z \<and> q = Z p))"

definition gi_stock_strong_L2 :: "('p \<Rightarrow> 'p) set \<Rightarrow> bool" where
  "gi_stock_strong_L2 S \<longleftrightarrow> (\<forall>X\<in>S. \<forall>Y\<in>S. gi_stock_strong_L2_pair S X Y)"

definition gi_stock_right_cancellative ::
  "('p \<Rightarrow> 'p) set \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> bool" where
  "gi_stock_right_cancellative S X \<longleftrightarrow>
    (\<forall>A\<in>S. \<forall>B\<in>S. A \<circ> X = B \<circ> X \<longrightarrow> A = B)"

section \<open>Correspondence with the existing exact-stock predicates\<close>

lemma gi_exact_native_fun_prime_iff:
  "sg_rich G \<Longrightarrow> gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<longleftrightarrow> pp_e_exact_fun_prime p"
  by (simp only: gi_exact_native_operator_stock_eq gi_stock_fun_prime_def
    pp_e_exact_fun_prime_def pp_stock_fun_prime_def)

lemma gi_exact_native_reversible_iff:
  "sg_rich G \<Longrightarrow> gi_stock_reversible (gi_exact_native_operator_stock G) Z \<longleftrightarrow> pp_e_exact_reversible Z"
  by (simp only: gi_exact_native_operator_stock_eq gi_stock_reversible_def pp_e_exact_reversible_def)

lemma gi_exact_native_group_eq:
  "sg_rich G \<Longrightarrow> gi_stock_group (gi_exact_native_operator_stock G) = pp_e_exact_G"
  by (simp only: gi_stock_group_def gi_exact_native_reversible_iff pp_e_exact_G_def)

lemma gi_exact_native_same_kind_iff:
  "sg_rich G \<Longrightarrow> gi_stock_same_kind (gi_exact_native_operator_stock G) X Y \<longleftrightarrow> pp_e_exact_same_kind X Y"
  by (simp only: gi_stock_same_kind_def gi_exact_native_group_eq pp_e_exact_same_kind_def)

lemma gi_exact_native_L2_pair_iff:
  "sg_rich G \<Longrightarrow> gi_stock_L2_pair (gi_exact_native_operator_stock G) X Y \<longleftrightarrow> pp_e_exact_L2_pair X Y"
  by (simp only: gi_stock_L2_pair_def gi_stock_fun_prime_def gi_stock_same_kind_def
    gi_stock_group_def gi_stock_reversible_def gi_exact_native_operator_stock_eq
    pp_e_exact_L2_pair_def pp_e_exact_fun_prime_def pp_stock_fun_prime_def
    pp_e_exact_same_kind_def pp_e_exact_G_def pp_e_exact_reversible_def)

theorem gi_exact_native_L2_iff:
  "sg_rich G \<Longrightarrow> gi_stock_L2 (gi_exact_native_operator_stock G) \<longleftrightarrow> pp_e_exact_L2"
  by (simp only: gi_stock_L2_def gi_stock_L2_pair_def gi_stock_fun_prime_def gi_stock_same_kind_def
    gi_stock_group_def gi_stock_reversible_def gi_exact_native_operator_stock_eq
    pp_e_exact_L2_def pp_e_exact_L2_pair_def pp_e_exact_fun_prime_def pp_stock_fun_prime_def
    pp_e_exact_same_kind_def pp_e_exact_G_def pp_e_exact_reversible_def)

lemma gi_exact_native_strong_L2_pair_iff:
  "sg_rich G \<Longrightarrow>
    gi_stock_strong_L2_pair (gi_exact_native_operator_stock G) X Y \<longleftrightarrow> pp_e_exact_strong_L2_pair X Y"
  by (simp only: gi_stock_strong_L2_pair_def gi_stock_fun_prime_def gi_stock_group_def
    gi_stock_reversible_def gi_exact_native_operator_stock_eq pp_e_exact_strong_L2_pair_def
    pp_e_exact_fun_prime_def pp_stock_fun_prime_def pp_e_exact_G_def pp_e_exact_reversible_def)

theorem gi_exact_native_strong_L2_iff:
  "sg_rich G \<Longrightarrow> gi_stock_strong_L2 (gi_exact_native_operator_stock G) \<longleftrightarrow> pp_e_exact_strong_L2"
  by (simp only: gi_stock_strong_L2_def gi_stock_strong_L2_pair_def gi_stock_fun_prime_def
    gi_stock_group_def gi_stock_reversible_def gi_exact_native_operator_stock_eq
    pp_e_exact_strong_L2_def pp_e_exact_strong_L2_pair_def pp_e_exact_fun_prime_def
    pp_stock_fun_prime_def pp_e_exact_G_def pp_e_exact_reversible_def)

lemma gi_exact_native_right_cancellative_iff:
  "sg_rich G \<Longrightarrow>
    gi_stock_right_cancellative (gi_exact_native_operator_stock G) Z \<longleftrightarrow> pp_e_exact_right_cancellative Z"
  by (simp only: gi_stock_right_cancellative_def gi_exact_native_operator_stock_eq
    pp_e_exact_right_cancellative_def)

section \<open>The actual child-variation witness in the complete native stock\<close>

theorem gi_exact_native_child_variation_logical_witness:
  assumes rich: "sg_rich G"
  shows "\<exists>A. gb_closed_logical G (Arr Prop Prop) A \<and>
    pp_e_raw_operator (gi_exact_native_closed_den G A) = pp_e_child_variation"
proof -
  obtain A where logical: "gb_closed_logical G (Arr Prop Prop) A"
    and denotation: "gi_exact_native_closed_den G A = pp_e_closed_den pp_e_HO_child_variation_term"
    using gi_old_closed_logical_native_witness[OF rich
      pp_e_HO_child_variation_terms_typed(3) pp_e_HO_child_variation_terms_logical(3)] by blast
  have raw: "pp_e_raw_operator (gi_exact_native_closed_den G A) = pp_e_child_variation"
    by (simp only: denotation pp_e_raw_operator_HO_child_variation)
  show ?thesis by (rule exI[where x=A], rule conjI[OF logical raw])
qed

theorem gi_exact_native_child_variation_in_stock:
  assumes rich: "sg_rich G"
  shows "pp_e_child_variation \<in> gi_exact_native_operator_stock G"
proof -
  obtain A where logical: "gb_closed_logical G (Arr Prop Prop) A"
    and raw: "pp_e_raw_operator (gi_exact_native_closed_den G A) = pp_e_child_variation"
    using gi_exact_native_child_variation_logical_witness[OF rich] by blast
  show ?thesis using gi_exact_native_operator_stockI[OF logical] by (simp only: raw)
qed

theorem gi_exact_native_fun_prime_exists:
  "sg_rich G \<Longrightarrow> \<exists>p. gi_stock_fun_prime (gi_exact_native_operator_stock G) p"
  by (simp only: gi_exact_native_fun_prime_iff; rule pp_e_exact_fun_prime_exists)

theorem gi_exact_native_child_variation_right_cancellative:
  "sg_rich G \<Longrightarrow> gi_stock_right_cancellative (gi_exact_native_operator_stock G) pp_e_child_variation"
  by (simp only: gi_exact_native_right_cancellative_iff; rule pp_e_exact_child_variation_right_cancellative)

theorem gi_exact_native_child_variation_nonreversible:
  "sg_rich G \<Longrightarrow> \<not> gi_stock_reversible (gi_exact_native_operator_stock G) pp_e_child_variation"
  by (simp only: gi_exact_native_reversible_iff; rule pp_e_child_variation_not_exact_reversible)

theorem gi_exact_native_child_variation_preserves_fun_prime:
  "sg_rich G \<Longrightarrow> gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<Longrightarrow>
    gi_stock_fun_prime (gi_exact_native_operator_stock G) (pp_e_child_variation p)"
  by (simp only: gi_exact_native_fun_prime_iff; rule pp_e_child_variation_preserves_fun_prime; assumption)

lemma gi_exact_native_child_variation_not_identity_kind:
  assumes rich: "sg_rich G"
  shows "\<not> gi_stock_same_kind (gi_exact_native_operator_stock G) id pp_e_child_variation"
proof
  assume kind: "gi_stock_same_kind (gi_exact_native_operator_stock G) id pp_e_child_variation"
  have old_kind: "pp_e_exact_same_kind id pp_e_child_variation"
    using kind by (simp only: gi_exact_native_same_kind_iff[OF rich])
  have member: "pp_e_child_variation \<in> pp_e_exact_G"
    by (rule pp_e_exact_same_kind_id_imp_reversible[OF old_kind])
  show False using member pp_e_child_variation_not_in_exact_G by contradiction
qed

theorem gi_exact_native_child_variation_certificate:
  assumes rich: "sg_rich G"
  shows "pp_e_child_variation \<in> gi_exact_native_operator_stock G"
    and "surj pp_e_child_variation"
    and "\<not> inj pp_e_child_variation"
    and "pp_e_child_variation (- P) = pp_e_child_variation P"
    and "gi_stock_right_cancellative (gi_exact_native_operator_stock G) pp_e_child_variation"
    and "\<not> gi_stock_reversible (gi_exact_native_operator_stock G) pp_e_child_variation"
proof -
  show "pp_e_child_variation \<in> gi_exact_native_operator_stock G"
    by (rule gi_exact_native_child_variation_in_stock[OF rich])
  show "surj pp_e_child_variation" by (rule pp_e_child_variation_surjective)
  show "\<not> inj pp_e_child_variation" by (rule pp_e_child_variation_not_injective)
  show "pp_e_child_variation (- P) = pp_e_child_variation P"
    by (rule pp_e_child_variation_complement)
  show "gi_stock_right_cancellative (gi_exact_native_operator_stock G) pp_e_child_variation"
    by (rule gi_exact_native_child_variation_right_cancellative[OF rich])
  show "\<not> gi_stock_reversible (gi_exact_native_operator_stock G) pp_e_child_variation"
    by (rule gi_exact_native_child_variation_nonreversible[OF rich])
qed

theorem gi_exact_native_L2_counterexample:
  assumes rich: "sg_rich G"
  shows "\<exists>p. gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<and>
    gi_stock_fun_prime (gi_exact_native_operator_stock G) (pp_e_child_variation p) \<and>
    id \<in> gi_exact_native_operator_stock G \<and>
    pp_e_child_variation \<in> gi_exact_native_operator_stock G \<and>
    id (pp_e_child_variation p) = pp_e_child_variation p \<and>
    \<not> gi_stock_same_kind (gi_exact_native_operator_stock G) id pp_e_child_variation"
proof -
  obtain p where fp: "gi_stock_fun_prime (gi_exact_native_operator_stock G) p"
    using gi_exact_native_fun_prime_exists[OF rich] by blast
  have fzp: "gi_stock_fun_prime (gi_exact_native_operator_stock G) (pp_e_child_variation p)"
    by (rule gi_exact_native_child_variation_preserves_fun_prime[OF rich fp])
  show ?thesis by (rule exI[where x=p])
    (use fp fzp gi_exact_native_identity_in_stock[OF rich]
      gi_exact_native_child_variation_in_stock[OF rich]
      gi_exact_native_child_variation_not_identity_kind[OF rich] in simp)
qed

theorem gi_exact_native_L2_false:
  assumes rich: "sg_rich G"
  shows "\<not> gi_stock_L2 (gi_exact_native_operator_stock G)"
proof
  assume l2: "gi_stock_L2 (gi_exact_native_operator_stock G)"
  obtain p where fp: "gi_stock_fun_prime (gi_exact_native_operator_stock G) p"
    and fzp: "gi_stock_fun_prime (gi_exact_native_operator_stock G) (pp_e_child_variation p)"
    and ident: "id \<in> gi_exact_native_operator_stock G"
    and variation: "pp_e_child_variation \<in> gi_exact_native_operator_stock G"
    and not_kind: "\<not> gi_stock_same_kind (gi_exact_native_operator_stock G) id pp_e_child_variation"
    using gi_exact_native_L2_counterexample[OF rich] by blast
  have pair: "gi_stock_L2_pair (gi_exact_native_operator_stock G) id pp_e_child_variation"
    using l2 ident variation unfolding gi_stock_L2_def by blast
  have kind: "gi_stock_same_kind (gi_exact_native_operator_stock G) id pp_e_child_variation"
    using pair fp fzp unfolding gi_stock_L2_pair_def by auto
  show False using kind not_kind by contradiction
qed

corollary gi_exact_native_strong_L2_false:
  assumes rich: "sg_rich G"
  shows "\<not> gi_stock_strong_L2 (gi_exact_native_operator_stock G)"
  by (simp only: gi_exact_native_strong_L2_iff[OF rich];
    rule pp_e_child_variation_refutes_exact_strong_L2)

text \<open>
  The counterexample uses X=id, Y=child variation, with inputs Zp and p.
  Both inputs are fun′ for precisely the complete native closed-logical
  raw stock. Child variation is surjective but not injective, is right
  cancellative on this stock, and has no two-sided pure inverse.

  These are fixed-stock semantic L2 results. They do not yet evaluate
  the object-language L2 formula under the local-saturated Pure predicate,
  and do not quantify over arbitrary enlarged pure stocks. No PP model
  or conclusion about Goodman's consistency question is asserted.
\<close>

end
