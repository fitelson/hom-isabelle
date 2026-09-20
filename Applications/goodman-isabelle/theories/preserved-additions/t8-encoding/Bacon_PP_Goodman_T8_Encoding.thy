theory Bacon_PP_Goodman_T8_Encoding
  imports 
    "Goodman_Legacy_T7.Bacon_PP_Goodman_T7_Absorption"
begin

section \<open>Goodman T8: exact finite-growth targets\<close>

definition pp_T8_diamond_operator :: oterm where
  "pp_T8_diamond_operator =
    Lam Prop (Neg (Eq Prop (Var 0) ObjFalse))"

lemma typed_pp_T8_diamond_operator:
  "\<Gamma> \<turnstile> pp_T8_diamond_operator : pp_unary_ty"
  unfolding pp_T8_diamond_operator_def pp_unary_ty_def
  using typed_var0[where \<sigma>=Prop and \<Gamma>=\<Gamma>] typed_ObjFalse
  by (intro has_type.Lam has_type.Neg has_type.Eq)

lemma pp_T8_diamond_operator_purity_axiom:
  "pp_pure pp_unary_ty pp_T8_diamond_operator
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_T8_diamond_operator : pp_unary_ty"
    by (rule typed_pp_T8_diamond_operator)
  show "consts_of pp_T8_diamond_operator = {}"
    by (simp add: pp_T8_diamond_operator_def ObjFalse_def ObjTrue_def)
  show "pp_pure pp_unary_ty pp_T8_diamond_operator =
      pp_pure pp_unary_ty pp_T8_diamond_operator"
    by simp
qed

lemma pp_T8_diamond_operator_beta:
  "compatible_step beta_contract
    (App pp_T8_diamond_operator A)
    (Neg (Eq Prop A ObjFalse))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop (Neg (Eq Prop (Var 0) ObjFalse)))
        A)
      (subst0 A (Neg (Eq Prop (Var 0) ObjFalse)))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App pp_T8_diamond_operator A)
      (Neg (Eq Prop A ObjFalse))"
    unfolding pp_T8_diamond_operator_def
    using step
    by (simp add: subst0_def ObjFalse_def ObjTrue_def)
qed

definition pp_T8_base_operators :: "oterm list" where
  "pp_T8_base_operators =
    [pp_identity_operator,
     gd_box_op,
     pp_T8_diamond_operator,
     gd_true_op,
     gd_false_op]"

lemma length_pp_T8_base_operators[simp]:
  "length pp_T8_base_operators = 5"
  by (simp add: pp_T8_base_operators_def)

lemma typed_pp_T8_base_operators:
  "B \<in> set pp_T8_base_operators \<Longrightarrow>
    \<Gamma> \<turnstile> B : pp_unary_ty"
  unfolding pp_T8_base_operators_def
  using typed_pp_identity_operator typed_gd_box_op
    typed_pp_T8_diamond_operator typed_gd_true_op typed_gd_false_op
  by auto

fun pp_T8_disjoin :: "oterm list \<Rightarrow> oterm" where
  "pp_T8_disjoin [] = ObjFalse"
| "pp_T8_disjoin [A] = A"
| "pp_T8_disjoin (A # B # As) =
    Disj A (pp_T8_disjoin (B # As))"

definition pp_T8_kind_atom :: "oterm \<Rightarrow> oterm" where
  "pp_T8_kind_atom B =
    Exists Prop
      (Conj
        (pp_fun_prime (Var 0))
        (Eq Prop
          (Var 1)
          (App B (Var 0))))"

definition pp_T8_kind_property :: "oterm list \<Rightarrow> oterm" where
  "pp_T8_kind_property Bs =
    Lam Prop
      (pp_T8_disjoin (map pp_T8_kind_atom Bs))"

lemma typed_pp_T8_kind_atom:
  assumes B_type: "Prop # Prop # \<Gamma> \<turnstile> B : pp_unary_ty"
  shows "Prop # \<Gamma> \<turnstile> pp_T8_kind_atom B : Prop"
proof -
  have q_type: "Prop # Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have p_type: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have Bq_type:
    "Prop # Prop # \<Gamma> \<turnstile> App B (Var 0) : Prop"
    using B_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T8_kind_atom_def
    using typed_pp_fun_prime[OF q_type] p_type Bq_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_T8_disjoin:
  assumes "\<And>A. A \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T8_disjoin As : Prop"
  using assms
proof (induction As rule: pp_T8_disjoin.induct)
  case 1
  then show ?case by (simp add: typed_ObjFalse)
next
  case (2 A)
  then show ?case by simp
next
  case (3 A B As)
  then show ?case
    by (simp add: has_type.Disj)
qed

lemma typed_pp_T8_kind_property:
  assumes closed_types:
    "\<And>B \<Delta>. B \<in> set Bs \<Longrightarrow>
      \<Delta> \<turnstile> B : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_kind_property Bs : pp_unary_ty"
proof -
  have atoms:
    "\<And>A. A \<in> set (map pp_T8_kind_atom Bs) \<Longrightarrow>
      Prop # \<Gamma> \<turnstile> A : Prop"
  proof -
    fix A
    assume "A \<in> set (map pp_T8_kind_atom Bs)"
    then obtain B where B: "B \<in> set Bs"
      and A: "A = pp_T8_kind_atom B" by auto
    show "Prop # \<Gamma> \<turnstile> A : Prop"
      unfolding A
      using closed_types[OF B, of "Prop # Prop # \<Gamma>"]
      by (rule typed_pp_T8_kind_atom)
  qed
  show ?thesis
    unfolding pp_T8_kind_property_def pp_unary_ty_def
    using typed_pp_T8_disjoin[OF atoms]
    by (rule has_type.Lam)
qed

definition pp_T8_nonempty_subsets :: "oterm list list" where
  "pp_T8_nonempty_subsets =
    filter (\<lambda>xs. xs \<noteq> []) (subseqs pp_T8_base_operators)"

definition pp_T8_growth_operators :: "oterm list" where
  "pp_T8_growth_operators =
    map pp_T8_kind_property pp_T8_nonempty_subsets"

lemma length_pp_T8_nonempty_subsets[simp]:
  "length pp_T8_nonempty_subsets = 31"
  by (simp add: pp_T8_nonempty_subsets_def
      pp_T8_base_operators_def)

lemma length_pp_T8_growth_operators[simp]:
  "length pp_T8_growth_operators = 31"
  by (simp add: pp_T8_growth_operators_def)

fun pp_T8_neq_all :: "otype \<Rightarrow> oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "pp_T8_neq_all \<sigma> A [] = ObjTrue"
| "pp_T8_neq_all \<sigma> A (B # Bs) =
    Conj (Neg (Eq \<sigma> A B)) (pp_T8_neq_all \<sigma> A Bs)"

fun pp_T8_pairwise_distinct :: "otype \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "pp_T8_pairwise_distinct \<sigma> [] = ObjTrue"
| "pp_T8_pairwise_distinct \<sigma> (A # As) =
    Conj
      (pp_T8_neq_all \<sigma> A As)
      (pp_T8_pairwise_distinct \<sigma> As)"

lemma typed_pp_T8_neq_all:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and Bs_type: "\<And>B. B \<in> set Bs \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_T8_neq_all \<sigma> A Bs : Prop"
  using Bs_type
proof (induction Bs)
  case Nil
  then show ?case by (simp add: typed_ObjTrue)
next
  case (Cons B Bs)
  have B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    using Cons.prems by simp
  have tail: "\<Gamma> \<turnstile> pp_T8_neq_all \<sigma> A Bs : Prop"
    using Cons.IH Cons.prems by simp
  show ?case
    using A_type B_type tail
    by (simp add: has_type.Conj has_type.Neg has_type.Eq)
qed

lemma typed_pp_T8_pairwise_distinct:
  assumes As_type: "\<And>A. A \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> A : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_T8_pairwise_distinct \<sigma> As : Prop"
  using As_type
proof (induction As)
  case Nil
  then show ?case by (simp add: typed_ObjTrue)
next
  case (Cons A As)
  have A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    using Cons.prems by simp
  have rest_types: "\<And>B. B \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma>"
    using Cons.prems by simp
  have head:
    "\<Gamma> \<turnstile> pp_T8_neq_all \<sigma> A As : Prop"
    using A_type rest_types by (rule typed_pp_T8_neq_all)
  have tail:
    "\<Gamma> \<turnstile> pp_T8_pairwise_distinct \<sigma> As : Prop"
    using Cons.IH rest_types by blast
  show ?case
    using head tail by (simp add: has_type.Conj)
qed

definition pp_T8_growth_claim :: "oterm \<Rightarrow> oterm" where
  "pp_T8_growth_claim r =
    Conj
      (pp_T8_pairwise_distinct pp_unary_ty
        pp_T8_growth_operators)
      (pp_T8_pairwise_distinct Prop
        (map (\<lambda>X. App X r) pp_T8_growth_operators))"

lemma typed_pp_T8_growth_operator:
  assumes "X \<in> set pp_T8_growth_operators"
  shows "\<Gamma> \<turnstile> X : pp_unary_ty"
proof -
  obtain Bs where Bs:
      "Bs \<in> set pp_T8_nonempty_subsets"
      "X = pp_T8_kind_property Bs"
    using assms
    unfolding pp_T8_growth_operators_def by auto
  have subset: "set Bs \<subseteq> set pp_T8_base_operators"
  proof -
    have member:
      "set Bs \<in> set ` set (subseqs pp_T8_base_operators)"
      using Bs(1)
      unfolding pp_T8_nonempty_subsets_def by auto
    show ?thesis
      using member
      by (simp add: subseqs_powset)
  qed
  show ?thesis
    unfolding Bs(2)
  proof (rule typed_pp_T8_kind_property)
    fix B \<Delta>
    assume "B \<in> set Bs"
    with subset have "B \<in> set pp_T8_base_operators" by blast
    then show "\<Delta> \<turnstile> B : pp_unary_ty"
      by (rule typed_pp_T8_base_operators)
  qed
qed

lemma typed_pp_T8_growth_claim:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T8_growth_claim r : Prop"
proof -
  have ops:
    "\<Gamma> \<turnstile>
      pp_T8_pairwise_distinct pp_unary_ty
        pp_T8_growth_operators : Prop"
    using typed_pp_T8_pairwise_distinct[
      OF typed_pp_T8_growth_operator] .
  have values_type:
    "\<And>P. P \<in> set
        (map (\<lambda>X. App X r) pp_T8_growth_operators)
      \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set
      (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    then obtain X where
      X: "X \<in> set pp_T8_growth_operators"
        "P = App X r" by auto
    show "\<Gamma> \<turnstile> P : Prop"
      unfolding X(2)
      using typed_pp_T8_growth_operator[OF X(1)] r_type
      unfolding pp_unary_ty_def by (rule has_type.App)
  qed
  have d_values:
    "\<Gamma> \<turnstile>
      pp_T8_pairwise_distinct Prop
        (map (\<lambda>X. App X r) pp_T8_growth_operators) : Prop"
    using values_type by (rule typed_pp_T8_pairwise_distinct)
  show ?thesis
    unfolding pp_T8_growth_claim_def
    using ops d_values by (rule has_type.Conj)
qed

text \<open>
  The list is definitionally the 31 nonempty subsets of the five advertised
  base kinds.  The proof theory below must establish, rather than assume,
  that the base kinds are distinct, that every generated property is pure,
  and that both displayed lists are pairwise distinct.
\<close>

end
