theory Goodman_TU_Inv_Exhaustion
  imports Goodman_T1_Transfer
begin

section \<open>Truth-uniformity becomes identity classification under Exhaustion\<close>

text \<open>
  The Boolean parameter b distinguishes the preserving branch (False)
  from the flipping branch (True). Both quantified tests are closed
  logical builders applied to Z. Thus Pure(Z) makes the test proposition
  pure; zeroary Exhaustion promotes its truth to necessity. Unary
  Intensionality, not contextual Equivalence, then identifies Z with
  identity or negation. No PP, L2, or fun′ existence assumption occurs.
\<close>

definition gi_uniform_test where
  "gi_uniform_test b Z = (if b then pp_truth_flipping Z else pp_truth_preserving Z)"

definition gi_uniform_operator where
  "gi_uniform_operator b = (if b then pp_negation_operator else pp_identity_operator)"

definition gi_uniform_literal where
  "gi_uniform_literal b = (if b then Neg (Var 0) else Var 0)"

definition gi_uniform_builder where
  "gi_uniform_builder b = Lam pp_unary_ty (gi_uniform_test b (Var 0))"

lemma gi_uniform_test_type:
  assumes "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> gi_uniform_test b Z : Prop"
  using typed_pp_truth_flipping[OF assms] typed_pp_truth_preserving[OF assms]
  unfolding gi_uniform_test_def by (cases b; simp)

lemma gi_uniform_operator_type:
  "\<Gamma> \<turnstile> gi_uniform_operator b : pp_unary_ty"
  using typed_pp_negation_operator[where \<Gamma>=\<Gamma>]
    typed_pp_identity_operator[where \<Gamma>=\<Gamma>]
  unfolding gi_uniform_operator_def
  by (cases b; simp)

lemma gi_uniform_literal_type:
  "Prop # \<Gamma> \<turnstile> gi_uniform_literal b : Prop"
  unfolding gi_uniform_literal_def
  by (cases b; simp only: if_True if_False; intro has_type.Neg typed_var0)

lemma gi_uniform_builder_type:
  "\<Gamma> \<turnstile> gi_uniform_builder b : pp_unary_ty \<rightarrow>\<^sub>o Prop"
  unfolding gi_uniform_builder_def
  by (rule has_type.Lam, rule gi_uniform_test_type, rule typed_var0)

lemma gi_uniform_builder_logical:
  "pp_logical_vocabulary (gi_uniform_builder b)"
  by (cases b; simp add: pp_logical_vocabulary_def gi_uniform_builder_def
    gi_uniform_test_def pp_truth_flipping_def pp_truth_preserving_def shift_def)

lemma gi_uniform_builder_beta:
  "compatible_step beta_contract (App (gi_uniform_builder b) Z) (gi_uniform_test b Z)"
proof (rule compatible_step.root)
  have raw: "beta_contract (App (Lam pp_unary_ty (gi_uniform_test b (Var 0))) Z)
    (subst0 Z (gi_uniform_test b (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract (App (gi_uniform_builder b) Z) (gi_uniform_test b Z)"
    using raw by (cases b; simp add: gi_uniform_builder_def gi_uniform_test_def subst0_def)
qed

lemma gi_uniform_builder_equality:
  assumes zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App (gi_uniform_builder b) Z) (gi_uniform_test b Z)"
proof -
  have at: "\<Gamma> \<turnstile> App (gi_uniform_builder b) Z : Prop"
    by (rule has_type.App[OF gi_uniform_builder_type zt])
  have bt: "\<Gamma> \<turnstile> gi_uniform_test b Z : Prop"
    by (rule gi_uniform_test_type[OF zt])
  show ?thesis
    by (rule CEV_zeroary_equivalence[OF at bt CEV_beta_step[OF at bt gi_uniform_builder_beta]])
qed

lemma gi_uniform_test_pure_from:
  assumes stock: "pp_T1_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop (gi_uniform_test b Z)"
proof -
  have member: "pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop) (gi_uniform_builder b) \<in> T"
    using pp_T1_purity_axiom[OF gi_uniform_builder_type gi_uniform_builder_logical] stock by blast
  have bp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop) (gi_uniform_builder b)"
    by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom[OF member],
      rule typed_pp_pure[OF gi_uniform_builder_type])
  have closure: "pp_application_closure pp_unary_ty Prop \<in> T"
    using pp_T1_application_closure_axiom stock by blast
  have ap: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure Prop (App (gi_uniform_builder b) Z)"
    by (rule pp_axiom_application_closed_from[OF closure gi_uniform_builder_type zt bp pure])
  have eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (gi_uniform_builder b) Z) (gi_uniform_test b Z)"
    by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base,
      rule gi_uniform_builder_equality[OF zt])
  show ?thesis by (rule CEV_axiom_from_pure_eq_transport[OF
    has_type.App[OF gi_uniform_builder_type zt] gi_uniform_test_type[OF zt] ap eq])
qed

subsection \<open>The boxed test matches unary Intensionality by two beta steps\<close>

lemma gi_uniform_operator_shift:
  "shift (gi_uniform_operator b) = gi_uniform_operator b"
  by (cases b; simp add: gi_uniform_operator_def pp_negation_operator_def shift_def)

lemma gi_uniform_operator_beta:
  "beta_contract (App (gi_uniform_operator b) (Var 0)) (gi_uniform_literal b)"
proof -
  have raw: "beta_contract (App (Lam Prop (gi_uniform_literal b)) (Var 0))
    (subst0 (Var 0) (gi_uniform_literal b))" by (rule beta_contract.beta)
  show ?thesis using raw
    by (cases b; simp add: gi_uniform_operator_def gi_uniform_literal_def
      pp_negation_operator_def pp_identity_operator_def subst0_def)
qed

lemma gi_uniform_test_unfold:
  "gi_uniform_test b Z = Forall Prop
    (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o gi_uniform_literal b)"
  by (cases b; simp add: gi_uniform_test_def gi_uniform_literal_def
    pp_truth_preserving_def pp_truth_flipping_def)

lemma gi_uniform_box_intens_test:
  assumes zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    ((\<box>\<^sub>o (intens_condition Prop Z (gi_uniform_operator b)))
      \<longleftrightarrow>\<^sub>o (\<box>\<^sub>o (gi_uniform_test b Z)))"
proof -
  let ?z = "App (shift Z) (Var 0)"
  let ?n = "App (gi_uniform_operator b) (Var 0)"
  let ?r = "gi_uniform_literal b"
  let ?a = "Forall Prop (Conj (Imp ?z ?n) (Imp ?n ?z))"
  let ?m = "Forall Prop (Conj (Imp ?z ?r) (Imp ?n ?z))"
  let ?c = "Forall Prop (Conj (Imp ?z ?r) (Imp ?r ?z))"
  have zs: "Prop # \<Gamma> \<turnstile> ?z : Prop"
    using zt unfolding pp_unary_ty_def by (rule typed_shift_app)
  have nt: "Prop # \<Gamma> \<turnstile> ?n : Prop"
    using gi_uniform_operator_type[where \<Gamma>="Prop # \<Gamma>" and b=b]
      typed_var0[where \<sigma>=Prop and \<Gamma>=\<Gamma>]
    unfolding pp_unary_ty_def by (rule has_type.App)
  have rt: "Prop # \<Gamma> \<turnstile> ?r : Prop" by (rule gi_uniform_literal_type)
  have at: "\<Gamma> \<turnstile> ?a : Prop"
    by (intro has_type.Forall has_type.Conj has_type.Imp; (rule zs | rule nt))
  have mt: "\<Gamma> \<turnstile> ?m : Prop"
    by (intro has_type.Forall has_type.Conj has_type.Imp; (rule zs | rule nt | rule rt))
  have ct: "\<Gamma> \<turnstile> ?c : Prop"
    by (intro has_type.Forall has_type.Conj has_type.Imp; (rule zs | rule rt))
  have first: "compatible_step beta_contract (\<box>\<^sub>o ?a) (\<box>\<^sub>o ?m)"
    unfolding ObjBox_def
    by (rule compatible_step.Eq_left, rule compatible_step.Forall_body,
      rule compatible_step.Conj_left, rule compatible_step.Imp_right,
      rule compatible_step.root, rule gi_uniform_operator_beta)
  have second: "compatible_step beta_contract (\<box>\<^sub>o ?m) (\<box>\<^sub>o ?c)"
    unfolding ObjBox_def
    by (rule compatible_step.Eq_left, rule compatible_step.Forall_body,
      rule compatible_step.Conj_right, rule compatible_step.Imp_left,
      rule compatible_step.root, rule gi_uniform_operator_beta)
  have result: "\<Gamma> \<turnstile>\<^sub>CEV
    ((\<box>\<^sub>o ?a) \<longleftrightarrow>\<^sub>o (\<box>\<^sub>o ?c))"
    by (rule CEV_biconditional_trans[OF typed_ObjBox[OF at] typed_ObjBox[OF mt]
      typed_ObjBox[OF ct] CEV_beta_step[OF typed_ObjBox[OF at] typed_ObjBox[OF mt] first]
      CEV_beta_step[OF typed_ObjBox[OF mt] typed_ObjBox[OF ct] second]])
  show ?thesis using result
    by (simp only: intens_condition_def gi_uniform_operator_shift gi_uniform_test_unfold)
qed

lemma gi_uniform_branch_identity_from:
  assumes stock: "pp_T1_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
    and test: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_uniform_test b Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty Z (gi_uniform_operator b)"
proof -
  have tt: "\<Gamma> \<turnstile> gi_uniform_test b Z : Prop" by (rule gi_uniform_test_type[OF zt])
  have ex: "pp_zeroary_exhaustion \<in> T"
    using stock pp_T1_zeroary_exhaustion_axiom by blast
  have exrule: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp (pp_pure Prop (gi_uniform_test b Z))
      (Imp (gi_uniform_test b Z) (\<box>\<^sub>o (gi_uniform_test b Z)))"
    by (rule CEV_axiom_from.Theorem, rule pp_axiom_zeroary_exhaustion_imp[OF ex tt])
  have bt: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (gi_uniform_test b Z)"
    by (rule CEV_axiom_from.MP[OF test CEV_axiom_from.MP[OF
      gi_uniform_test_pure_from[OF stock zt pure] exrule]])
  have equiv: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    ((\<box>\<^sub>o (intens_condition Prop Z (gi_uniform_operator b)))
      \<longleftrightarrow>\<^sub>o (\<box>\<^sub>o (gi_uniform_test b Z)))"
    by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base,
      rule gi_uniform_box_intens_test[OF zt])
  have boxed: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    \<box>\<^sub>o (intens_condition Prop Z (gi_uniform_operator b))"
    by (rule CEV_axiom_from.MP[OF bt CEV_axiom_from_conj_right[OF equiv]])
  have intens: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp (\<box>\<^sub>o (intens_condition Prop Z (gi_uniform_operator b)))
      (Eq pp_unary_ty Z (gi_uniform_operator b))"
    using CEV_unary_intensionality[OF zt[unfolded pp_unary_ty_def]
      gi_uniform_operator_type[unfolded pp_unary_ty_def]]
    unfolding pp_unary_ty_def by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis by (rule CEV_axiom_from.MP[OF boxed intens])
qed

subsection \<open>Assemble both directions of the Inv biconditional\<close>

lemma gi_TU_Exhaustion_group_classification:
  assumes stock: "pp_T1_axioms \<subseteq> T" and tu: "pp_TU \<in> T"
    and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_group_member Z)
    (Disj (Eq pp_unary_ty Z pp_identity_operator) (Eq pp_unary_ty Z pp_negation_operator))"
proof -
  let ?g = "pp_group_member Z"
  let ?p = "pp_truth_preserving Z"
  let ?f = "pp_truth_flipping Z"
  let ?i = "Eq pp_unary_ty Z pp_identity_operator"
  let ?n = "Eq pp_unary_ty Z pp_negation_operator"
  let ?d = "Disj ?i ?n"
  have gt: "\<Gamma> \<turnstile> ?g : Prop" by (rule typed_pp_group_member[OF zt])
  have pt: "\<Gamma> \<turnstile> ?p : Prop" by (rule typed_pp_truth_preserving[OF zt])
  have ft: "\<Gamma> \<turnstile> ?f : Prop" by (rule typed_pp_truth_flipping[OF zt])
  have it: "\<Gamma> \<turnstile> ?i : Prop" by (rule has_type.Eq[OF zt typed_pp_identity_operator])
  have nt: "\<Gamma> \<turnstile> ?n : Prop" by (rule has_type.Eq[OF zt typed_pp_negation_operator])
  have dt: "\<Gamma> \<turnstile> ?d : Prop" by (rule has_type.Disj[OF it nt])
  have group: "\<Gamma> ; T ; {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?g"
    by (rule CEV_axiom_from.Assumption; (simp | rule gt))
  have pure: "\<Gamma> ; T ; {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
    using group unfolding pp_group_member_def by (rule CEV_axiom_from_conj_left)
  have uniform: "\<Gamma> ; T ; {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj ?p ?f"
    by (rule CEV_axiom_from.MP[OF group CEV_axiom_from.Theorem[OF CEV_axiom_TU_instance[OF tu zt]]])
  have left: "\<Gamma> ; T ; insert ?p {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?d"
  proof -
    have pure': "\<Gamma> ; T ; insert ?p {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
      by (rule CEV_axiom_from_mono[OF pure]; blast)
    have test: "\<Gamma> ; T ; insert ?p {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_uniform_test False Z"
      by (simp only: gi_uniform_test_def if_False;
        rule CEV_axiom_from.Assumption; (simp | rule pt))
    have eq: "\<Gamma> ; T ; insert ?p {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?i"
      using gi_uniform_branch_identity_from[OF stock zt pure' test]
      by (simp only: gi_uniform_operator_def if_False)
    show ?thesis by (rule CEV_axiom_from_disj_left_intro[OF it nt eq])
  qed
  have right: "\<Gamma> ; T ; insert ?f {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?d"
  proof -
    have pure': "\<Gamma> ; T ; insert ?f {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
      by (rule CEV_axiom_from_mono[OF pure]; blast)
    have test: "\<Gamma> ; T ; insert ?f {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_uniform_test True Z"
      by (simp only: gi_uniform_test_def if_True;
        rule CEV_axiom_from.Assumption; (simp | rule ft))
    have eq: "\<Gamma> ; T ; insert ?f {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?n"
      using gi_uniform_branch_identity_from[OF stock zt pure' test]
      by (simp only: gi_uniform_operator_def if_True)
    show ?thesis by (rule CEV_axiom_from_disj_right_intro[OF it nt eq])
  qed
  have conclusion: "\<Gamma> ; T ; {?g} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?d"
    by (rule CEV_axiom_from_T5_disj_cases[OF pt ft dt uniform left right])
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF gt conclusion])
qed

lemma gi_standard_operator_group_from:
  assumes stock: "pp_T1_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty Z (gi_uniform_operator b)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
proof -
  have member: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_group_member (gi_uniform_operator b)"
    using pp_identity_operator_group_member_T1[OF stock, where \<Gamma>=\<Gamma>]
      pp_negation_operator_group_member_T1[OF stock, where \<Gamma>=\<Gamma>]
    unfolding gi_uniform_operator_def by (cases b; simp)
  have reverse: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty (gi_uniform_operator b) Z"
    by (rule CEV_axiom_from_eq_sym[OF zt gi_uniform_operator_type eq])
  show ?thesis by (rule CEV_axiom_from_group_member_transport[OF gi_uniform_operator_type zt
    reverse CEV_axiom_from.Theorem[OF member]])
qed

lemma gi_standard_operator_classification_converse:
  assumes stock: "pp_T1_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp
    (Disj (Eq pp_unary_ty Z pp_identity_operator) (Eq pp_unary_ty Z pp_negation_operator))
    (pp_group_member Z)"
proof -
  let ?i = "Eq pp_unary_ty Z pp_identity_operator"
  let ?n = "Eq pp_unary_ty Z pp_negation_operator"
  let ?d = "Disj ?i ?n"
  have it: "\<Gamma> \<turnstile> ?i : Prop" by (rule has_type.Eq[OF zt typed_pp_identity_operator])
  have nt: "\<Gamma> \<turnstile> ?n : Prop" by (rule has_type.Eq[OF zt typed_pp_negation_operator])
  have dt: "\<Gamma> \<turnstile> ?d : Prop" by (rule has_type.Disj[OF it nt])
  have gt: "\<Gamma> \<turnstile> pp_group_member Z : Prop" by (rule typed_pp_group_member[OF zt])
  have disj: "\<Gamma> ; T ; {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?d"
    by (rule CEV_axiom_from.Assumption; (simp | rule dt))
  have left: "\<Gamma> ; T ; insert ?i {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
  proof (rule gi_standard_operator_group_from[OF stock zt, where b=False])
    show "\<Gamma> ; T ; insert ?i {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty Z (gi_uniform_operator False)"
      by (simp only: gi_uniform_operator_def if_False;
        rule CEV_axiom_from.Assumption; (simp | rule it))
  qed
  have right: "\<Gamma> ; T ; insert ?n {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
  proof (rule gi_standard_operator_group_from[OF stock zt, where b=True])
    show "\<Gamma> ; T ; insert ?n {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty Z (gi_uniform_operator True)"
      by (simp only: gi_uniform_operator_def if_True;
        rule CEV_axiom_from.Assumption; (simp | rule nt))
  qed
  have result: "\<Gamma> ; T ; {?d} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    by (rule CEV_axiom_from_T5_disj_cases[OF it nt gt disj left right])
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF dt result])
qed

theorem gi_CEV_TU_Exhaustion_implies_Inv:
  assumes stock: "pp_T1_axioms \<subseteq> T" and tu: "pp_TU \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
proof -
  let ?Q = "pp_group_member (Var 0) \<longleftrightarrow>\<^sub>o
    Disj (Eq pp_unary_ty (Var 0) pp_identity_operator)
      (Eq pp_unary_ty (Var 0) pp_negation_operator)"
  have zt: "[pp_unary_ty] \<turnstile> Var 0 : pp_unary_ty" by (rule typed_var0)
  have forward: "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_group_member (Var 0))
    (Disj (Eq pp_unary_ty (Var 0) pp_identity_operator) (Eq pp_unary_ty (Var 0) pp_negation_operator))"
    by (rule gi_TU_Exhaustion_group_classification[OF stock tu zt])
  have backward: "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp
    (Disj (Eq pp_unary_ty (Var 0) pp_identity_operator) (Eq pp_unary_ty (Var 0) pp_negation_operator))
    (pp_group_member (Var 0))"
    by (rule gi_standard_operator_classification_converse[OF stock zt])
  have body: "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    by (rule CEV_axiom_conj_intro[OF forward backward])
  have qt: "[pp_unary_ty] \<turnstile> ?Q : Prop" by (rule CEV_axiom_proves_formula[OF body])
  show ?thesis unfolding pp_Inv_def
    by (rule CEV_axiom_generalize_theorem[OF qt body])
qed

corollary gi_CEV_TU_Exhaustion_exact_stock:
  "[] ; insert pp_TU pp_T1_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
  by (rule gi_CEV_TU_Exhaustion_implies_Inv; auto)

section \<open>Transfer over the native T1 background\<close>

text \<open>
  Logical purity, application closure and zeroary Exhaustion are the
  independently written native T1 stock. TU and Inv remain explicitly
  translated formulas: this theorem does not claim independent native
  definitions of those two principles, or any derivation of RS.
\<close>

lemma gi_TU_T1_axioms_closed:
  "A \<in> insert pp_TU pp_T1_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  by (auto intro: typed_pp_TU gi_T1_axioms_closed)

lemma gi_TU_T1_native_stock_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> insert (gi_to_book G [] k pp_TU) (gb_T1_axioms G)"
  shows "book_theory_formula gb_signature G A"
proof -
  have tu: "book_theory_formula gb_signature G (gi_to_book G [] k pp_TU)"
    by (rule gi_to_book_language[OF rich typed_pp_TU _ gi_TU_admitted[OF names]]; simp)
  show ?thesis using member
    by (auto intro: tu gb_T1_axioms_language[OF rich])
qed

lemma gi_TU_T1_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> insert pp_TU pp_T1_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (insert (gi_to_book G [] k pp_TU) (gb_T1_axioms G)) (gi_to_book G [] k A)"
proof (cases "A = pp_TU")
  case True
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k pp_TU)"
    by (rule gi_to_book_language[OF rich typed_pp_TU _ gi_constants_universal]; simp)
  show ?thesis unfolding True
    by (rule goodman_book_proves.Axiom[OF _ language]; simp)
next
  case False
  have original: "A \<in> pp_T1_axioms" using member False by blast
  show ?thesis
    by (rule gi_T1_axiom_from_native[OF rich names _ original]; auto)
qed

theorem gi_TU_Exhaustion_implies_Inv_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (insert (gi_to_book G [] k pp_TU) (gb_T1_axioms G)) (gi_to_book G [] k pp_Inv)"
proof -
  have original: "[] ; insert pp_TU pp_T1_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
    by (rule gi_CEV_TU_Exhaustion_exact_stock)
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G
    (insert (gi_to_book G [] k pp_TU) (gb_T1_axioms G)) (gi_to_book G [] k pp_Inv)"
    by (rule gi_native_package_preservation[OF rich original gi_TU_T1_axioms_closed
      gi_TU_T1_axiom_from_native[OF rich names]]; simp)
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich original _
    gi_Inv_admitted[OF names] universal gi_TU_T1_native_stock_language[OF rich names]]; simp)
qed

end
