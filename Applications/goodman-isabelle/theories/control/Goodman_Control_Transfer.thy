theory Goodman_Control_Transfer
  imports Goodman_Legacy_Control_Range.Bacon_PP_Control_Range
    Goodman_Integration_Individual.Goodman_T45_Transfer
begin

section \<open>Jp = fun′(p), Sp = (p ↔ Jp), E = ∃q.fun′(Sq)\<close>

definition gb_control_axioms where
  "gb_control_axioms G = insert (gb_zeroary_exhaustion G) (gb_T6_core G)"

abbreviation gi_control_source where
  "gi_control_source \<equiv> insert pp_zeroary_exhaustion pp_T6_core_PP_axioms"

lemma gi_control_source_closed:
  "A \<in> gi_control_source \<Longrightarrow> [] \<turnstile> A : Prop"
  by (auto intro: typed_pp_zeroary_exhaustion gi_T6_core_closed)

lemma gb_control_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_control_axioms G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_control_axioms_def by (auto intro: gb_zeroary_exhaustion_language gb_T6_core_language)

lemma gi_control_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> gi_control_source"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_control_axioms G) (gi_to_book G [] k A)"
proof (cases "A = pp_zeroary_exhaustion")
  case True
  show ?thesis by (simp only: True; rule gi_zeroary_exhaustion_from_native[OF rich names];
    simp add: gb_control_axioms_def)
next
  case False
  have old: "A \<in> pp_T6_core_PP_axioms" using member False by simp
  have native: "gi_to_book G [] k A \<in> gb_T6_core G" using gi_T6_core_inclusion[OF rich names] old by blast
  have stock: "gi_to_book G [] k A \<in> gb_control_axioms G" using native unfolding gb_control_axioms_def by simp
  show ?thesis by (rule goodman_book_proves.Axiom[OF stock
    gi_gb_universal_language[OF gb_T6_core_language[OF rich native]]])
qed

theorem gi_control_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_control_axioms G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_control_source_closed
      gi_control_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted universal
    gb_control_axioms_language[OF rich]])
qed

lemma gi_control_J_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_fun_prime_classifier"
  by (simp add: pp_fun_prime_classifier_def gi_T2_fun_prime_admitted)

lemma gi_control_S_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_fun_prime_control"
  by (simp add: pp_fun_prime_control_def gi_control_J_admitted)

lemma gi_control_square_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_control_square"
  by (simp add: pp_control_square_def pp_compose_def gi_control_S_admitted shift_def gi_constants_rename)

lemma gi_control_E_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_control_range_witness"
  by (simp add: pp_control_range_witness_def gi_T2_fun_prime_admitted gi_control_S_admitted)

text \<open>
  The first results use only the PP purity/application core. Exhaustion is
  not silently added to these purity and pointwise nonuniformity claims.
\<close>

theorem gi_control_classifier_pure:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [] k (pp_pure pp_unary_ty pp_fun_prime_classifier))"
  by (rule gi_T2_PP_native_preservation[OF rich names CEV_fun_prime_classifier_pure[OF subset_refl]];
    use names in \<open>simp add: pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def gi_control_J_admitted[OF names]\<close>)

theorem gi_control_operator_pure:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [] k (pp_pure pp_unary_ty pp_fun_prime_control))"
  by (rule gi_T2_PP_native_preservation[OF rich names CEV_fun_prime_control_pure[OF subset_refl]];
    use names in \<open>simp add: pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def gi_control_S_admitted[OF names]\<close>)

theorem gi_control_J_squared_false:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and pt: "\<Gamma> \<turnstile> p : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_classifier p)) ObjFalse))"
  by (rule gi_T2_PP_native_preservation[OF rich names CEV_J_squared_eq_falsity[OF subset_refl pt] chart distinct];
    simp add: gi_control_J_admitted[OF names] admitted ObjFalse_def ObjTrue_def)

theorem gi_control_nonuniform_at_fun_prime:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and pt: "\<Gamma> \<turnstile> p : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime p)
      (Neg (Disj (pp_truth_preserving pp_fun_prime_control) (pp_truth_flipping pp_fun_prime_control)))))"
  by (rule gi_T2_PP_native_preservation[OF rich names CEV_control_not_uniform_at_fun_prime[OF subset_refl pt] chart distinct];
    simp add: gi_T2_fun_prime_admitted[OF names admitted] pp_truth_preserving_def pp_truth_flipping_def
      gi_control_S_admitted[OF names] shift_def gi_constants_rename)

section \<open>Iteration and range use the PP core plus zeroary Exhaustion\<close>

theorem gi_control_cube:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G [] k (Eq pp_unary_ty (pp_compose pp_control_square pp_fun_prime_control) pp_fun_prime_control))"
proof -
  have source: "[] ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ Eq pp_unary_ty (pp_compose pp_control_square pp_fun_prime_control) pp_fun_prime_control"
    by (rule CEV_control_cube_eq_control[OF subset_refl])
  show ?thesis by (rule gi_control_native_preservation[OF rich names source];
    simp add: gi_control_square_admitted[OF names] gi_control_S_admitted[OF names]
      gi_control_E_admitted[OF names] gi_T2_fun_prime_admitted[OF names] pp_exists_fun_prime_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def shift_def gi_constants_rename)
qed

theorem gi_control_square_idempotent:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G [] k (Eq pp_unary_ty (pp_compose pp_control_square pp_control_square) pp_control_square))"
proof -
  have source: "[] ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ Eq pp_unary_ty (pp_compose pp_control_square pp_control_square) pp_control_square"
    by (rule CEV_control_square_idempotent[OF subset_refl])
  show ?thesis by (rule gi_control_native_preservation[OF rich names source];
    simp add: gi_control_square_admitted[OF names] gi_control_S_admitted[OF names]
      gi_control_E_admitted[OF names] gi_T2_fun_prime_admitted[OF names] pp_exists_fun_prime_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def shift_def gi_constants_rename)
qed

theorem gi_control_range_implies_identity:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G [] k (Imp pp_control_range_witness (Eq pp_unary_ty pp_control_square pp_identity_operator)))"
proof -
  have source: "[] ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_control_range_witness (Eq pp_unary_ty pp_control_square pp_identity_operator)"
    by (rule CEV_control_range_witness_implies_square_identity[OF subset_refl])
  show ?thesis by (rule gi_control_native_preservation[OF rich names source];
    simp add: gi_control_square_admitted[OF names] gi_control_S_admitted[OF names]
      gi_control_E_admitted[OF names] gi_T2_fun_prime_admitted[OF names] pp_exists_fun_prime_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def shift_def gi_constants_rename)
qed

theorem gi_control_range_iff_identity:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G [] k (Imp pp_exists_fun_prime (Conj (Imp pp_control_range_witness (Eq pp_unary_ty pp_control_square pp_identity_operator)) (Imp (Eq pp_unary_ty pp_control_square pp_identity_operator) pp_control_range_witness))))"
proof -
  have source: "[] ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime (Conj (Imp pp_control_range_witness (Eq pp_unary_ty pp_control_square pp_identity_operator)) (Imp (Eq pp_unary_ty pp_control_square pp_identity_operator) pp_control_range_witness))"
    by (rule CEV_control_range_witness_iff_square_identity[OF subset_refl])
  show ?thesis by (rule gi_control_native_preservation[OF rich names source];
    simp add: gi_control_square_admitted[OF names] gi_control_S_admitted[OF names]
      gi_control_E_admitted[OF names] gi_T2_fun_prime_admitted[OF names] pp_exists_fun_prime_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def shift_def gi_constants_rename)
qed

theorem gi_control_no_range_negative_square:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G [] k (Imp pp_exists_fun_prime (Imp (Neg pp_control_range_witness) (Eq pp_unary_ty pp_control_square (pp_compose pp_negation_operator pp_fun_prime_control)))))"
proof -
  have source: "[] ; gi_control_source \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime (Imp (Neg pp_control_range_witness) (Eq pp_unary_ty pp_control_square (pp_compose pp_negation_operator pp_fun_prime_control)))"
    by (rule CEV_control_no_range_witness_implies_negative_square[OF subset_refl])
  show ?thesis by (rule gi_control_native_preservation[OF rich names source];
    simp add: gi_control_square_admitted[OF names] gi_control_S_admitted[OF names]
      gi_control_E_admitted[OF names] gi_T2_fun_prime_admitted[OF names] pp_exists_fun_prime_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def shift_def gi_constants_rename)
qed

theorem gi_control_fun_prime_heredity:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and pt: "\<Gamma> \<turnstile> p : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G ns k (Imp (ObjDiamond (pp_fun_prime p)) (pp_fun_prime p)))"
  by (rule gi_control_native_preservation[OF rich names CEV_fun_prime_heredity_PP_exhaustion[OF subset_refl pt] chart distinct];
    simp add: gi_T2_fun_prime_admitted gi_control_S_admitted[OF names] names admitted
      ObjDiamond_def ObjBox_def ObjTrue_def)

theorem gi_control_reflects_fun_prime:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and pt: "\<Gamma> \<turnstile> p : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_control_axioms G)
    (gi_to_book G ns k (Imp (pp_fun_prime (App pp_fun_prime_control p)) (pp_fun_prime p)))"
  by (rule gi_control_native_preservation[OF rich names CEV_control_reflects_fun_prime_PP_exhaustion[OF subset_refl pt] chart distinct];
    simp add: gi_T2_fun_prime_admitted gi_control_S_admitted[OF names] names admitted
      ObjDiamond_def ObjBox_def ObjTrue_def)

text \<open>
  In particular S³=S and (S²)²=S². The range clauses retain their displayed
  antecedents: E suffices for S²=id; the converse and the negative-square
  alternative retain ∃fun′. None proves E, ¬E, Recombination without the
  stated Exhaustion, or consistency. Targets are explicitly translated
  object-language formulas; native stocks have been independently matched.
\<close>

end
