theory Goodman_T1_Transfer
  imports Goodman_Integration_Central_Stock.Goodman_Native_Fun_Prime
begin

section \<open>T1: the minimal native stock retains zeroary Exhaustion\<close>

text \<open>
  T1 uses purity of closed logical terms, application closure, and zeroary
  Exhaustion. It does not need PP, Recombination, Persistence, or a fundamental
  proposition. We keep this smaller stock instead of deriving T1 from a larger
  central package. The proofs below transfer the existing CEV+ derivations;
  they are not semantic validity arguments or new axiom declarations.
\<close>

definition gb_T1_axioms where
  "gb_T1_axioms G = gb_purity_schema G \<union> gb_application_schema G \<union>
    {gb_zeroary_exhaustion G}"

lemma gi_T1_axioms_closed:
  "A \<in> pp_T1_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T1_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed
    typed_pp_zeroary_exhaustion)

lemma gb_T1_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T1_axioms G \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gb_T1_axioms_def gb_application_schema_def
  by (auto intro: gb_purity_schema_language gb_application_closure_language
    gb_zeroary_exhaustion_language)

lemma gb_T1_axioms_closed:
  "A \<in> gb_T1_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_T1_axioms_def gb_application_schema_def
  by (auto simp: gb_purity_schema_closed gb_basic_axioms_closed gb_QLN_axioms_closed)

lemma gi_T1_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and stock: "gb_T1_axioms G \<subseteq> U" and member: "A \<in> pp_T1_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof (cases "A = pp_zeroary_exhaustion")
  case True
  have "gb_zeroary_exhaustion G \<in> U"
    using stock unfolding gb_T1_axioms_def by blast
  then show ?thesis unfolding True
    by (rule gi_zeroary_exhaustion_from_native[OF rich names])
next
  case False
  have member': "A \<in> pp_purity_schema \<union> pp_application_closure_schema"
    using member False unfolding pp_T1_axioms_def by blast
  have image: "gi_to_book G [] k A \<in> gb_purity_schema G \<union> gb_application_schema G"
    using member' gi_purity_schema_inclusion[OF rich names]
      gi_application_schema_equality[OF names, where G=G] by blast
  have native: "gi_to_book G [] k A \<in> gb_T1_axioms G"
    using image unfolding gb_T1_axioms_def by blast
  have in_U: "gi_to_book G [] k A \<in> U" using stock native by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_gb_universal_language[OF gb_T1_axioms_language[OF rich native]])
  show ?thesis by (rule goodman_book_proves.Axiom[OF in_U language])
qed

theorem gi_T1_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_T1_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T1_axioms G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T1_axioms G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_T1_axioms_closed
      gi_T1_axiom_from_native[OF rich names subset_refl] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    universal gb_T1_axioms_language[OF rich]])
qed

section \<open>Pure propositions: the individually transferred T1 theorem\<close>

lemma gi_T1_extreme_admitted:
  "gi_goodman_names k \<Longrightarrow>
    gi_constants_admitted k gb_signature pp_T1_pure_propositions_extreme"
  by (simp add: pp_T1_pure_propositions_extreme_def pp_proposition_extreme_def
    pp_pure_def pp_Pure_def ObjTrue_def ObjFalse_def gi_goodman_names_def gb_signature_def)

theorem gi_T1_pure_propositions_extreme_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T1_axioms G)
    (gi_to_book G [] k pp_T1_pure_propositions_extreme)"
  by (rule gi_T1_native_preservation[OF rich names
    CEV_Goodman_T1_pure_propositions_extreme[OF subset_refl] _ _
    gi_T1_extreme_admitted[OF names]]; simp)

text \<open>
  Here is an independent named-language statement of the same theorem,
  using the source's logical representatives ⊤₀ = ∀q.(q → q) and ¬⊤₀.
  The two representatives are NOT definitionally book_top and book_bottom.
  The existing theorem gi_goodman_truth_identity relates ⊤₀ to book_top;
  this endpoint does not silently replace either representative.
\<close>

definition gb_T1_extreme_at where
  "gb_T1_extreme_at G ns p = book_or G
    (book_leibniz G Prop p (gi_old_top G ns))
    (book_leibniz G Prop p (book_not G (gi_old_top G ns)))"

definition gb_T1_pure_propositions_extreme where
  "gb_T1_pure_propositions_extreme G = (let p = gb_x G Prop in
    book_all G p (book_imp (gb_pure Prop (NVar p))
      (gb_T1_extreme_at G [p] (NVar p))))"

lemma gi_T1_extreme_translation:
  "gi_to_book G ns k (pp_proposition_extreme p) =
    gb_T1_extreme_at G ns (gi_to_book G ns k p)"
  by (simp add: pp_proposition_extreme_def gb_T1_extreme_at_def
    ObjFalse_def gi_true_translation)

lemma gi_T1_pure_extreme_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k pp_T1_pure_propositions_extreme = gb_T1_pure_propositions_extreme G"
  by (simp add: pp_T1_pure_propositions_extreme_def gb_T1_pure_propositions_extreme_def
    gi_pure_translation gi_T1_extreme_translation gb_x_def Let_def)

theorem gi_T1_pure_propositions_extreme:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T1_axioms G) (gb_T1_pure_propositions_extreme G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis using gi_T1_pure_propositions_extreme_translated[OF rich names]
    by (simp only: gi_T1_pure_extreme_translation[OF names])
qed

section \<open>The biconditional operators are identity or negation\<close>

definition gb_T1_identity_operator where
  "gb_T1_identity_operator G ns = (let p = named_chart_fresh G ns Prop in NLam p (NVar p))"

definition gb_T1_negation_operator where
  "gb_T1_negation_operator G ns = (let p = named_chart_fresh G ns Prop in NLam p (book_not G (NVar p)))"

definition gb_T1_biconditional_operator where
  "gb_T1_biconditional_operator G ns A =
    (let a = named_chart_fresh G ns Prop; p = named_chart_fresh G (a # ns) Prop in
      NApp (NLam a (NLam p (book_and G
        (book_imp (NVar p) (NVar a)) (book_imp (NVar a) (NVar p))))) A)"

definition gb_T1_biconditional_classification where
  "gb_T1_biconditional_classification G ns A =
    book_imp (gb_pure Prop A) (book_or G
      (book_leibniz G gb_unary (gb_T1_biconditional_operator G ns A) (gb_T1_identity_operator G ns))
      (book_leibniz G gb_unary (gb_T1_biconditional_operator G ns A) (gb_T1_negation_operator G ns)))"

lemma gi_T1_identity_operator_translation:
  "gi_to_book G ns k pp_identity_operator = gb_T1_identity_operator G ns"
  by (simp add: pp_identity_operator_def gb_T1_identity_operator_def Let_def)

lemma gi_T1_negation_operator_translation:
  "gi_to_book G ns k pp_negation_operator = gb_T1_negation_operator G ns"
  by (simp add: pp_negation_operator_def gb_T1_negation_operator_def Let_def)

lemma gi_T1_biconditional_operator_translation:
  "gi_to_book G ns k (pp_biconditional_operator A) =
    gb_T1_biconditional_operator G ns (gi_to_book G ns k A)"
  by (simp add: pp_biconditional_operator_def pp_biconditional_builder_def
    gb_T1_biconditional_operator_def Let_def)

lemma gi_T1_biconditional_classification_admitted:
  assumes names: "gi_goodman_names k" and admitted: "gi_constants_admitted k gb_signature A"
  shows "gi_constants_admitted k gb_signature (Imp (pp_pure Prop A)
    (Disj (Eq pp_unary_ty (pp_biconditional_operator A) pp_identity_operator)
      (Eq pp_unary_ty (pp_biconditional_operator A) pp_negation_operator)))"
  using names admitted
  by (simp add: pp_pure_def pp_Pure_def pp_biconditional_operator_def pp_biconditional_builder_def
    pp_identity_operator_def pp_negation_operator_def gi_goodman_names_def gb_signature_def)

theorem gi_T1_biconditional_classification_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> A : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T1_axioms G)
    (gi_to_book G ns k (Imp (pp_pure Prop A)
      (Disj (Eq pp_unary_ty (pp_biconditional_operator A) pp_identity_operator)
        (Eq pp_unary_ty (pp_biconditional_operator A) pp_negation_operator))))"
  by (rule gi_T1_native_preservation[OF rich names
    CEV_Goodman_T1_biconditional_operator_classification[OF subset_refl typed]
    chart distinct gi_T1_biconditional_classification_admitted[OF names admitted]])

theorem gi_T1_biconditional_classification:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> A : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T1_axioms G)
    (gb_T1_biconditional_classification G ns (gi_to_book G ns k A))"
  using gi_T1_biconditional_classification_translated[OF assms]
  by (simp only: gi_to_book.simps gi_pure_translation[OF names]
    gi_T1_biconditional_operator_translation gi_T1_identity_operator_translation
    gi_T1_negation_operator_translation gb_T1_biconditional_classification_def pp_unary_ty_def)

section \<open>WI implies Inv over precisely the T1 stock\<close>

text \<open>
  The common stock is native, but WI and Inv are still explicitly translated
  formulas. No independent native identification of those quantified route
  principles is claimed by this theorem. WI is an additional axiom here;
  Inv is the conclusion. There is no L2, PP, or existence-of-fun′ premise.
\<close>

definition gi_T1_WI_native_stock where
  "gi_T1_WI_native_stock G k = insert (gi_to_book G [] k pp_WI) (gb_T1_axioms G)"

lemma gi_T1_WI_axioms_closed:
  "A \<in> pp_T1_WI_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T1_WI_axioms_def
  by (auto intro: gi_T1_axioms_closed typed_pp_WI)

lemma gi_T1_WI_native_stock_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> gi_T1_WI_native_stock G k"
  shows "book_theory_formula gb_signature G A"
proof -
  have wi: "book_theory_formula gb_signature G (gi_to_book G [] k pp_WI)"
    by (rule gi_to_book_language[OF rich typed_pp_WI _ gi_WI_admitted[OF names]]; simp)
  show ?thesis using member unfolding gi_T1_WI_native_stock_def
    by (auto intro: wi gb_T1_axioms_language[OF rich])
qed

lemma gi_T1_WI_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> pp_T1_WI_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gi_T1_WI_native_stock G k) (gi_to_book G [] k A)"
proof (cases "A = pp_WI")
  case True
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k pp_WI)"
    by (rule gi_to_book_language[OF rich typed_pp_WI _ gi_constants_universal]; simp)
  show ?thesis unfolding True
    by (rule goodman_book_proves.Axiom[OF _ language]; simp add: gi_T1_WI_native_stock_def)
next
  case False
  have original: "A \<in> pp_T1_axioms" using member False unfolding pp_T1_WI_axioms_def by blast
  show ?thesis by (rule gi_T1_axiom_from_native[OF rich names _ original];
    auto simp: gi_T1_WI_native_stock_def)
qed

theorem gi_T1_WI_implies_Inv_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T1_WI_native_stock G k) (gi_to_book G [] k pp_Inv)"
proof -
  have original: "[] ; pp_T1_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
    by (rule CEV_Goodman_T1_WI_collapses_to_Inv[OF subset_refl])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gi_T1_WI_native_stock G k)
    (gi_to_book G [] k pp_Inv)"
    by (rule gi_native_package_preservation[OF rich original gi_T1_WI_axioms_closed
      gi_T1_WI_axiom_from_native[OF rich names]]; simp)
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich original _ gi_Inv_admitted[OF names]
    universal gi_T1_WI_native_stock_language[OF rich names]]; simp)
qed

end
