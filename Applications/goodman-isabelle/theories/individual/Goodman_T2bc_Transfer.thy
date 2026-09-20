theory Goodman_T2bc_Transfer
  imports Goodman_T1_Transfer
begin

section \<open>T2b and T2c use only logical purity and application closure\<close>

text \<open>
  Let S contain purity of every closed logical term and application closure.
  T2b says that fun′(r) implies r ≠ ⊤, r ≠ ⊥, and r ≠ ¬r. T2c says that
  fun′(r) implies ∀p.(Pure(p) → ◇(r = p)). We transfer both results over S,
  without PP, Exhaustion, Recombination, Persistence, or an existence axiom.
  In particular the displayed fun′ antecedents are not discharged.
\<close>

definition gb_T2_min_axioms where
  "gb_T2_min_axioms G = gb_purity_schema G \<union> gb_application_schema G"

lemma gi_T2_min_axioms_closed:
  "A \<in> pp_T2_min_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T2_min_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed)

lemma gb_T2_min_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T2_min_axioms G \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gb_T2_min_axioms_def gb_application_schema_def
  by (auto intro: gb_purity_schema_language gb_application_closure_language)

lemma gb_T2_min_axioms_closed:
  "A \<in> gb_T2_min_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_T2_min_axioms_def gb_application_schema_def
  by (auto simp: gb_purity_schema_closed gb_basic_axioms_closed)

lemma gi_T2_min_stock_inclusion:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_T2_min_axioms \<subseteq> gb_T2_min_axioms G"
  unfolding pp_T2_min_axioms_def gb_T2_min_axioms_def image_Un
  using gi_purity_schema_inclusion gi_application_schema_equality by blast

lemma gi_T2_min_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> pp_T2_min_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_T2_min_axioms G) (gi_to_book G [] k A)"
proof -
  have native: "gi_to_book G [] k A \<in> gb_T2_min_axioms G"
    using gi_T2_min_stock_inclusion[OF rich names] member by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_gb_universal_language[OF gb_T2_min_axioms_language[OF rich native]])
  show ?thesis by (rule goodman_book_proves.Axiom[OF native language])
qed

theorem gi_T2_min_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T2_min_axioms G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_T2_min_axioms_closed
      gi_T2_min_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    universal gb_T2_min_axioms_language[OF rich]])
qed

section \<open>Signature guards for the individual conclusions\<close>

lemma gi_T2_fun_prime_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature p \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_fun_prime p)"
  by (simp add: pp_fun_prime_def pp_pure_def pp_Pure_def gi_goodman_names_def
    gb_signature_def shift_by_def gi_constants_rename)

lemma gi_T2b_nontriviality_admitted:
  "gi_constants_admitted k gb_signature p \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T2b_nontriviality p)"
  by (simp add: pp_T2b_nontriviality_def ObjTrue_def ObjFalse_def)

lemma gi_T2c_parameter_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature p \<Longrightarrow>
    gi_constants_admitted k gb_signature
      (Imp (pp_fun_prime r) (Imp (pp_pure Prop p) (ObjDiamond (Eq Prop r p))))"
  by (simp add: gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def)

lemma gi_T2c_quantified_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r)
      (Forall Prop (Imp (pp_pure Prop (Var 0))
        (ObjDiamond (Eq Prop (shift r) (Var 0))))))"
  by (simp add: gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def
    shift_def gi_constants_rename)

section \<open>Individually named transfers, with all parameter guards\<close>

theorem gi_T2b_nontriviality_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> p : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (Imp (pp_fun_prime p) (pp_T2b_nontriviality p)))"
proof (rule gi_T2_min_native_preservation[OF rich names
    CEV_Goodman_T2b[OF subset_refl typed] chart distinct])
  show "gi_constants_admitted k gb_signature (Imp (pp_fun_prime p) (pp_T2b_nontriviality p))"
    using gi_T2_fun_prime_admitted[OF names admitted] gi_T2b_nontriviality_admitted[OF admitted] by simp
qed

theorem gi_T2b_truth_not_fun_prime_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [] k (Neg (pp_fun_prime ObjTrue)))"
proof (rule gi_T2_min_native_preservation[OF rich names
    CEV_not_fun_prime_ObjTrue[OF subset_refl]])
  show "map G [] = []" by simp
  show "distinct []" by simp
  show "gi_constants_admitted k gb_signature (Neg (pp_fun_prime ObjTrue))"
    by (simp add: gi_T2_fun_prime_admitted[OF names] ObjTrue_def)
qed

theorem gi_T2b_falsity_not_fun_prime_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [] k (Neg (pp_fun_prime ObjFalse)))"
proof (rule gi_T2_min_native_preservation[OF rich names
    CEV_not_fun_prime_ObjFalse[OF subset_refl]])
  show "map G [] = []" by simp
  show "distinct []" by simp
  show "gi_constants_admitted k gb_signature (Neg (pp_fun_prime ObjFalse))"
    by (simp add: gi_T2_fun_prime_admitted[OF names] ObjFalse_def ObjTrue_def)
qed

theorem gi_T2c_parameter_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and pt: "\<Gamma> \<turnstile> p : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and pa: "gi_constants_admitted k gb_signature p"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (Imp (pp_fun_prime r)
      (Imp (pp_pure Prop p) (ObjDiamond (Eq Prop r p)))))"
  by (rule gi_T2_min_native_preservation[OF rich names
    CEV_Goodman_T2c_parameter[OF subset_refl rt pt] chart distinct
    gi_T2c_parameter_admitted[OF names ra pa]])

theorem gi_T2c_quantified_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (Imp (pp_fun_prime r)
      (Forall Prop (Imp (pp_pure Prop (Var 0))
        (ObjDiamond (Eq Prop (shift r) (Var 0)))))))"
  by (rule gi_T2_min_native_preservation[OF rich names
    CEV_Goodman_T2c[OF subset_refl rt] chart distinct gi_T2c_quantified_admitted[OF names ra]])

section \<open>Independent named formulas, with explicit fresh operator binders\<close>

definition gb_T2_fun_prime_at where
  "gb_T2_fun_prime_at G = gb_fun_prime_with_names G
    (gb_y G Prop gb_unary) (gb_z G Prop gb_unary gb_unary) (NVar (gb_x G Prop))"

lemma gb_T2_fun_prime_binders:
  "sg_rich G \<Longrightarrow>
    distinct [gb_x G Prop, gb_y G Prop gb_unary, gb_z G Prop gb_unary gb_unary]"
  by (rule gb_names_distinct; assumption)

lemma gb_T2_fun_prime_at_language:
  "sg_rich G \<Longrightarrow> book_theory_formula gb_signature G (gb_T2_fun_prime_at G)"
  unfolding gb_T2_fun_prime_at_def
  by (intro gb_fun_prime_with_names_language gb_names_type gb_x_language; assumption)

lemma gb_T2_fun_prime_at_fv:
  assumes rich: "sg_rich G"
  shows "named_fv (gb_T2_fun_prime_at G) = {gb_x G Prop}"
  using gb_T2_fun_prime_binders[OF rich]
  by (auto simp: gb_T2_fun_prime_at_def gb_fun_prime_with_names_fv)

lemma gi_T2_fun_prime_var_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k (pp_fun_prime (Var 0)) = gb_T2_fun_prime_at G"
  by (simp add: pp_fun_prime_def gb_T2_fun_prime_at_def gb_fun_prime_with_names_def
    pp_unary_ty_def gi_pure_translation gb_y_def[symmetric] gi_gb_z_reversed Let_def
    shift_by_def shift_ren_def)

definition gb_T2b_nontriviality where
  "gb_T2b_nontriviality G = (let r = NVar (gb_x G Prop); top = gi_old_top G [gb_x G Prop] in
    book_and G (book_not G (book_leibniz G Prop r top))
      (book_and G (book_not G (book_leibniz G Prop r (book_not G top)))
        (book_not G (book_leibniz G Prop r (book_not G r)))))"

definition gb_T2b_claim where
  "gb_T2b_claim G = book_imp (gb_T2_fun_prime_at G) (gb_T2b_nontriviality G)"

lemma gi_T2b_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (pp_T2b_nontriviality (Var 0))) = gb_T2b_claim G"
  by (simp add: gb_T2b_claim_def gi_T2_fun_prime_var_translation
    pp_T2b_nontriviality_def gb_T2b_nontriviality_def ObjFalse_def gi_true_translation Let_def)

theorem gi_T2b_nontriviality:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G) (gb_T2b_claim G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [gb_x G Prop] = [Prop]" by (simp add: gb_names_type[OF rich])
  have translated: "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0)) (pp_T2b_nontriviality (Var 0))))"
    by (rule gi_T2b_nontriviality_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T2b_claim_translation[OF names])
qed

text \<open>
  The source's possibility abbreviation is ¬(¬A = ⊤₀), with ⊤₀ the explicit
  logical truth representative. We expose that definition instead of silently
  substituting a differently represented book_diamond. Likewise the truth and
  falsity in T2b above remain ⊤₀ and ¬⊤₀, rather than definitionally book_top
  and book_bottom. All equalities inside these formulas are book Leibniz identity.
\<close>

definition gb_T2_source_diamond where
  "gb_T2_source_diamond G ns A = book_not G
    (book_leibniz G Prop (book_not G A) (gi_old_top G ns))"

lemma gi_T2_diamond_translation:
  "gi_to_book G ns k (ObjDiamond A) = gb_T2_source_diamond G ns (gi_to_book G ns k A)"
  by (simp add: ObjDiamond_def ObjBox_def gb_T2_source_diamond_def gi_true_translation)

definition gb_T2c_claim where
  "gb_T2c_claim G = (let r = gb_x G Prop; p = gb_y G Prop Prop in
    book_imp (gb_T2_fun_prime_at G) (book_all G p
      (book_imp (gb_pure Prop (NVar p))
        (gb_T2_source_diamond G [p, r] (book_leibniz G Prop (NVar r) (NVar p))))))"

lemma gb_T2c_proposition_binders_distinct:
  "sg_rich G \<Longrightarrow> gb_x G Prop \<noteq> gb_y G Prop Prop"
  using gb_names_distinct[where \<sigma>=Prop and \<tau>=Prop and \<upsilon>=Prop] by auto

lemma gi_T2c_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (Forall Prop (Imp (pp_pure Prop (Var 0))
        (ObjDiamond (Eq Prop (shift (Var 0)) (Var 0)))))) = gb_T2c_claim G"
  by (simp add: gb_T2c_claim_def gi_T2_fun_prime_var_translation gi_T2_diamond_translation
    gi_pure_translation gb_y_def Let_def shift_def shift_ren_def)

theorem gi_T2c_attainment:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G) (gb_T2c_claim G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [gb_x G Prop] = [Prop]" by (simp add: gb_names_type[OF rich])
  have translated: "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (Forall Prop (Imp (pp_pure Prop (Var 0))
        (ObjDiamond (Eq Prop (shift (Var 0)) (Var 0)))))))"
    by (rule gi_T2c_quantified_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T2c_claim_translation[OF names])
qed

text \<open>
  The two final endpoints have native named conclusions with one free
  proposition name r, and no constructor-language syntax in those conclusions.
  The arbitrary-term parameter endpoints above remain explicitly translated;
  replacing their translated fun′ binder charts by arbitrary independently
  chosen fresh names requires the corresponding α-conversion argument.
  Neither endpoint derives ∃r.fun′(r), establishes consistency of its antecedent,
  or omits the antecedent. The stock S itself contains no PP axiom.
\<close>

end
