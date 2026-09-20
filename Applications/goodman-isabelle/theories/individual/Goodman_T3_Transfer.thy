theory Goodman_T3_Transfer
  imports Goodman_T2a_Transfer
    Goodman_Integration_Central_Stock.Goodman_Native_QSS
begin

section \<open>T3: separate possible identity from repaired Heredity\<close>

text \<open>
  QSS and unary Persistence yield only possible identity of the two pure
  operators in the displayed modal argument. They do not, by that argument,
  yield actual identity. We preserve this weak conclusion separately from
  the two checked Heredity repairs: zeroary Exhaustion, or rigidity of
  identity restricted to pure unary operators. The stronger older repair
  using possible-identity-implies-identity for all unary operators is also
  retained explicitly, not conflated with pure-identity rigidity.

  None of the results below establishes that the uncorrected full-theory
  claim is false. The historical modal-abstraction counterexamples are not
  models of the complete CEV+ theory and are not replayed in this file.
\<close>

definition gi_T3_modal_source where
  "gi_T3_modal_source = {pp_QSS, pp_persistence pp_unary_ty}"

definition gb_T3_modal_axioms where
  "gb_T3_modal_axioms G = {gb_QSS G, gb_persistence G gb_unary}"

definition gb_T3_exhaustion_axioms where
  "gb_T3_exhaustion_axioms G = gb_T2_min_axioms G \<union> gb_T3_modal_axioms G \<union>
    {gb_zeroary_exhaustion G}"

lemma gi_T3_modal_source_closed:
  "A \<in> gi_T3_modal_source \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_T3_modal_source_def by (auto intro: typed_pp_QSS typed_pp_persistence)

lemma gi_T3_min_source_closed:
  "A \<in> pp_T3_min_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T3_min_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed
    typed_pp_QSS typed_pp_persistence typed_pp_zeroary_exhaustion)

lemma gb_T3_modal_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T3_modal_axioms G \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gb_T3_modal_axioms_def by (auto intro: gb_QSS_language gb_persistence_language)

lemma gb_T3_exhaustion_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T3_exhaustion_axioms G \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gb_T3_exhaustion_axioms_def
  by (auto intro: gb_T2_min_axioms_language gb_T3_modal_axioms_language gb_zeroary_exhaustion_language)

lemma gi_T3_modal_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and stock: "gb_T3_modal_axioms G \<subseteq> U" and member: "A \<in> gi_T3_modal_source"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof -
  have qss_in: "gb_QSS G \<in> U" and pers_in: "gb_persistence G gb_unary \<in> U"
    using stock unfolding gb_T3_modal_axioms_def by auto
  have qss: "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_QSS)"
    by (simp only: gi_QSS_translation[OF names];
      rule goodman_book_proves.Axiom[OF qss_in gi_gb_universal_language[OF gb_QSS_language[OF rich]]])
  have pers: "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k (pp_persistence pp_unary_ty))"
    by (rule gi_persistence_from_native[OF rich names]; use pers_in in \<open>simp only: pp_unary_ty_def\<close>)
  show ?thesis using member qss pers unfolding gi_T3_modal_source_def by auto
qed

lemma gi_T3_exhaustion_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> pp_T3_min_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_exhaustion_axioms G) (gi_to_book G [] k A)"
proof -
  have logical: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_exhaustion_axioms G)
    (gi_to_book G [] k B)" if "B \<in> pp_T2_min_axioms" for B
    by (rule goodman_book_mono[OF gi_T2_min_axiom_from_native[OF rich names that]];
      auto simp: gb_T3_exhaustion_axioms_def)
  have modal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_exhaustion_axioms G)
    (gi_to_book G [] k B)" if "B \<in> gi_T3_modal_source" for B
    by (rule gi_T3_modal_axiom_from_native[OF rich names _ that];
      auto simp: gb_T3_exhaustion_axioms_def)
  have exhaustion: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_exhaustion_axioms G)
    (gi_to_book G [] k pp_zeroary_exhaustion)"
    by (rule gi_zeroary_exhaustion_from_native[OF rich names]; simp add: gb_T3_exhaustion_axioms_def)
  show ?thesis using member logical modal exhaustion
    unfolding pp_T3_min_axioms_def pp_T2_min_axioms_def gi_T3_modal_source_def by blast
qed

section \<open>The weak modal conclusion\<close>

definition gb_T3_modal_result where
  "gb_T3_modal_result G ns r X Y =
    book_imp (gb_T2_source_diamond G ns (gb_fun Prop r))
      (book_imp (book_and G (gb_pure gb_unary X) (gb_pure gb_unary Y))
        (book_imp (book_leibniz G Prop (NApp X r) (NApp Y r))
          (gb_T2_source_diamond G ns (book_leibniz G gb_unary X Y))))"

lemma gi_T3_modal_result_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature X \<Longrightarrow> gi_constants_admitted k gb_signature Y \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (ObjDiamond (pp_fun Prop r))
      (Imp (Conj (pp_pure pp_unary_ty X) (pp_pure pp_unary_ty Y))
        (Imp (Eq Prop (App X r) (App Y r)) (ObjDiamond (Eq pp_unary_ty X Y)))))"
  by (simp add: pp_fun_def pp_Fun_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def)

theorem gi_T3_modal_core:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and xt: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and yt: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and xa: "gi_constants_admitted k gb_signature X" and ya: "gi_constants_admitted k gb_signature Y"
  shows "goodman_book_proves gb_signature G (gb_T3_modal_axioms G)
    (gb_T3_modal_result G ns (gi_to_book G ns k r) (gi_to_book G ns k X) (gi_to_book G ns k Y))"
proof -
  let ?A = "Imp (ObjDiamond (pp_fun Prop r))
    (Imp (Conj (pp_pure pp_unary_ty X) (pp_pure pp_unary_ty Y))
      (Imp (Eq Prop (App X r) (App Y r)) (ObjDiamond (Eq pp_unary_ty X Y))))"
  have source: "\<Gamma> ; gi_T3_modal_source \<turnstile>\<^sub>CEV\<^sup>+ ?A"
    by (rule CEV_T3_modal_core[OF _ _ rt xt yt]; simp add: gi_T3_modal_source_def)
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_modal_axioms G) (gi_to_book G ns k ?A)"
    by (rule gi_native_package_preservation[OF rich source gi_T3_modal_source_closed
      gi_T3_modal_axiom_from_native[OF rich names subset_refl] chart distinct])
  have restricted: "goodman_book_proves gb_signature G (gb_T3_modal_axioms G) (gi_to_book G ns k ?A)"
    by (rule gi_native_conclusion_restrict[OF rich source chart
      gi_T3_modal_result_admitted[OF names ra xa ya] universal gb_T3_modal_axioms_language[OF rich]])
  show ?thesis using restricted by (simp add: gb_T3_modal_result_def
    gi_T2_diamond_translation gi_fun_translation[OF names] gi_pure_translation[OF names] pp_unary_ty_def)
qed

section \<open>The closed native Heredity formula\<close>

definition gb_T3_heredity where
  "gb_T3_heredity G = book_all G (gb_x G Prop)
    (book_imp (gb_T2_source_diamond G [gb_x G Prop] (gb_fun Prop (NVar (gb_x G Prop))))
      (gb_T2_fun_prime_at G))"

lemma gi_T3_heredity_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_T3_heredity"
  by (simp add: pp_T3_heredity_def gi_T2_fun_prime_admitted pp_fun_def pp_Fun_def
    gi_goodman_names_def gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def)

lemma gi_T3_heredity_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_T3_heredity = gb_T3_heredity G"
  by (simp add: pp_T3_heredity_def gb_T3_heredity_def
    gi_T2_fun_prime_var_translation gi_T2_diamond_translation gi_fun_translation
    gb_x_def[symmetric] Let_def)

theorem gi_T3_heredity_with_exhaustion:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T3_exhaustion_axioms G) (gb_T3_heredity G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have source: "[] ; pp_T3_min_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
    by (rule CEV_Goodman_T3_heredity_min[OF subset_refl])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_exhaustion_axioms G)
    (gi_to_book G [] k pp_T3_heredity)"
    by (rule gi_native_package_preservation[OF rich source gi_T3_min_source_closed
      gi_T3_exhaustion_axiom_from_native[OF rich names]]; simp)
  have restricted: "goodman_book_proves gb_signature G (gb_T3_exhaustion_axioms G)
    (gi_to_book G [] k pp_T3_heredity)"
    by (rule gi_native_conclusion_restrict[OF rich source _ gi_T3_heredity_admitted[OF names]
      universal gb_T3_exhaustion_axioms_language[OF rich]]; simp)
  show ?thesis using restricted by (simp only: gi_T3_heredity_translation[OF names])
qed

section \<open>The alternative repair: rigidity restricted to pure operators\<close>

definition gb_T3_pure_eq_rigidity where
  "gb_T3_pure_eq_rigidity G \<sigma> =
    (let x = gb_x G \<sigma>; y = gb_y G \<sigma> \<sigma>; eq = book_leibniz G \<sigma> (NVar x) (NVar y)
     in book_all G x (book_all G y
       (book_imp (book_and G (gb_pure \<sigma> (NVar x)) (gb_pure \<sigma> (NVar y)))
         (book_imp (gb_T2_source_diamond G [y, x] eq) eq))))"

definition gb_T3_rigid_axioms where
  "gb_T3_rigid_axioms G = insert (gb_T3_pure_eq_rigidity G gb_unary) (gb_T3_modal_axioms G)"

lemma gi_T3_pure_eq_rigidity_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (pp_pure_eq_rigidity \<sigma>)"
  by (simp add: pp_pure_eq_rigidity_def pp_pure_def pp_Pure_def gi_goodman_names_def
    gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def)

lemma gi_T3_pure_eq_rigidity_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k (pp_pure_eq_rigidity \<sigma>) = gb_T3_pure_eq_rigidity G \<sigma>"
  by (simp add: pp_pure_eq_rigidity_def gb_T3_pure_eq_rigidity_def
    gi_T2_diamond_translation gi_pure_translation gb_x_def[symmetric] gb_y_def[symmetric] Let_def)

lemma gb_T3_pure_eq_rigidity_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_T3_pure_eq_rigidity G \<sigma>)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have "book_theory_formula gb_signature G (gi_to_book G [] k (pp_pure_eq_rigidity \<sigma>))"
    by (rule gi_to_book_language[OF rich typed_pp_pure_eq_rigidity _ gi_T3_pure_eq_rigidity_admitted[OF names]]; simp)
  then show ?thesis by (simp only: gi_T3_pure_eq_rigidity_translation[OF names])
qed

lemma gb_T3_rigid_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T3_rigid_axioms G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_T3_rigid_axioms_def
  by (auto intro: gb_T3_pure_eq_rigidity_language gb_T3_modal_axioms_language)

lemma gi_T3_rigid_source_closed:
  "A \<in> pp_T3_rigid_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T3_rigid_axioms_def by (auto intro: typed_pp_QSS typed_pp_persistence typed_pp_pure_eq_rigidity)

lemma gi_T3_rigid_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> pp_T3_rigid_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_rigid_axioms G) (gi_to_book G [] k A)"
proof -
  have modal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_rigid_axioms G)
    (gi_to_book G [] k B)" if "B \<in> gi_T3_modal_source" for B
    by (rule gi_T3_modal_axiom_from_native[OF rich names _ that]; auto simp: gb_T3_rigid_axioms_def)
  have rigid: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_rigid_axioms G)
    (gi_to_book G [] k (pp_pure_eq_rigidity pp_unary_ty))"
  proof -
    have member': "gb_T3_pure_eq_rigidity G gb_unary \<in> gb_T3_rigid_axioms G"
      by (simp add: gb_T3_rigid_axioms_def)
    have native: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_rigid_axioms G)
      (gb_T3_pure_eq_rigidity G gb_unary)"
      by (rule goodman_book_proves.Axiom[OF member'
        gi_gb_universal_language[OF gb_T3_pure_eq_rigidity_language[OF rich]]])
    show ?thesis using native
      by (simp only: gi_T3_pure_eq_rigidity_translation[OF names] pp_unary_ty_def)
  qed
  show ?thesis using member modal rigid unfolding pp_T3_rigid_axioms_def gi_T3_modal_source_def by blast
qed

theorem gi_T3_heredity_with_pure_rigidity:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T3_rigid_axioms G) (gb_T3_heredity G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have source: "[] ; pp_T3_rigid_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
    by (rule CEV_Goodman_T3_heredity_rigid[OF subset_refl])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T3_rigid_axioms G)
    (gi_to_book G [] k pp_T3_heredity)"
    by (rule gi_native_package_preservation[OF rich source gi_T3_rigid_source_closed
      gi_T3_rigid_axiom_from_native[OF rich names]]; simp)
  have restricted: "goodman_book_proves gb_signature G (gb_T3_rigid_axioms G)
    (gi_to_book G [] k pp_T3_heredity)"
    by (rule gi_native_conclusion_restrict[OF rich source _ gi_T3_heredity_admitted[OF names]
      universal gb_T3_rigid_axioms_language[OF rich]]; simp)
  show ?thesis using restricted by (simp only: gi_T3_heredity_translation[OF names])
qed

section \<open>Preserve the stronger earlier repair without identifying it with the pure repair\<close>

definition gi_T3_possible_identity_source where
  "gi_T3_possible_identity_source = {pp_QSS, pp_persistence pp_unary_ty, pp_possible_identity_actual pp_unary_ty}"

lemma gi_T3_possible_identity_source_closed:
  "A \<in> gi_T3_possible_identity_source \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_T3_possible_identity_source_def
  by (auto intro: typed_pp_QSS typed_pp_persistence typed_pp_possible_identity_actual)

lemma gi_T3_possible_identity_source_admitted:
  "gi_goodman_names k \<Longrightarrow> A \<in> gi_T3_possible_identity_source \<Longrightarrow>
    gi_constants_admitted k gb_signature A"
  unfolding gi_T3_possible_identity_source_def
  by (auto simp: pp_QSS_def pp_persistence_def pp_possible_identity_actual_def
    pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def gi_goodman_names_def gb_signature_def
    ObjDiamond_def ObjBox_def ObjTrue_def)

theorem gi_T3_heredity_with_all_unary_rigidity_image_stock:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (image (gi_to_book G [] k) gi_T3_possible_identity_source) (gb_T3_heredity G)"
proof -
  have source: "[] ; gi_T3_possible_identity_source \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
    by (rule CEV_Goodman_T3_repaired_from; simp add: gi_T3_possible_identity_source_def)
  have translated: "goodman_book_proves gb_signature G
    (image (gi_to_book G [] k) gi_T3_possible_identity_source) (gi_to_book G [] k pp_T3_heredity)"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich source gi_T3_possible_identity_source_closed _ _
      gi_T3_possible_identity_source_admitted[OF names] gi_T3_heredity_admitted[OF names]]; simp)
  show ?thesis using translated by (simp only: gi_T3_heredity_translation[OF names])
qed

text \<open>
  The weak conclusion remains modal. The Exhaustion route uses logical
  purity/application plus unary Persistence, QSS, and zeroary Exhaustion;
  the pure-rigidity route uses only unary Persistence, QSS, and the displayed
  pure-identity rigidity axiom. Neither route adds PP. No necessity or
  minimality claim about these hypotheses is made.

  The final older repair retains its exact three-formula image stock; only
  its conclusion is independently identified with native Heredity. Its
  all-unary-identity premise is stronger than the pure-identity premise.
  It must not be advertised as the original argument or as an established
  consequence of the background. No model, consistency theorem, or
  derivation of uncorrected Heredity is obtained by these transfers.
\<close>

end
