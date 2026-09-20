theory Goodman_Native_TU_RS_Witness
  imports Goodman_Native_T6_Routes
    "Goodman_Integration_Individual.Goodman_TU_RS_Witness"
begin

section \<open>TU ⇒ RS in the native calculus, with the explicit witness R₊\<close>

text \<open>
  Goodman's notes (p.2, classification bullet, RS item) assert
  "Inv ⊢ RS and TU ⊢ RS, witness G := 'true and fun′'". The checked
  constructor proof (Goodman_TU_RS_Witness) derives RS from the stock
  gi_TU_RS_axioms = PP core (logical purity, application closure, PP)
  ∪ {zeroary Exhaustion, ∃fun′, TU}. Zeroary Exhaustion enters through
  the TU⇒Inv classification and is retained here, as is ∃fun′, which
  is the §4 standing assumption of the notes. Nothing below asserts the
  implication over the weaker stock lacking Exhaustion. The notes'
  p.2 entailment and p.3 "RS is not comparable to TU" remarks remain an
  unresolved source discrepancy. This transfer does not establish that
  Goodman intended the latter remark only for the weaker scope.

  The stock below is written with the independent native packages.
  Its members are literal translations of the constructor stock except
  zeroary Exhaustion, whose native form is related to the translated
  formula by the existing provable equivalence, not by syntactic identity.
\<close>

definition gb_TU_RS_axioms where
  "gb_TU_RS_axioms G = gb_T6_core G \<union>
    {gb_zeroary_exhaustion G, gb_exists_fun_prime G, gb_TU G}"

lemma gb_TU_RS_axioms_T1_form:
  "gb_TU_RS_axioms G = gb_T1_axioms G \<union> {gb_target_PP, gb_exists_fun_prime G, gb_TU G}"
  unfolding gb_TU_RS_axioms_def gb_T6_core_def gb_T1_axioms_def by auto

lemma gb_TU_RS_axioms_language:
  assumes rich: "sg_rich G" and member: "A \<in> gb_TU_RS_axioms G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gb_TU_RS_axioms_def
  by (auto intro: gb_T6_core_language[OF rich] gb_zeroary_exhaustion_language[OF rich]
    gb_exists_fun_prime_language[OF rich] gb_TU_language_closed(1)[OF rich])

lemma gb_TU_RS_axioms_closed:
  assumes rich: "sg_rich G" and member: "A \<in> gb_TU_RS_axioms G"
  shows "named_fv A = {}"
proof -
  have zero: "named_fv (gb_zeroary_exhaustion G) = {}"
    by (rule gb_T1_axioms_closed[where G=G]) (simp add: gb_T1_axioms_def)
  show ?thesis using member unfolding gb_TU_RS_axioms_def
    by (auto simp: zero gb_exists_fun_prime_closed gb_TU_language_closed(2)[OF rich]
      dest: gb_T6_core_closed)
qed

section \<open>Stock correspondence: every constructor axiom is native-derivable\<close>

lemma gi_TU_RS_axioms_closed:
  "A \<in> gi_TU_RS_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_TU_RS_axioms_def pp_T6_core_PP_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed typed_pp_target_PP
    typed_pp_zeroary_exhaustion typed_pp_exists_fun_prime typed_pp_TU)

theorem gi_TU_RS_literal_stock_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) (pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_TU})
    \<subseteq> gb_TU_RS_axioms G"
  unfolding gb_TU_RS_axioms_def image_Un image_insert image_empty
    gi_exists_fun_prime_translation[OF names] gi_TU_native_translation[OF names]
  using gi_T6_core_inclusion[OF rich names] by blast

lemma gi_TU_RS_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> gi_TU_RS_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_TU_RS_axioms G) (gi_to_book G [] k A)"
proof -
  consider (core) "A \<in> pp_T6_core_PP_axioms" | (exhaustion) "A = pp_zeroary_exhaustion"
    | (existence) "A = pp_exists_fun_prime" | (tu) "A = pp_TU"
    using member unfolding gi_TU_RS_axioms_def by blast
  then show ?thesis
  proof cases
    case core
    have native: "gi_to_book G [] k A \<in> gb_T6_core G"
      using gi_T6_core_inclusion[OF rich names] core by blast
    have in_U: "gi_to_book G [] k A \<in> gb_TU_RS_axioms G"
      using native unfolding gb_TU_RS_axioms_def by blast
    have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
      by (rule gi_gb_universal_language[OF gb_T6_core_language[OF rich native]])
    show ?thesis by (rule goodman_book_proves.Axiom[OF in_U language])
  next
    case exhaustion
    show ?thesis unfolding exhaustion
      by (rule gi_zeroary_exhaustion_from_native[OF rich names]) (simp add: gb_TU_RS_axioms_def)
  next
    case existence
    have in_U: "gb_exists_fun_prime G \<in> gb_TU_RS_axioms G" by (simp add: gb_TU_RS_axioms_def)
    show ?thesis unfolding existence gi_exists_fun_prime_translation[OF names]
      by (rule goodman_book_proves.Axiom[OF in_U
        gi_gb_universal_language[OF gb_exists_fun_prime_language[OF rich]]])
  next
    case tu
    have in_U: "gb_TU G \<in> gb_TU_RS_axioms G" by (simp add: gb_TU_RS_axioms_def)
    show ?thesis unfolding tu gi_TU_native_translation[OF names]
      by (rule goodman_book_proves.Axiom[OF in_U
        gi_gb_universal_language[OF gb_TU_language_closed(1)[OF rich]]])
  qed
qed

theorem gi_TU_RS_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; gi_TU_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_TU_RS_axioms G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_TU_RS_axioms G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_TU_RS_axioms_closed
      gi_TU_RS_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    universal gb_TU_RS_axioms_language[OF rich]])
qed

section \<open>The RS endpoint with the independent native RS formula\<close>

theorem gi_native_TU_RS_derives_RS:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_TU_RS_axioms G) (gb_RS G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have translated: "goodman_book_proves gb_signature G (gb_TU_RS_axioms G) (gi_to_book G [] k pp_RS)"
    by (rule gi_TU_RS_native_preservation[OF rich names gi_CEV_TU_RS_exact_stock _ _
      gi_RS_admitted[OF names]]; simp)
  show ?thesis using translated by (simp only: gi_RS_native_translation[OF names])
qed

section \<open>The explicit witness R₊ = λp.(p ∧ fun′ p) in the named language\<close>

definition gb_RS_plus_on_chart where
  "gb_RS_plus_on_chart G ns =
    (let p = named_chart_fresh G ns Prop
     in NLam p (book_and G (NVar p) (gb_fun_prime_on_chart G (p # ns) (NVar p))))"

definition gb_RS_plus where
  "gb_RS_plus G = gb_RS_plus_on_chart G []"

lemma gi_RS_plus_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k gi_RS_plus = gb_RS_plus_on_chart G ns"
  by (simp add: gi_RS_plus_def gb_RS_plus_on_chart_def
    gi_T6_fun_prime_variable_native_translation Let_def)

lemma gi_RS_plus_shift_by[simp]: "shift_by n gi_RS_plus = gi_RS_plus"
  by (simp add: gi_RS_plus_def pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_by_def shift_ren_def)

lemma gi_RS_plus_purity_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (pp_pure pp_unary_ty gi_RS_plus)"
  by (simp add: gi_RS_plus_def pp_fun_prime_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def gi_constants_rename)

lemma gi_RS_plus_specification_admitted:
  "gi_goodman_names k \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_rigid_specification gi_RS_plus)"
  by (simp add: pp_rigid_specification_def pp_spec_instantiated_def pp_spec_only_fun_prime_def
    pp_spec_rigid_def gi_RS_plus_def pp_fun_prime_def pp_group_member_def pp_reversible_def
    pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def shift_def gi_constants_rename)

theorem gi_native_TU_RS_witness_pure:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_TU_RS_axioms G) (gb_pure gb_unary (gb_RS_plus G))"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "[] ; gi_TU_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty gi_RS_plus"
    by (rule gi_RS_plus_pure) (auto simp: gi_TU_RS_axioms_def)
  have translated: "goodman_book_proves gb_signature G (gb_TU_RS_axioms G)
      (gi_to_book G [] k (pp_pure pp_unary_ty gi_RS_plus))"
    by (rule gi_TU_RS_native_preservation[OF rich names original _ _
      gi_RS_plus_purity_admitted[OF names]]; simp)
  show ?thesis using translated
    by (simp only: gi_pure_translation[OF names] gi_RS_plus_native_translation[OF names]
      gb_RS_plus_def pp_unary_ty_def)
qed

theorem gi_native_TU_RS_witness_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_TU_RS_axioms G)
    (gi_to_book G [] k (pp_rigid_specification gi_RS_plus))"
  by (rule gi_TU_RS_native_preservation[OF rich names gi_CEV_TU_RS_exact_witness _ _
    gi_RS_plus_specification_admitted[OF names]]; simp)

section \<open>The uniform native specification of R₊, up to α\<close>

text \<open>
  Under each binder the translation re-chooses the bound name inside R₊.
  The closed term R₊ has α-equivalent translations on every distinct chart,
  so the four conjuncts are α-congruent to the uniform native formula
  gb_rigid_specification_on_chart G [] (gb_RS_plus G), in which the same
  named term gb_RS_plus G occurs at every position.
\<close>

lemma gi_RS_plus_chart_alpha:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and distinct: "distinct ns"
  shows "named_alpha G (gi_to_book G ns k gi_RS_plus) (gb_RS_plus G)"
  unfolding gb_RS_plus_def gi_RS_plus_native_translation[OF names, symmetric]
  by (rule gi_closed_chart_alpha[OF rich gi_RS_plus_type distinct])

theorem gi_RS_plus_specification_alpha:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "named_alpha G (gi_to_book G [] k (pp_rigid_specification gi_RS_plus))
    (gb_rigid_specification_on_chart G [] (gb_RS_plus G))"
proof -
  define z where "z = named_chart_fresh G [] gb_unary"
  define p where "p = named_chart_fresh G [z] Prop"
  define q where "q = named_chart_fresh G [p, z] Prop"
  define p0 where "p0 = named_chart_fresh G [] Prop"
  have zp: "p \<noteq> z" using named_chart_fresh_notin[OF rich, of "[z]" Prop] by (simp add: p_def)
  have qp: "q \<noteq> p" and qz: "q \<noteq> z"
    using named_chart_fresh_notin[OF rich, of "[p, z]" Prop] by (simp_all add: q_def)
  have leaf0: "named_alpha G (gi_to_book G [p0] k gi_RS_plus) (gb_RS_plus G)"
    by (rule gi_RS_plus_chart_alpha[OF rich names]) simp
  have leaf3: "named_alpha G (gi_to_book G [q, p, z] k gi_RS_plus) (gb_RS_plus G)"
    by (rule gi_RS_plus_chart_alpha[OF rich names]) (simp add: zp qp qz)
  have pure: "gi_to_book G [] k (pp_pure pp_unary_ty gi_RS_plus) = gb_pure gb_unary (gb_RS_plus G)"
    by (simp only: gi_pure_translation[OF names] gi_RS_plus_native_translation[OF names]
      gb_RS_plus_def pp_unary_ty_def)
  have instantiated: "named_alpha G (gi_to_book G [] k (pp_spec_instantiated gi_RS_plus))
      (gb_spec_instantiated_on_chart G [] (gb_RS_plus G))"
    unfolding pp_spec_instantiated_def gb_spec_instantiated_on_chart_def
    by (simp only: gi_to_book.simps gi_RS_plus_shift Let_def nth_Cons_0 book_exists_def
      p0_def[symmetric])
      (intro named_alpha.App named_alpha.Lam named_alpha.Refl leaf0)
  have only: "named_alpha G (gi_to_book G [] k (pp_spec_only_fun_prime gi_RS_plus))
      (gb_spec_only_fun_prime_on_chart G [] (gb_RS_plus G))"
    unfolding pp_spec_only_fun_prime_def gb_spec_only_fun_prime_on_chart_def
    by (simp only: gi_to_book.simps gi_RS_plus_shift Let_def nth_Cons_0 book_all_def book_imp_def
      gi_T6_fun_prime_variable_native_translation[OF names] p0_def[symmetric])
      (intro named_alpha.App named_alpha.Lam named_alpha.Refl leaf0)
  have rigid: "named_alpha G (gi_to_book G [] k (pp_spec_rigid gi_RS_plus))
      (gb_spec_rigid_on_chart G [] (gb_RS_plus G))"
    unfolding pp_spec_rigid_def gb_spec_rigid_on_chart_def
    by (simp only: gi_to_book.simps gi_RS_plus_shift gi_RS_plus_shift_by Let_def nth_Cons_0 nth_Cons_Suc
      numeral_2_eq_2 One_nat_def book_all_def book_imp_def book_and_def book_leibniz_def pp_unary_ty_def
      gi_T6_group_variable_native_translation[OF names] z_def[symmetric] p_def[symmetric] q_def[symmetric])
      (intro named_alpha.App named_alpha.Lam named_alpha.Refl leaf3)
  show ?thesis
    unfolding pp_rigid_specification_def gb_rigid_specification_on_chart_def
    by (simp only: gi_to_book.simps pure book_and_def)
      (intro named_alpha.App named_alpha.Refl instantiated only rigid)
qed

theorem gi_native_TU_RS_witness_specification:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_TU_RS_axioms G)
    (gb_rigid_specification_on_chart G [] (gb_RS_plus G))"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule gi_goodman_alpha_transport[OF rich gi_RS_plus_specification_alpha[OF rich names]
      gi_native_TU_RS_witness_translated[OF rich names]])
qed

text \<open>
  The three native endpoints are: purity of the named witness, its full
  rigid-specification conjunction (purity, instantiation, only-fun′,
  rigidity), and RS itself, each over gb_TU_RS_axioms G in gb_signature.
  No translation parameter k occurs in any endpoint statement. The stock
  retains zeroary Exhaustion and ∃fun′; no result here removes either.
  These are derivability statements in the named axiom extension, not a
  deduction-theorem implication and not consistency of the stock.
\<close>

end
