theory Goodman_Native_Biconditional_Algebra
  imports
    "Goodman_Legacy_WI_Master.Bacon_PP_Goodman_T6_WI_Master"
    "Goodman_Integration_Native_Extras.Goodman_Native_T6_Extras"
begin

section \<open>Biconditional operators are self-inverse, pure, and members of G\<close>

text \<open>
  Goodman's notes, p.2 ("Reversible" bullet): for any pure proposition A the
  operator λp.(p ↔ A) is a known member of G, and these operators "are each
  their own inverse". The preserved constructor helpers
  CEV_axiom_biconditional_self_inverse, CEV_axiom_biconditional_operator_pure_from
  and CEV_axiom_biconditional_group_member_from prove the parameterised facts
  inside larger WI-route derivations. Here they are packaged individually as
  closed sentences and transferred to the native language.

  Self-inverseness needs no added axiom at all: (B_a ∘ B_a) = id is a
  theorem of C⁺ for every a. The conditional purity and group-membership
  results are proved here from Pure(a) over the T6 PP core (logical purity,
  application closure, PP at t→t). This does not establish that PP is necessary;
  no L2, Exhaustion, fun′ or classification principle occurs. Composition is
  λp.B_a(B_a p), identity is Leibniz identity at t→t, and G-membership is
  the native gb_group_member_on_chart (purity plus a pure two-sided inverse).
\<close>

subsection \<open>Closed constructor sentences from the preserved helpers\<close>

definition gi_bic_self_inverse where
  "gi_bic_self_inverse = Forall Prop (Eq pp_unary_ty
    (pp_compose (pp_biconditional_operator (Var 0)) (pp_biconditional_operator (Var 0)))
    pp_identity_operator)"

definition gi_bic_operator_pure where
  "gi_bic_operator_pure = Forall Prop (Imp (pp_pure Prop (Var 0))
    (pp_pure pp_unary_ty (pp_biconditional_operator (Var 0))))"

definition gi_bic_group_member where
  "gi_bic_group_member = Forall Prop (Imp (pp_pure Prop (Var 0))
    (pp_group_member (pp_biconditional_operator (Var 0))))"

theorem gi_CEV_bic_self_inverse:
  "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_bic_self_inverse"
proof -
  let ?B = "pp_biconditional_operator (Var 0)"
  let ?E = "Eq pp_unary_ty (pp_compose ?B ?B) pp_identity_operator"
  have pt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have body: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ ?E"
    using CEV_axiom_biconditional_self_inverse[OF pt, where T=T and S="{}"]
    by (simp only: CEV_axiom_from_empty_iff)
  have et: "[Prop] \<turnstile> ?E : Prop" by (rule CEV_axiom_proves_formula[OF body])
  show ?thesis unfolding gi_bic_self_inverse_def by (rule CEV_axiom_generalize_theorem[OF et body])
qed

theorem gi_CEV_bic_operator_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_bic_operator_pure"
proof -
  let ?H = "pp_pure Prop (Var 0)"
  have pt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have ht: "[Prop] \<turnstile> ?H : Prop" by (rule typed_pp_pure[OF pt])
  have h: "[Prop] ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H" by (rule CEV_axiom_from.Assumption[OF _ ht]) simp
  have conclusion: "[Prop] ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_biconditional_operator (Var 0))"
    by (rule CEV_axiom_biconditional_operator_pure_from[OF core pt h])
  have body: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (pp_pure pp_unary_ty (pp_biconditional_operator (Var 0)))"
    by (rule CEV_axiom_from_singleton_imp[OF ht conclusion])
  have bt: "[Prop] \<turnstile> Imp ?H (pp_pure pp_unary_ty (pp_biconditional_operator (Var 0))) : Prop"
    by (rule CEV_axiom_proves_formula[OF body])
  show ?thesis unfolding gi_bic_operator_pure_def by (rule CEV_axiom_generalize_theorem[OF bt body])
qed

theorem gi_CEV_bic_group_member:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_bic_group_member"
proof -
  let ?H = "pp_pure Prop (Var 0)"
  have pt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have ht: "[Prop] \<turnstile> ?H : Prop" by (rule typed_pp_pure[OF pt])
  have h: "[Prop] ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H" by (rule CEV_axiom_from.Assumption[OF _ ht]) simp
  have conclusion: "[Prop] ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member (pp_biconditional_operator (Var 0))"
    by (rule CEV_axiom_biconditional_group_member_from[OF core pt h])
  have body: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (pp_group_member (pp_biconditional_operator (Var 0)))"
    by (rule CEV_axiom_from_singleton_imp[OF ht conclusion])
  have bt: "[Prop] \<turnstile> Imp ?H (pp_group_member (pp_biconditional_operator (Var 0))) : Prop"
    by (rule CEV_axiom_proves_formula[OF body])
  show ?thesis unfolding gi_bic_group_member_def by (rule CEV_axiom_generalize_theorem[OF bt body])
qed

lemma gi_bic_self_inverse_typed: "[] \<turnstile> gi_bic_self_inverse : Prop"
  by (rule CEV_axiom_proves_formula[OF gi_CEV_bic_self_inverse])

lemma gi_bic_operator_pure_typed: "[] \<turnstile> gi_bic_operator_pure : Prop"
  by (rule CEV_axiom_proves_formula[OF gi_CEV_bic_operator_pure[OF subset_refl]])

lemma gi_bic_group_member_typed: "[] \<turnstile> gi_bic_group_member : Prop"
  by (rule CEV_axiom_proves_formula[OF gi_CEV_bic_group_member[OF subset_refl]])

subsection \<open>Native sentences on explicit charts\<close>

definition gb_bic_self_inverse where
  "gb_bic_self_inverse G =
    (let a = named_chart_fresh G [] Prop; p = named_chart_fresh G [a] Prop
     in book_all G a (book_leibniz G gb_unary
       (gb_T6_compose p (gb_biconditional_operator_on_chart G [p, a] (NVar a))
         (gb_biconditional_operator_on_chart G [p, a] (NVar a)))
       (gb_T6_identity p)))"

definition gb_bic_operator_pure where
  "gb_bic_operator_pure G =
    (let a = named_chart_fresh G [] Prop
     in book_all G a (book_imp (gb_pure Prop (NVar a))
       (gb_pure gb_unary (gb_biconditional_operator_on_chart G [a] (NVar a)))))"

definition gb_bic_group_member where
  "gb_bic_group_member G =
    (let a = named_chart_fresh G [] Prop
     in book_all G a (book_imp (gb_pure Prop (NVar a))
       (gb_group_member_on_chart G [a] (gb_biconditional_operator_on_chart G [a] (NVar a)))))"

lemma gi_bic_builder_shift[simp]: "rename Suc pp_biconditional_builder = pp_biconditional_builder"
  by (simp add: pp_biconditional_builder_def)

lemma gi_bic_self_inverse_translation:
  "gi_to_book G [] k gi_bic_self_inverse = gb_bic_self_inverse G"
  by (simp add: gi_bic_self_inverse_def gb_bic_self_inverse_def pp_compose_def
    pp_biconditional_operator_def gb_biconditional_operator_on_chart_def gb_T6_compose_def
    gi_T6_identity_native_translation gi_T6_biconditional_builder_native_translation
    pp_unary_ty_def shift_def Let_def)

lemma gi_bic_operator_pure_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k gi_bic_operator_pure = gb_bic_operator_pure G"
  by (simp add: gi_bic_operator_pure_def gb_bic_operator_pure_def gi_pure_translation
    gi_T6_biconditional_operator_variable_native_translation pp_unary_ty_def Let_def)

subsection \<open>α-transport for the group-membership sentence\<close>

text \<open>
  Inside pp_group_member the operator B_a is re-translated under the
  reversibility binders, so the literal translation names the builder's
  bound variables differently at each occurrence. The builder is a closed
  logical term; its chart translations are α-equivalent, and congruence
  gives the uniform native sentence in which the same term
  gb_biconditional_operator_on_chart G [a] (NVar a) occurs throughout.
\<close>

lemma gb_bic_builder_chart_alpha:
  assumes rich: "sg_rich G" and ns: "distinct ns" and ms: "distinct ms"
  shows "named_alpha G (gb_biconditional_builder_on_chart G ns :: gb_term) (gb_biconditional_builder_on_chart G ms)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have left: "named_alpha G (gi_to_book G ns k pp_biconditional_builder) (gi_to_book G [] k pp_biconditional_builder)"
    by (rule gi_closed_chart_alpha[OF rich typed_pp_biconditional_builder ns])
  have right: "named_alpha G (gi_to_book G ms k pp_biconditional_builder) (gi_to_book G [] k pp_biconditional_builder)"
    by (rule gi_closed_chart_alpha[OF rich typed_pp_biconditional_builder ms])
  have both: "named_alpha G (gi_to_book G ns k pp_biconditional_builder) (gi_to_book G ms k pp_biconditional_builder)"
    by (rule named_alpha.Trans[OF left named_alpha.Sym[OF right]])
  show ?thesis using both[unfolded gi_T6_biconditional_builder_native_translation] .
qed

theorem gi_bic_group_member_alpha:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "named_alpha G (gi_to_book G [] k gi_bic_group_member) (gb_bic_group_member G)"
proof -
  define a where "a = named_chart_fresh G [] Prop"
  define i where "i = named_chart_fresh G [a] gb_unary"
  define p where "p = named_chart_fresh G [i, a] Prop"
  have ia: "i \<noteq> a" using named_chart_fresh_notin[OF rich, of "[a]" gb_unary] by (simp add: i_def)
  have pi: "p \<noteq> i" and pa: "p \<noteq> a"
    using named_chart_fresh_notin[OF rich, of "[i, a]" Prop] by (simp_all add: p_def)
  have leaf2: "named_alpha G (gb_biconditional_builder_on_chart G [i, a] :: gb_term) (gb_biconditional_builder_on_chart G [a])"
    by (rule gb_bic_builder_chart_alpha[OF rich]) (simp_all add: ia)
  have leaf3: "named_alpha G (gb_biconditional_builder_on_chart G [p, i, a] :: gb_term) (gb_biconditional_builder_on_chart G [a])"
    by (rule gb_bic_builder_chart_alpha[OF rich]) (simp_all add: ia pi pa)
  show ?thesis
    unfolding gi_bic_group_member_def gb_bic_group_member_def pp_group_member_def pp_reversible_def
      pp_compose_def pp_identity_operator_def pp_biconditional_operator_def
      gb_group_member_on_chart_def gb_T2a_group_member_def gb_T2a_reversible_def
      gb_biconditional_operator_on_chart_def
    apply (simp only: gi_to_book.simps shift_def rename.simps gi_bic_builder_shift lift_ren.simps
      gi_pure_translation[OF names] gi_T6_biconditional_builder_native_translation
      Let_def nth_Cons_0 nth_Cons_Suc One_nat_def pp_unary_ty_def
      book_all_def book_imp_def book_and_def book_exists_def book_leibniz_def gb_pure_def
      a_def[symmetric] i_def[symmetric] p_def[symmetric])
    by (intro named_alpha.App named_alpha.Lam named_alpha.Refl leaf2 leaf3)
qed

subsection \<open>Admissibility in the declared signature\<close>

lemma gi_bic_self_inverse_admitted:
  "gi_constants_admitted k \<Sigma> gi_bic_self_inverse"
  by (simp add: gi_bic_self_inverse_def pp_compose_def pp_biconditional_operator_def
    pp_biconditional_builder_def pp_identity_operator_def shift_def gi_constants_rename)

lemma gi_bic_operator_pure_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature gi_bic_operator_pure"
  by (simp add: gi_bic_operator_pure_def pp_biconditional_operator_def pp_biconditional_builder_def
    pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def)

lemma gi_bic_group_member_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature gi_bic_group_member"
  by (simp add: gi_bic_group_member_def pp_group_member_def pp_reversible_def pp_compose_def
    pp_identity_operator_def pp_biconditional_operator_def pp_biconditional_builder_def
    pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

subsection \<open>Transfer over the empty stock and over the native T6 PP core\<close>

lemma gi_T6_core_axioms_closed:
  "A \<in> pp_T6_core_PP_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T6_core_PP_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed typed_pp_target_PP)

lemma gi_T6_core_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> pp_T6_core_PP_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_T6_core G) (gi_to_book G [] k A)"
proof -
  have native: "gi_to_book G [] k A \<in> gb_T6_core G"
    using gi_T6_core_inclusion[OF rich names] member by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_gb_universal_language[OF gb_T6_core_language[OF rich native]])
  show ?thesis by (rule goodman_book_proves.Axiom[OF native language])
qed

theorem gi_T6_core_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T6_core G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_T6_core_axioms_closed
      gi_T6_core_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    universal gb_T6_core_language[OF rich]])
qed

theorem gi_native_bic_self_inverse_empty_stock:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G {} (gb_bic_self_inverse G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have translated: "goodman_book_proves gb_signature G (image (gi_to_book G [] k) {})
      (gi_to_book G [] k gi_bic_self_inverse)"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich gi_CEV_bic_self_inverse _ _ _ _
      gi_bic_self_inverse_admitted]; simp)
  show ?thesis using translated by (simp only: image_empty gi_bic_self_inverse_translation)
qed

theorem gi_native_bic_self_inverse:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G U (gb_bic_self_inverse G)"
  by (rule goodman_book_mono[OF gi_native_bic_self_inverse_empty_stock[OF rich]]) simp

theorem gi_native_bic_operator_pure:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_bic_operator_pure G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G [] k gi_bic_operator_pure)"
    by (rule gi_T6_core_native_preservation[OF rich names gi_CEV_bic_operator_pure[OF subset_refl] _ _
      gi_bic_operator_pure_admitted[OF names]]; simp)
  show ?thesis using translated by (simp only: gi_bic_operator_pure_translation[OF names])
qed

theorem gi_native_bic_group_member_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G [] k gi_bic_group_member)"
  by (rule gi_T6_core_native_preservation[OF rich names gi_CEV_bic_group_member[OF subset_refl] _ _
    gi_bic_group_member_admitted[OF names]]; simp)

theorem gi_native_bic_group_member:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_bic_group_member G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule gi_goodman_alpha_transport[OF rich gi_bic_group_member_alpha[OF rich names]
      gi_native_bic_group_member_translated[OF rich names]])
qed

subsection \<open>Language and closedness of the native sentences\<close>

lemma gb_bic_self_inverse_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_bic_self_inverse G)"
    and "named_fv (gb_bic_self_inverse G :: gb_term) = {}"
proof -
  note lc = gi_native_T6_extra_language_closed[where G=G and M=gi_bic_self_inverse and B="gb_bic_self_inverse G",
    OF rich gi_bic_self_inverse_typed gi_bic_self_inverse_admitted gi_bic_self_inverse_translation]
  show "book_theory_formula gb_signature G (gb_bic_self_inverse G)" by (rule lc(1))
  show "named_fv (gb_bic_self_inverse G :: gb_term) = {}" by (rule lc(2))
qed

lemma gb_bic_operator_pure_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_bic_operator_pure G)"
    and "named_fv (gb_bic_operator_pure G :: gb_term) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=gi_bic_operator_pure and B="gb_bic_operator_pure G",
    OF rich gi_bic_operator_pure_typed gi_bic_operator_pure_admitted gi_bic_operator_pure_translation] by blast+

text \<open>
  gb_bic_self_inverse G is ∀a.((λp.B_a(B_a p)) = λp.p), a theorem of C⁺ over
  every added stock, in particular over the empty one. gb_bic_operator_pure G
  is ∀a.(Pure(a) → Pure(B_a)) and gb_bic_group_member G is ∀a.(Pure(a) → B_a ∈ G),
  both over the native T6 PP core. These package the notes' "known members of G"
  remark for biconditional operators. They do not assert WI, Inv, or that these
  are the only members of G, and they are not the exact-root group algebra of T9.
\<close>

end
