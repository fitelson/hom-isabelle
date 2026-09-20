theory Goodman_Restricted_Signature_Transfer
  imports Goodman_Extension_Retraction
begin

section \<open>Whole CEV+ proofs in the requested target signature\<close>

lemma gi_CEV_conclusion_language:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and admitted: "gi_constants_admitted k \<Sigma> A"
  shows "book_theory_formula \<Sigma> G (gi_to_book G ns k A)"
  by (rule gi_to_book_language[OF rich CEV_axiom_proves_formula[OF derivation] chart admitted])

theorem gi_CEV_axiom_preservation_in_signature:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and closed: "\<And>B. B \<in> T \<Longrightarrow> [] \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_constants_admitted k \<Sigma> B"
    and conclusion: "gi_constants_admitted k \<Sigma> A"
  shows "goodman_book_proves \<Sigma> G (image (gi_to_book G [] k) T) (gi_to_book G ns k A)"
proof (rule gi_goodman_foreign_constants_eliminate[
    OF rich gi_CEV_axiom_preservation[OF rich derivation closed chart distinct]])
  fix B assume "B \<in> image (gi_to_book G [] k) T"
  then obtain C where member: "C \<in> T" and shape: "B = gi_to_book G [] k C" by blast
  show "book_theory_formula \<Sigma> G B" unfolding shape
    by (rule gi_to_book_language[OF rich closed[OF member] _ axioms[OF member]]; simp)
next
  show "named_in_signature \<Sigma> (gi_to_book G ns k A)"
    by (rule book_language_signature[OF gi_CEV_conclusion_language[OF rich derivation chart conclusion]])
qed

theorem gi_CEV_closed_refutation_in_signature:
  assumes rich: "sg_rich G" and refutation: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    and closed: "\<And>B. B \<in> T \<Longrightarrow> [] \<turnstile> B : Prop"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_constants_admitted k \<Sigma> B"
  shows "goodman_book_proves \<Sigma> G (image (gi_to_book G [] k) T) (book_bottom G)"
proof (rule gi_goodman_foreign_constants_eliminate[OF rich gi_CEV_closed_refutation[OF rich refutation closed]])
  fix B assume "B \<in> image (gi_to_book G [] k) T"
  then obtain C where member: "C \<in> T" and shape: "B = gi_to_book G [] k C" by blast
  show "book_theory_formula \<Sigma> G B" unfolding shape
    by (rule gi_to_book_language[OF rich closed[OF member] _ axioms[OF member]]; simp)
next
  show "named_in_signature \<Sigma> (book_bottom G)"
    by (rule book_language_signature[OF book_bottom_language[OF rich]])
qed

lemma gi_native_conclusion_restrict:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and admitted: "gi_constants_admitted k gb_signature A"
    and transfer: "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G ns k A)"
    and stock: "\<And>B. B \<in> U \<Longrightarrow> book_theory_formula gb_signature G B"
  shows "goodman_book_proves gb_signature G U (gi_to_book G ns k A)"
proof (rule gi_goodman_foreign_constants_eliminate[OF rich transfer])
  fix B assume "B \<in> U"
  then show "book_theory_formula gb_signature G B" by (rule stock)
next
  show "named_in_signature gb_signature (gi_to_book G ns k A)"
    by (rule book_language_signature[OF gi_CEV_conclusion_language[OF rich derivation chart admitted]])
qed

section \<open>Native central packages in the Pure/Fun signature\<close>

theorem gi_background_preservation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_background_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_background_axioms G) (gi_to_book G ns k A)"
  by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    gi_background_proof_preservation[OF rich names derivation chart distinct]
    gb_background_axioms_language[OF rich]])

theorem gi_recombination_PP_preservation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_axioms G) (gi_to_book G ns k A)"
  by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    gi_recombination_PP_preservation[OF rich names derivation chart distinct]
    gb_recombination_PP_language[OF rich]])

theorem gi_QLN_PP_preservation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_zeroary_unary_QLN_PP_axioms G) (gi_to_book G ns k A)"
  by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    gi_QLN_PP_preservation[OF rich names derivation chart distinct]
    gb_QLN_PP_language[OF rich]])

theorem gi_repaired_PP_preservation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; insert pp_zeroary_exhaustion pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_zeroary_exhaustion G) (gi_to_book G ns k A)"
  by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    gi_repaired_PP_preservation[OF rich names derivation chart distinct]
    gb_repaired_PP_language[OF rich]])

lemma gi_persistent_QLN_language:
  "sg_rich G \<Longrightarrow> B \<in> gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G \<Longrightarrow>
    book_theory_formula gb_signature G B"
  by (auto intro: gb_QLN_PP_language gb_persistence_schema_language)

theorem gi_persistent_QLN_PP_preservation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_full_QLN_PP_persistence_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G
    (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G) (gi_to_book G ns k A)"
  by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    gi_persistent_QLN_PP_preservation[OF rich names derivation chart distinct]
    gi_persistent_QLN_language[OF rich]])

section \<open>Consistency hypotheses now use the actual Goodman signature\<close>

corollary gi_recombination_PP_consistency_in_signature:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G)"
  shows "CEV_axiom_consistent [] pp_recombination_PP_axioms"
proof -
  have universal: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_recombination_PP_axioms G)"
    using consistent gi_goodman_consistency_universal_iff[OF rich gb_recombination_PP_language[OF rich]] by blast
  show ?thesis by (rule gi_recombination_PP_consistency_transfer[OF rich universal])
qed

corollary gi_QLN_PP_consistency_in_signature:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent gb_signature G (gb_zeroary_unary_QLN_PP_axioms G)"
  shows "CEV_axiom_consistent [] pp_full_QLN_PP_axioms"
proof -
  have universal: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_zeroary_unary_QLN_PP_axioms G)"
    using consistent gi_goodman_consistency_universal_iff[OF rich gb_QLN_PP_language[OF rich]] by blast
  show ?thesis by (rule gi_QLN_PP_consistency_transfer[OF rich universal])
qed

corollary gi_repaired_PP_consistency_in_signature:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent gb_signature G (gb_recombination_PP_zeroary_exhaustion G)"
  shows "CEV_axiom_consistent [] (insert pp_zeroary_exhaustion pp_recombination_PP_axioms)"
proof -
  have universal: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_recombination_PP_zeroary_exhaustion G)"
    using consistent gi_goodman_consistency_universal_iff[OF rich gb_repaired_PP_language[OF rich]] by blast
  show ?thesis by (rule gi_repaired_PP_consistency_transfer[OF rich universal])
qed

corollary gi_persistent_QLN_PP_consistency_in_signature:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent gb_signature G
      (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G)"
  shows "CEV_axiom_consistent [] pp_full_QLN_PP_persistence_axioms"
proof -
  have universal: "goodman_book_consistent (\<lambda>_. UNIV) G
      (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G)"
    using consistent gi_goodman_consistency_universal_iff[OF rich gi_persistent_QLN_language[OF rich]] by blast
  show ?thesis by (rule gi_persistent_QLN_PP_consistency_transfer[OF rich universal])
qed

text \<open>
  Only the conclusion and added axioms must use the declared signature.
  Intermediate proof formulas may use other constants. The target
  restriction is now proved, not assumed. The source closed-stock premise
  belongs to CEV+ translation, not to the general retraction theorem.
  All consistency statements remain conditional.
\<close>

end
