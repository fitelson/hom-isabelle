theory Goodman_Exact_QLN_Transfer
  imports
    "Goodman_Exact_Recombination.Bacon_PP_ZF_Exact_Recombination"
    "Goodman_Integration_Logical_Stock.Goodman_Exact_Stock_Correspondence"
    "Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Translation"
begin

section \<open>Transport exact truth through a native, empty-stock equivalence\<close>

context pp_e_constants
begin

lemma gi_exact_goodman_closed_global_translation:
  assumes rich: "sg_rich G" and term_type: "[] \<turnstile> M : Prop"
    and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
    and old_truth: "\<And>w. pp_e_holds (pp_e_eval C pp_e_closed_env M) w"
  shows "gi_exact_goodman_global_valid C G (gi_to_book G [] k M)"
proof (unfold gi_exact_goodman_global_valid_iff, intro allI impI)
  fix w g
  assume typed: "book_env_typed gi_exact_domain G g"
  have denotation: "gi_exact_goodman_denote C G g (gi_to_book G [] k M) =
      pp_e_eval C pp_e_closed_env M"
    by (rule gi_exact_goodman_closed_denotation_translation[
      OF rich term_type typed names vocabulary])
  show "gi_exact_valuation w (gi_exact_goodman_denote C G g (gi_to_book G [] k M))"
    by (simp only: denotation gi_exact_valuation_def; rule old_truth)
qed

lemma gi_exact_goodman_empty_equivalence_transport:
  assumes rich: "sg_rich G"
    and left_language: "book_theory_formula gb_signature G A"
    and right_language: "book_theory_formula gb_signature G B"
    and equivalence: "goodman_book_proves (\<lambda>_. UNIV) G {} (book_iff G A B)"
    and left_valid: "gi_exact_goodman_global_valid C G A"
  shows "gi_exact_goodman_global_valid C G B"
proof -
  have iff_language: "book_theory_formula gb_signature G (book_iff G A B)"
    by (rule book_iff_language[OF rich left_language right_language])
  have restricted: "goodman_book_proves gb_signature G {} (book_iff G A B)"
  proof (rule gi_goodman_foreign_constants_eliminate[OF rich equivalence])
    fix D :: gb_term
    assume impossible: "D \<in> {}"
    then show "book_theory_formula gb_signature G D" by simp
  next
    show "named_in_signature gb_signature (book_iff G A B)"
      by (rule book_language_signature[OF iff_language])
  qed
  have iff_valid: "gi_exact_goodman_global_valid C G (book_iff G A B)"
  proof (rule gi_exact_goodman_extension_global_sound[OF rich restricted])
    fix D :: gb_term
    assume impossible: "D \<in> {}"
    then show "gi_exact_goodman_global_valid C G D" by simp
  qed
  show ?thesis
  proof (unfold gi_exact_goodman_global_valid_iff, intro allI impI)
    fix w g
    assume typed: "book_env_typed gi_exact_domain G g"
    have iff_at_world: "gi_exact_valuation w
        (gi_exact_goodman_denote C G g (book_iff G A B))"
      using iff_valid typed by (simp only: gi_exact_goodman_global_valid_iff; blast)
    have left_at_world: "gi_exact_valuation w (gi_exact_goodman_denote C G g A)"
      using left_valid typed by (simp only: gi_exact_goodman_global_valid_iff; blast)
    have semantic_iff:
        "gi_exact_valuation w (gi_exact_goodman_denote C G g (book_iff G A B)) =
          (gi_exact_valuation w (gi_exact_goodman_denote C G g A) =
            gi_exact_valuation w (gi_exact_goodman_denote C G g B))"
      by (rule book_full_minimal_model.book_iff_truth[
        OF gi_exact_goodman_minimal_model[OF rich] rich typed left_language right_language])
    show "gi_exact_valuation w (gi_exact_goodman_denote C G g B)"
      using semantic_iff iff_at_world left_at_world by blast
  qed
qed

theorem gi_exact_goodman_closed_equivalence_transfer:
  assumes rich: "sg_rich G" and term_type: "[] \<turnstile> M : Prop"
    and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
    and admitted: "gi_constants_admitted k gb_signature M"
    and native_language: "book_theory_formula gb_signature G B"
    and equivalence: "goodman_book_proves (\<lambda>_. UNIV) G {}
      (book_iff G (gi_to_book G [] k M) B)"
    and old_truth: "\<And>w. pp_e_holds (pp_e_eval C pp_e_closed_env M) w"
  shows "gi_exact_goodman_global_valid C G B"
proof -
  have translated_language: "book_theory_formula gb_signature G (gi_to_book G [] k M)"
    by (rule gi_to_book_language[OF rich term_type _ admitted]; simp)
  have translated_valid: "gi_exact_goodman_global_valid C G (gi_to_book G [] k M)"
    by (rule gi_exact_goodman_closed_global_translation[
      OF rich term_type names vocabulary old_truth])
  show ?thesis by (rule gi_exact_goodman_empty_equivalence_transport[
    OF rich translated_language native_language equivalence translated_valid])
qed

end

section \<open>Source-name and target-type guards for the four QLN directions\<close>

lemma gi_exact_zeroary_recombination_vocabulary:
  "consts_of pp_zeroary_recombination \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_zeroary_recombination_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def)

lemma gi_exact_unary_recombination_vocabulary:
  "consts_of pp_unary_recombination \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def)

lemma gi_exact_zeroary_exhaustion_vocabulary:
  "consts_of pp_zeroary_exhaustion \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def)

lemma gi_exact_unary_exhaustion_vocabulary:
  "consts_of pp_unary_exhaustion \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_unary_exhaustion_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def)

lemma gi_exact_zeroary_recombination_admitted:
  assumes names: "gi_goodman_names k"
  shows "gi_constants_admitted k gb_signature pp_zeroary_recombination"
  using names by (simp add: pp_zeroary_recombination_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def gi_goodman_names_def gb_signature_def)

lemma gi_exact_unary_recombination_admitted:
  assumes names: "gi_goodman_names k"
  shows "gi_constants_admitted k gb_signature pp_unary_recombination"
  using names by (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
      ObjBox_def ObjTrue_def gi_goodman_names_def gb_signature_def)

lemma gi_exact_zeroary_exhaustion_admitted:
  assumes names: "gi_goodman_names k"
  shows "gi_constants_admitted k gb_signature pp_zeroary_exhaustion"
  using names by (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def gi_goodman_names_def gb_signature_def)

lemma gi_exact_unary_exhaustion_admitted:
  assumes names: "gi_goodman_names k"
  shows "gi_constants_admitted k gb_signature pp_unary_exhaustion"
  using names by (simp add: pp_unary_exhaustion_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
      ObjBox_def ObjTrue_def gi_goodman_names_def gb_signature_def)

lemma gi_exact_QLN_constants:
  "pp_e_constants pp_e_generic_internal_constants"
  by standard (rule pp_e_generic_internal_constants_typed)

section \<open>Native global QLN for the exact generic-seed interpretation\<close>

text \<open>
  These four conclusions use Bacon's exact carriers and the existing
  generic seed for the complete closed-logical stock. They are global:
  every world and every typed total assignment is covered. The intermediate
  equivalence proofs have no added axioms, and their universal signature
  is retracted to the declared Goodman signature before soundness is used.

  The zeroary/unary scope is explicit. This file does not assemble the
  remaining background schemas, identify the generic seed with a different
  glued proposition, or prove PP.
\<close>

theorem gi_exact_generic_zeroary_recombination_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_zeroary_recombination G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_exact_QLN_constants rich typed_pp_zeroary_recombination names
        gi_exact_zeroary_recombination_vocabulary gi_exact_zeroary_recombination_admitted[OF names]
        gb_zeroary_recombination_language[OF rich] gi_zeroary_recombination_equivalence[OF rich names]
        pp_e_generic_zeroary_recombination_holds])
qed

theorem gi_exact_generic_unary_recombination_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_unary_recombination G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_exact_QLN_constants rich typed_pp_unary_recombination names
        gi_exact_unary_recombination_vocabulary gi_exact_unary_recombination_admitted[OF names]
        gb_unary_recombination_language[OF rich] gi_unary_recombination_equivalence[OF rich names]
        pp_e_generic_unary_recombination_holds])
qed

theorem gi_exact_generic_zeroary_exhaustion_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_zeroary_exhaustion G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_exact_QLN_constants rich typed_pp_zeroary_exhaustion names
        gi_exact_zeroary_exhaustion_vocabulary gi_exact_zeroary_exhaustion_admitted[OF names]
        gb_zeroary_exhaustion_language[OF rich] gi_zeroary_exhaustion_equivalence[OF rich names]
        pp_e_generic_zeroary_exhaustion_holds])
qed

theorem gi_exact_generic_unary_exhaustion_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_unary_exhaustion G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_exact_QLN_constants rich typed_pp_unary_exhaustion names
        gi_exact_unary_exhaustion_vocabulary gi_exact_unary_exhaustion_admitted[OF names]
        gb_unary_exhaustion_language[OF rich] gi_unary_exhaustion_equivalence[OF rich names]
        pp_e_generic_unary_exhaustion_holds])
qed

end
