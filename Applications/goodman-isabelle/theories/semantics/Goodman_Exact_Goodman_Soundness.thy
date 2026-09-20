theory Goodman_Exact_Goodman_Soundness
  imports Goodman_Exact_Classicist_Soundness
    "Goodman_Integration_T6.Goodman_Extension_Constant_Map"
    "Bacon_Book_Environment_Development.Bacon_Book_Constant_Model_Pullback"
begin

section \<open>The native Pure/Fun language on the same exact carriers\<close>

lemma gi_goodman_string_term_as_constant_rename:
  "gi_goodman_string_term A = book_constant_rename gi_goodman_string_name A"
  by (induction A; simp add: book_constant_rename_simps)

definition gi_exact_goodman_denote where
  "gi_exact_goodman_denote C G g A = gi_exact_named_denote C G g (gi_goodman_string_term A)"

lemma gi_exact_goodman_denote_pullback:
  "gi_exact_goodman_denote C G = book_constant_pullback_denote (gi_exact_named_denote C G) gi_goodman_string_name"
  by (rule ext, rule ext; simp only: gi_exact_goodman_denote_def
    book_constant_pullback_denote_def gi_goodman_string_term_as_constant_rename)

definition gi_exact_goodman_global_valid where
  "gi_exact_goodman_global_valid C G A \<longleftrightarrow> gi_exact_global_valid C G (gi_goodman_string_term A)"

lemma gi_exact_goodman_global_valid_iff:
  "gi_exact_goodman_global_valid C G A \<longleftrightarrow>
    (\<forall>w g. book_env_typed gi_exact_domain G g \<longrightarrow>
      gi_exact_valuation w (gi_exact_goodman_denote C G g A))"
  by (simp only: gi_exact_goodman_global_valid_def gi_exact_global_valid_def
    book_formula_valid_def gi_exact_goodman_denote_def)

context pp_e_constants
begin

theorem gi_exact_goodman_minimal_model:
  assumes rich: "sg_rich G"
  shows "book_full_minimal_model gi_exact_domain gi_exact_app gb_signature G
    (gi_exact_goodman_denote C G) (gi_exact_valuation w) gi_exact_logical_value"
proof -
  have original: "book_full_minimal_model gi_exact_domain gi_exact_app gi_goodman_string_signature G
    (gi_exact_named_denote C G) (gi_exact_valuation w) gi_exact_logical_value"
    by (rule gi_exact_book_minimal_model[OF rich])
  have pulled: "book_full_minimal_model gi_exact_domain gi_exact_app gb_signature G
    (book_constant_pullback_denote (gi_exact_named_denote C G) gi_goodman_string_name)
    (gi_exact_valuation w) gi_exact_logical_value"
    by (rule book_full_minimal_model.book_constant_pullback_full_minimal_model[
      OF original gi_goodman_string_signature_map])
  show ?thesis by (simp only: gi_exact_goodman_denote_pullback; rule pulled)
qed

theorem gi_exact_goodman_extension_global_sound:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves gb_signature G T A"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_exact_goodman_global_valid C G B"
  shows "gi_exact_goodman_global_valid C G A"
proof -
  have renamed: "goodman_book_proves gi_goodman_string_signature G
    (image gi_goodman_string_term T) (gi_goodman_string_term A)"
    by (rule gi_goodman_string_proof_preservation[OF rich derivation])
  have valid: "gi_exact_global_valid C G (gi_goodman_string_term A)"
  proof (rule gi_exact_extension_global_sound[OF rich renamed])
    fix B assume "B \<in> image gi_goodman_string_term T"
    then obtain D where member: "D \<in> T" and shape: "B = gi_goodman_string_term D" by blast
    show "gi_exact_global_valid C G B"
      using axioms[OF member] unfolding gi_exact_goodman_global_valid_def shape .
  qed
  show ?thesis using valid by (simp only: gi_exact_goodman_global_valid_def)
qed

theorem gi_exact_goodman_consistent_of_global_axioms:
  assumes rich: "sg_rich G"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_exact_goodman_global_valid C G B"
  shows "goodman_book_consistent gb_signature G T"
proof (unfold goodman_book_consistent_def, intro notI)
  assume refutation: "goodman_book_proves gb_signature G T (book_bottom G)"
  have global: "gi_exact_goodman_global_valid C G (book_bottom G)"
    by (rule gi_exact_goodman_extension_global_sound[OF rich refutation axioms])
  have impossible: "gi_exact_global_valid C G (book_bottom G)"
    using global by (simp only: gi_exact_goodman_global_valid_def book_typed_name_map_bottom)
  show False by (rule notE[OF gi_exact_bottom_not_global[OF rich] impossible])
qed

end

corollary gi_exact_empty_native_extension_consistent:
  assumes rich: "sg_rich G"
  shows "goodman_book_consistent gb_signature G {}"
proof -
  have constants: "pp_e_constants pp_e_default_constants"
    by standard (simp add: pp_e_default_constants_def pp_e_default_in_domain)
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_consistent_of_global_axioms[OF constants rich]; simp)
qed

text \<open>
  The typed Pure/Fun names have only been relabeled; domains, application,
  worlds, logical values and assignments are unchanged. This now covers
  the native Goodman axiom-extension predicate itself, not just a string
  surrogate. All added axioms must be globally valid. In particular no
  interpretation satisfying PP is asserted and no old/new pure-stock
  equality is inferred from this conditional soundness theorem.
\<close>

end
