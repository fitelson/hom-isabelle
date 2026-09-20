theory Goodman_Exact_Closed_Decoding
  imports Goodman_Exact_Logical_Stock.Bacon_PP_ZF_Exact_Logical_Stock
    Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Soundness
    "Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Closed_Roundtrip"
begin

section \<open>Every closed logical named term has an old closed logical denotation\<close>

definition gi_exact_decode where
  "gi_exact_decode G A = pterm_to_oterm (book_named_to_pterm G A)"

lemma gi_pterm_empty_signature_const_free:
  "pterm_in_signature (\<lambda>_. {}) P \<Longrightarrow> consts_of (pterm_to_oterm P) = {}"
  by (induction P; auto)

lemma gi_closed_named_decode_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and closed: "named_fv A = {}"
  shows "[] \<turnstile> gi_exact_decode G A : \<sigma>"
proof -
  have named: "has_ntype book_minimal_logical_type G A \<sigma>"
    using book_language_named[OF language] unfolding named_in_language_def by blast
  have source: "has_stype book_minimal_logical_type [] (named_to_source G [] A) \<sigma>"
    by (rule named_to_source_closed_type[OF named closed])
  have parametric_type: "has_ptype [] (book_named_to_pterm G A) \<sigma>"
    unfolding book_named_to_pterm_def by (rule book_minimal_to_pterm_type[OF source])
  show ?thesis unfolding gi_exact_decode_def by (rule pterm_to_preserves_typing[OF parametric_type])
qed

lemma gi_closed_logical_decode:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "[] \<turnstile> gi_exact_decode G A : \<sigma>"
    and "pp_logical_vocabulary (gi_exact_decode G A)"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G A \<sigma>"
    and closed: "named_fv A = {}" using logical unfolding gb_closed_logical_def by blast+
  show "[] \<turnstile> gi_exact_decode G A : \<sigma>" by (rule gi_closed_named_decode_type[OF language closed])
  have signature: "pterm_in_signature (\<lambda>_. {}) (book_named_to_pterm G A)"
    by (rule book_named_translation_in_signature[OF language])
  show "pp_logical_vocabulary (gi_exact_decode G A)"
    unfolding pp_logical_vocabulary_def gi_exact_decode_def
    by (rule gi_pterm_empty_signature_const_free[OF signature])
qed

lemma gi_exact_old_closed_evaluation:
  assumes typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
  shows "pp_e_eval C g M = pp_e_closed_den M"
proof -
  have free: "consts_of M = {}" using logical unfolding pp_logical_vocabulary_def .
  have same_constants: "pp_e_eval C g M = pp_e_eval pp_e_default_constants g M"
    by (rule pp_e_eval_const_free[OF free])
  have left_member: "Elem (pp_e_eval pp_e_default_constants g M) (pp_e_domain \<sigma>)"
    using DefaultExactBaconConstants.pp_e_eval_type[OF typed pp_e_empty_env_typed]
    by (simp only: pp_e_dom_def)
  have right_member: "Elem (pp_e_closed_den M) (pp_e_domain \<sigma>)"
    by (rule pp_e_closed_den_in_domain[OF typed])
  have related: "pp_e_eqv \<sigma> [] (pp_e_eval pp_e_default_constants g M) (pp_e_closed_den M)"
    unfolding pp_e_closed_den_def
    by (rule DefaultExactBaconConstants.pp_e_eval_respects[OF typed pp_e_empty_env_eqv])
  have equal: "pp_e_eval pp_e_default_constants g M = pp_e_closed_den M"
    using related by (simp only: pp_e_eqv_iff_action_eq[OF left_member right_member]
      rev.simps pp_b_action_one_all[OF left_member] pp_b_action_one_all[OF right_member])
  show ?thesis by (rule trans[OF same_constants equal])
qed

theorem gi_closed_logical_decode_denotation:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_named_denote C G g A = pp_e_closed_den (gi_exact_decode G A)"
  unfolding gi_exact_named_denote_def gi_exact_decode_def[symmetric]
  by (rule gi_exact_old_closed_evaluation[OF gi_closed_logical_decode(1)[OF logical]
    gi_closed_logical_decode(2)[OF logical]])

section \<open>Changing the empty nonlogical alphabet loses no logical terms\<close>

abbreviation gi_string_logical_to_goodman :: "string book_named_term \<Rightarrow> gb_term" where
  "gi_string_logical_to_goodman A \<equiv> book_typed_name_map (\<lambda>_ _. PureName) A"

lemma gi_empty_signature_name_map_language:
  "book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G A \<sigma> \<Longrightarrow>
    book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G (book_typed_name_map f A) \<sigma>"
  by (rule book_typed_name_map_language; auto)

lemma gi_empty_signature_name_map_closed_logical:
  "gb_closed_logical G \<sigma> A \<Longrightarrow> gb_closed_logical G \<sigma> (book_typed_name_map f A)"
  unfolding gb_closed_logical_def
  by (auto simp: book_typed_name_map_fv intro: gi_empty_signature_name_map_language)

lemma gi_logical_string_roundtrip:
  "named_in_signature (\<lambda>_. {}) A \<Longrightarrow>
    gi_goodman_string_term (gi_string_logical_to_goodman A) = A"
  by (induction A; auto)

theorem gi_goodman_closed_logical_decode_denotation:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "[] \<turnstile> gi_exact_decode G (gi_goodman_string_term A) : \<sigma>"
    and "pp_logical_vocabulary (gi_exact_decode G (gi_goodman_string_term A))"
    and "gi_exact_goodman_denote C G g A = pp_e_closed_den (gi_exact_decode G (gi_goodman_string_term A))"
proof -
  have mapped: "gb_closed_logical G \<sigma> (gi_goodman_string_term A)"
    by (rule gi_empty_signature_name_map_closed_logical[OF logical])
  show "[] \<turnstile> gi_exact_decode G (gi_goodman_string_term A) : \<sigma>"
    by (rule gi_closed_logical_decode(1)[OF mapped])
  show "pp_logical_vocabulary (gi_exact_decode G (gi_goodman_string_term A))"
    by (rule gi_closed_logical_decode(2)[OF mapped])
  show "gi_exact_goodman_denote C G g A = pp_e_closed_den (gi_exact_decode G (gi_goodman_string_term A))"
    unfolding gi_exact_goodman_denote_def by (rule gi_closed_logical_decode_denotation[OF mapped])
qed

text \<open>
  This proves the reverse denotational inclusion for every closed logical
  named term, not just terms in the image of the forward translation.
  Empty-signature retyping changes only an alphabet which the term cannot
  use. The comparison with pp_e_closed_den does not assume that its old
  all-Empty assignment is globally typed. The following theory,
  Goodman_Exact_Stock_Correspondence, combines this reverse inclusion
  with all-type forward denotation preservation to prove stock equality.
\<close>

end
