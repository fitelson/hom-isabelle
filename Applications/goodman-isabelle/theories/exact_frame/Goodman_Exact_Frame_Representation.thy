theory Goodman_Exact_Frame_Representation
  imports
    "Goodman_Integration_Exact_QLN.Goodman_Exact_10_1_Transfer"
    "Goodman_Integration_Exact_Applicative.Goodman_Exact_Denotation_Translation"
    "Goodman_Integration_Exact_Applicative.Goodman_Exact_Modal_Functionality"
    "Goodman_Exact_Frame_Completeness.Bacon_PP_ZF_Exact_Completeness"
begin

section \<open>Bacon's frame-consistency representation for closed named sentences\<close>

text \<open>
  The preserved enumeration and frame-completeness snapshots are now
  selected (sessions Goodman_Exact_Enumeration and Goodman_Exact_Frame_Completeness,
  with their recorded import lines). Their sentence-level result is
  pp_e_Bacon_consistency_representation: a sentence A of the t-generated
  fragment over the string signature S is frame-consistent, i.e. true at the
  root of SOME typed interpretation C of the constants on Bacon's fixed
  frame, iff ◇A is true at the root of the single glued interpretation
  pp_e_complete_constants S.

  Here that theorem is transferred to closed named string terms through the
  decoder used by the accepted Theorem 10.1 transfer. "Consistency" means
  satisfiability on the fixed frame; the frame theory ranges over typed
  interpretations of the constants on that frame. It is neither syntactic
  H consistency nor H completeness, and the alphabet of constant names is
  the fixed string alphabet of the snapshot.
\<close>

subsection \<open>The named signature predicate and its decoding\<close>

fun gi_exact_named_in_signature ::
  "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> string book_named_term \<Rightarrow> bool" where
  "gi_exact_named_in_signature S (NVar n) = True"
| "gi_exact_named_in_signature S (NConst c \<sigma>) = S c \<sigma>"
| "gi_exact_named_in_signature S (NLogical l) = True"
| "gi_exact_named_in_signature S (NApp F A) =
    (gi_exact_named_in_signature S F \<and> gi_exact_named_in_signature S A)"
| "gi_exact_named_in_signature S (NLam n A) = gi_exact_named_in_signature S A"

lemma gi_exact_minimal_logical_in_signature:
  "pp_e_term_in_signature S (pterm_to_oterm (book_minimal_logical_translation l))"
  by (cases l) simp_all

lemma gi_exact_named_in_signature_encoding:
  "pp_e_term_in_signature S (pterm_to_oterm (book_minimal_to_pterm (named_to_source G ns M))) =
    gi_exact_named_in_signature S M"
  by (induction M arbitrary: ns) (simp_all add: gi_exact_minimal_logical_in_signature)

theorem gi_exact_named_in_signature_decode_iff:
  "pp_e_term_in_signature S (gi_exact_decode G M) \<longleftrightarrow> gi_exact_named_in_signature S M"
  by (simp only: gi_exact_decode_def book_named_to_pterm_def gi_exact_named_in_signature_encoding)

lemma gi_exact_named_in_signature_iff_ssignature:
  "gi_exact_named_in_signature (\<lambda>c \<sigma>. c \<in> \<Sigma> \<sigma>) M \<longleftrightarrow> named_in_signature \<Sigma> M"
  by (induction M) simp_all

subsection \<open>Named sentences of the fragment and their decoded sentences\<close>

definition gi_exact_named_sentence where
  "gi_exact_named_sentence S G M \<longleftrightarrow>
    book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G M Prop \<and>
    named_fv M = {} \<and>
    gi_exact_named_propositional_term G M \<and>
    gi_exact_named_in_signature S M"

lemma gi_exact_named_sentence_decode:
  assumes sentence: "gi_exact_named_sentence S G M"
  shows "pp_e_sentence S (gi_exact_decode G M)"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G M Prop"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
    and signature: "gi_exact_named_in_signature S M"
    using sentence unfolding gi_exact_named_sentence_def by blast+
  have typed: "[] \<turnstile> gi_exact_decode G M : Prop"
    by (rule gi_closed_named_decode_type[OF language closed_term])
  have decoded_fragment: "pp_e_propositional_term (gi_exact_decode G M)"
    by (simp only: gi_exact_named_propositional_decode_iff; rule fragment)
  have decoded_signature: "pp_e_term_in_signature S (gi_exact_decode G M)"
    by (simp only: gi_exact_named_in_signature_decode_iff; rule signature)
  show ?thesis unfolding pp_e_sentence_def using typed decoded_fragment decoded_signature by blast
qed

lemma gi_exact_named_sentence_from_signature:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M Prop"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "gi_exact_named_sentence (\<lambda>c \<sigma>. c \<in> \<Sigma> \<sigma>) G M"
proof -
  have universal: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G M Prop"
    by (rule book_language_signature_mono[OF language]; simp)
  have signature: "named_in_signature \<Sigma> M" by (rule book_language_signature[OF language])
  show ?thesis unfolding gi_exact_named_sentence_def
    using universal closed_term fragment signature
    by (simp only: gi_exact_named_in_signature_iff_ssignature)
qed

subsection \<open>Frame satisfiability and truth in the complete model, natively\<close>

definition gi_exact_named_frame_satisfiable where
  "gi_exact_named_frame_satisfiable G g M \<longleftrightarrow>
    (\<exists>C. pp_e_constants C \<and> pp_e_holds (gi_exact_named_denote C G g M) [])"

lemma gi_exact_named_frame_satisfiable_decode:
  assumes closed_term: "named_fv M = {}"
  shows "gi_exact_named_frame_satisfiable G g M \<longleftrightarrow>
    (\<exists>C. pp_e_constants C \<and> pp_e_true_in C (gi_exact_decode G M))"
  unfolding gi_exact_named_frame_satisfiable_def pp_e_true_in_def
  by (simp only: gi_exact_closed_named_decoder_value[OF closed_term])

theorem gi_exact_named_frame_consistent_decode:
  assumes sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_satisfiable G g M \<longleftrightarrow> pp_e_frame_consistent S (gi_exact_decode G M)"
proof -
  have closed_term: "named_fv M = {}" using sentence unfolding gi_exact_named_sentence_def by blast
  show ?thesis
    unfolding gi_exact_named_frame_satisfiable_decode[OF closed_term] pp_e_frame_consistent_iff_model
    using gi_exact_named_sentence_decode[OF sentence] by blast
qed

theorem gi_exact_named_frame_representation_branch:
  assumes sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_satisfiable G g M \<longleftrightarrow>
    (\<exists>w. pp_e_holds (gi_exact_named_denote (pp_e_complete_constants S) G h M) w)"
proof -
  have closed_term: "named_fv M = {}" using sentence unfolding gi_exact_named_sentence_def by blast
  have decoded: "pp_e_sentence S (gi_exact_decode G M)" by (rule gi_exact_named_sentence_decode[OF sentence])
  have representation: "pp_e_frame_consistent S (gi_exact_decode G M) \<longleftrightarrow>
      pp_e_true_in (pp_e_complete_constants S) (\<diamond>\<^sub>o (gi_exact_decode G M))"
    by (rule pp_e_Bacon_consistency_representation[OF decoded])
  have possible: "pp_e_true_in (pp_e_complete_constants S) (\<diamond>\<^sub>o (gi_exact_decode G M)) \<longleftrightarrow>
      (\<exists>w. pp_e_holds (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env (gi_exact_decode G M)) w)"
    by (rule pp_e_ObjDiamond_true_iff)
  show ?thesis
    unfolding gi_exact_named_frame_consistent_decode[OF sentence] representation possible
    by (simp only: gi_exact_closed_named_decoder_value[OF closed_term])
qed

theorem gi_exact_named_frame_representation_diamond:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G h"
    and sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_satisfiable G g M \<longleftrightarrow>
    pp_e_holds (gi_exact_named_denote (pp_e_complete_constants S) G h
      (book_not G (book_box G (book_not G M)))) []"
proof -
  have language: "book_theory_formula (\<lambda>_. UNIV) G M"
    using sentence unfolding gi_exact_named_sentence_def by blast
  have not_language: "book_theory_formula (\<lambda>_. UNIV) G (book_not G M)"
    by (rule book_not_language[OF rich language])
  have box_language: "book_theory_formula (\<lambda>_. UNIV) G (book_box G (book_not G M))"
    by (rule book_box_language[OF rich not_language])
  let ?C = "pp_e_complete_constants S"
  have model: "pp_e_constants ?C" by (rule pp_e_complete_constants_model)
  have outer: "pp_e_holds (gi_exact_named_denote ?C G h (book_not G (book_box G (book_not G M)))) [] \<longleftrightarrow>
      \<not> pp_e_holds (gi_exact_named_denote ?C G h (book_box G (book_not G M))) []"
    by (rule pp_e_constants.gi_exact_named_not_holds[OF model rich typed box_language])
  have box: "pp_e_holds (gi_exact_named_denote ?C G h (book_box G (book_not G M))) [] \<longleftrightarrow>
      (\<forall>v. prefix [] v \<longrightarrow> pp_e_holds (gi_exact_named_denote ?C G h (book_not G M)) v)"
    by (rule pp_e_constants.gi_exact_named_box_holds[OF model rich typed not_language])
  have inner: "\<And>v. pp_e_holds (gi_exact_named_denote ?C G h (book_not G M)) v \<longleftrightarrow>
      \<not> pp_e_holds (gi_exact_named_denote ?C G h M) v"
    by (rule pp_e_constants.gi_exact_named_not_holds[OF model rich typed language])
  have diamond: "pp_e_holds (gi_exact_named_denote ?C G h (book_not G (book_box G (book_not G M)))) [] \<longleftrightarrow>
      (\<exists>w. pp_e_holds (gi_exact_named_denote ?C G h M) w)"
    unfolding outer box inner by simp
  show ?thesis unfolding diamond by (rule gi_exact_named_frame_representation_branch[OF sentence])
qed

subsection \<open>The complete model realizes every frame-satisfiable named sentence at a branch\<close>

theorem gi_exact_named_frame_satisfiable_at_branch:
  assumes sentence: "gi_exact_named_sentence S G M"
    and satisfiable: "gi_exact_named_frame_satisfiable G g M"
  shows "\<exists>n. pp_e_holds (gi_exact_named_denote (pp_e_complete_constants S) G h M) [n]"
proof -
  have closed_term: "named_fv M = {}" using sentence unfolding gi_exact_named_sentence_def by blast
  have consistent: "pp_e_frame_consistent S (gi_exact_decode G M)"
    using satisfiable by (simp only: gi_exact_named_frame_consistent_decode[OF sentence])
  have member: "gi_exact_decode G M \<in> pp_e_frame_consistent_sentences S"
    using consistent unfolding pp_e_frame_consistent_sentences_def by simp
  have in_range: "gi_exact_decode G M \<in> range (pp_e_consistent_sentence_enum S)"
    using pp_e_consistent_sentence_enum_range[of S] member by simp
  obtain n where enum': "gi_exact_decode G M = pp_e_consistent_sentence_enum S n"
    using in_range by (rule rangeE)
  have enum: "pp_e_consistent_sentence_enum S n = gi_exact_decode G M" by (rule enum'[symmetric])
  have branch: "pp_e_holds (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env (gi_exact_decode G M)) [n]"
    using pp_e_enumerated_sentence_true_at_branch[of S n] unfolding enum .
  show ?thesis using branch by (simp only: gi_exact_closed_named_decoder_value[OF closed_term]) blast
qed

subsection \<open>The companion necessity theorem: frame validity is necessity in the complete model\<close>

definition gi_exact_named_frame_valid where
  "gi_exact_named_frame_valid G g M \<longleftrightarrow>
    (\<forall>C. pp_e_constants C \<longrightarrow> pp_e_holds (gi_exact_named_denote C G g M) [])"

lemma gi_exact_named_frame_valid_decode:
  assumes sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_valid G g M \<longleftrightarrow> gi_exact_decode G M \<in> pp_e_frame_theory S"
proof -
  have closed_term: "named_fv M = {}" using sentence unfolding gi_exact_named_sentence_def by blast
  have decoded: "pp_e_sentence S (gi_exact_decode G M)" by (rule gi_exact_named_sentence_decode[OF sentence])
  show ?thesis
    unfolding gi_exact_named_frame_valid_def pp_e_frame_theory_def pp_e_true_in_def
    using decoded by (simp only: gi_exact_closed_named_decoder_value[OF closed_term]) blast
qed

theorem gi_exact_named_frame_completeness_branch:
  assumes sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_valid G g M \<longleftrightarrow>
    (\<forall>w. pp_e_holds (gi_exact_named_denote (pp_e_complete_constants S) G h M) w)"
proof -
  have closed_term: "named_fv M = {}" using sentence unfolding gi_exact_named_sentence_def by blast
  have decoded: "pp_e_sentence S (gi_exact_decode G M)" by (rule gi_exact_named_sentence_decode[OF sentence])
  have completeness: "gi_exact_decode G M \<in> pp_e_frame_theory S \<longleftrightarrow>
      pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o (gi_exact_decode G M))"
    by (rule pp_e_Bacon_exact_completeness[OF decoded])
  have necessary: "pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o (gi_exact_decode G M)) \<longleftrightarrow>
      (\<forall>w. pp_e_holds (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env (gi_exact_decode G M)) w)"
    by (rule pp_e_ObjBox_true_iff)
  show ?thesis
    unfolding gi_exact_named_frame_valid_decode[OF sentence] completeness necessary
    by (simp only: gi_exact_closed_named_decoder_value[OF closed_term])
qed

theorem gi_exact_named_frame_completeness_box:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G h"
    and sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_valid G g M \<longleftrightarrow>
    pp_e_holds (gi_exact_named_denote (pp_e_complete_constants S) G h (book_box G M)) []"
proof -
  have language: "book_theory_formula (\<lambda>_. UNIV) G M"
    using sentence unfolding gi_exact_named_sentence_def by blast
  let ?C = "pp_e_complete_constants S"
  have model: "pp_e_constants ?C" by (rule pp_e_complete_constants_model)
  have box: "pp_e_holds (gi_exact_named_denote ?C G h (book_box G M)) [] \<longleftrightarrow>
      (\<forall>v. prefix [] v \<longrightarrow> pp_e_holds (gi_exact_named_denote ?C G h M) v)"
    by (rule pp_e_constants.gi_exact_named_box_holds[OF model rich typed language])
  have all_worlds: "pp_e_holds (gi_exact_named_denote ?C G h (book_box G M)) [] \<longleftrightarrow>
      (\<forall>w. pp_e_holds (gi_exact_named_denote ?C G h M) w)"
    unfolding box by simp
  show ?thesis unfolding all_worlds by (rule gi_exact_named_frame_completeness_branch[OF sentence])
qed

theorem gi_exact_named_frame_valid_iff_negation_unsatisfiable:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and sentence: "gi_exact_named_sentence S G M"
  shows "gi_exact_named_frame_valid G g M \<longleftrightarrow> \<not> gi_exact_named_frame_satisfiable G g (book_not G M)"
proof -
  have language: "book_theory_formula (\<lambda>_. UNIV) G M"
    using sentence unfolding gi_exact_named_sentence_def by blast
  have negated: "\<And>C. pp_e_constants C \<Longrightarrow>
      pp_e_holds (gi_exact_named_denote C G g (book_not G M)) [] \<longleftrightarrow>
      \<not> pp_e_holds (gi_exact_named_denote C G g M) []"
    by (rule pp_e_constants.gi_exact_named_not_holds[OF _ rich typed language])
  show ?thesis
    unfolding gi_exact_named_frame_valid_def gi_exact_named_frame_satisfiable_def
    using negated by blast
qed

lemma gi_exact_complete_constants_model:
  "pp_e_constants (pp_e_complete_constants S)"
  by (rule pp_e_complete_constants_model)

text \<open>
  gi_exact_named_frame_valid G g M says that M is true at the root of every
  typed interpretation of the string constants on the frame; by the exact
  completeness theorem this is equivalent to M being true at every
  substitution of the complete model, and to the native □M being true at its
  root. Together with the representation theorem above, satisfiability and
  validity of closed named sentences of the fragment are both characterized
  by the single complete model. This is not an effective decision procedure.
  gi_exact_named_frame_satisfiable G g M says that M is true at the root of
  some typed interpretation of the string constants on Bacon's fixed frame;
  by the representation theorem this is equivalent to M being true at some
  substitution w in the single complete model pp_e_complete_constants S, and
  (for a rich variable stock and typed assignment) to the native ◇M = ¬□¬M
  being true at the root of that model. The complete model is itself a typed
  interpretation on the frame. The alphabet is the fixed string alphabet, the
  fragment is t-generated, and nothing is asserted about syntactic H
  consistency, H completeness, or the arbitrary-name Theorem 10.1.
\<close>

end
