theory Bacon_Book_Conjunction_Decoding_Environment
  imports Bacon_Book_Conjunction_Raw_Conversion_Transport Bacon_Book_Full_Environment
begin

section \<open>Decoding pulls a conjunction environment back to the tagged signature\<close>

text \<open>
  Define Jᵈg(A)=Jg(dec(A)), leaving D, App and G unchanged.
  A full environment for the primitive-conjunction language then supplies
  a full minimal environment for the EXACT tagged target signature.
  Source role: the primitive-symbol encoding for Bacon §5.2, p.104,
  with the environment condition of Definition 14.13, p.302.

  Target-language guards control the distinguished tag at every typing
  step. For raw conversion, the proved decoder first retracts the chain
  into that target signature; wrong-type foreign tags are not decoded as
  if they had the type of ∧. Free-variable preservation transfers the
  exact intersection agreement condition.

  This is environment transport from an explicitly supplied environment.
  No valuation, logical-value witness, conjunction truth clause, model
  existence, or Functionality is assumed or concluded.
\<close>

definition book_conj_decoded_denote ::
  "((nat \<Rightarrow> 'v) \<Rightarrow> 'c book_conj_term \<Rightarrow> 'v) \<Rightarrow>
    (nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> 'v" where
  "book_conj_decoded_denote J g A = J g (book_conj_decode A)"

theorem book_conj_decoded_full_environment:
  fixes \<Sigma> :: "'c ssignature"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_conj_term \<Rightarrow> 'v"
  assumes rich: "sg_rich G"
    and original: "book_full_environment D app book_conj_logical_type UNIV \<Sigma> G J"
  shows "book_full_environment D app book_minimal_logical_type UNIV
    (book_conj_target_signature \<Sigma>) G (book_conj_decoded_denote J)"
proof -
  interpret Source: book_full_environment D app book_conj_logical_type UNIV \<Sigma> G J
    by (rule original)
  have decoded_type: "book_conj_decoded_denote J g A \<in> D \<tau>"
    if language: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G A \<tau>"
      and typed: "book_env_typed D G g" for A \<tau> g
  proof -
    have decoded: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode A) \<tau>"
      by (rule book_conj_decode_language[OF language])
    show ?thesis unfolding book_conj_decoded_denote_def
      by (rule Source.denote_type[OF UNIV_I decoded typed])
  qed
  have decoded_var: "book_conj_decoded_denote J g (NVar n) = g n"
    if typed: "book_env_typed D G g" for g n
    by (simp only: book_conj_decoded_denote_def book_conj_decode.simps;
      rule Source.denote_var[OF UNIV_I typed])
  have decoded_app: "book_conj_decoded_denote J g (NApp F A) =
      app \<sigma> \<tau> (book_conj_decoded_denote J g F) (book_conj_decoded_denote J g A)"
    if head: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G F (Arr \<sigma> \<tau>)"
      and argument: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G A \<sigma>"
      and typed: "book_env_typed D G g" for F A \<sigma> \<tau> g
  proof -
    have decoded_head: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode F) (Arr \<sigma> \<tau>)"
      by (rule book_conj_decode_language[OF head])
    have decoded_argument: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode A) \<sigma>"
      by (rule book_conj_decode_language[OF argument])
    show ?thesis by (simp only: book_conj_decoded_denote_def book_conj_decode.simps;
      rule Source.denote_app[OF UNIV_I UNIV_I UNIV_I decoded_head decoded_argument typed])
  qed
  have decoded_environment: "book_conj_decoded_denote J g A = book_conj_decoded_denote J h B"
    if left: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G A \<tau>"
      and right: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G B \<tau>"
      and conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
      and gt: "book_env_typed D G g" and ht: "book_env_typed D G h"
      and overlap: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
    for A B \<tau> g h
  proof -
    have decoded_left: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode A) \<tau>"
      by (rule book_conj_decode_language[OF left])
    have decoded_right: "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_decode B) \<tau>"
      by (rule book_conj_decode_language[OF right])
    have decoded_conversion: "named_raw_beta_eta book_conj_logical_type G \<tau> (book_conj_decode A) (book_conj_decode B)"
      by (rule book_conj_decode_raw_conversion[OF rich conversion left right])
    show ?thesis unfolding book_conj_decoded_denote_def
    proof (rule Source.environment[OF UNIV_I UNIV_I decoded_left decoded_right decoded_conversion gt ht])
      fix n
      assume shared: "n \<in> named_fv (book_conj_decode A) \<inter> named_fv (book_conj_decode B)"
      have original_shared: "n \<in> named_fv A \<inter> named_fv B"
        using shared by (simp only: book_conj_decode_fv)
      show "g n = h n" by (rule overlap[OF original_shared])
    qed
  qed
  show ?thesis
    by (unfold_locales;
      (rule Source.app_type | rule decoded_type | rule decoded_var | rule decoded_app | rule decoded_environment);
      assumption)
qed

end
