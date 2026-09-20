theory Goodman_Exact_Named_Conversion
  imports Goodman_Exact_Interpretation_Structure
    "Goodman_Exact_Legacy_07.Bacon_PP_ZF_Exact_CEV_Soundness"
    "Bacon_Book_Environment_Development.Bacon_Book_Full_Environment"
begin

section \<open>Exact denotation is preserved by typed βη conversion\<close>

text \<open>
  The book's named source relation permits raw typed βη conversion.
  The existing source translation places each such conversion, with
  declared-language endpoints, in a sufficiently large finite prefix of
  the variable stock. We decode its parametric terms into the constructor
  syntax and use the exact appendix evaluator's contextual β/η theorems.

  No new conversion axiom is assumed. Constants retain the typed values
  required by pp_e_constants. The carrier, application, and evaluator are
  those of the preceding exact-model adapter.
\<close>

context pp_e_constants
begin

lemma gi_exact_pterm_beta_eval:
  assumes contraction: "pcompatible_step pbeta_contract M N"
    and left_type: "has_ptype \<Gamma> M \<tau>"
    and right_type: "has_ptype \<Gamma> N \<tau>"
    and assignment_type: "pp_e_env_typed \<Gamma> g"
  shows "pp_e_eval C g (pterm_to_oterm M) =
    pp_e_eval C g (pterm_to_oterm N)"
proof -
  have decoded_step:
      "compatible_step beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
    by (rule iffD1[OF pcompatible_beta_string_iff contraction])
  have decoded_left: "\<Gamma> \<turnstile> pterm_to_oterm M : \<tau>"
    by (rule pterm_to_preserves_typing[OF left_type])
  have decoded_right: "\<Gamma> \<turnstile> pterm_to_oterm N : \<tau>"
    by (rule pterm_to_preserves_typing[OF right_type])
  show ?thesis
    by (rule pp_e_beta_compatible_eval[
      OF decoded_step decoded_left decoded_right assignment_type])
qed

lemma gi_exact_pterm_eta_eval:
  assumes contraction: "pcompatible_step peta_contract M N"
    and left_type: "has_ptype \<Gamma> M \<tau>"
    and right_type: "has_ptype \<Gamma> N \<tau>"
    and assignment_type: "pp_e_env_typed \<Gamma> g"
  shows "pp_e_eval C g (pterm_to_oterm M) =
    pp_e_eval C g (pterm_to_oterm N)"
proof -
  have decoded_step:
      "compatible_step eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
    by (rule iffD1[OF pcompatible_eta_string_iff contraction])
  have decoded_left: "\<Gamma> \<turnstile> pterm_to_oterm M : \<tau>"
    by (rule pterm_to_preserves_typing[OF left_type])
  have decoded_right: "\<Gamma> \<turnstile> pterm_to_oterm N : \<tau>"
    by (rule pterm_to_preserves_typing[OF right_type])
  show ?thesis
    by (rule pp_e_eta_compatible_eval[
      OF decoded_step decoded_left decoded_right assignment_type])
qed

theorem gi_exact_pterm_raw_conversion_eval:
  assumes conversion: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and assignment_type: "pp_e_env_typed \<Gamma> g"
  shows "pp_e_eval C g (pterm_to_oterm M) =
    pp_e_eval C g (pterm_to_oterm N)"
  using conversion assignment_type
proof (induction arbitrary: g rule: pbeta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule refl)
next
  case (Beta \<Gamma> M \<tau> N)
  show ?case
    by (rule gi_exact_pterm_beta_eval[OF Beta.hyps(3,1,2) Beta.prems])
next
  case (Eta \<Gamma> M \<tau> N)
  show ?case
    by (rule gi_exact_pterm_eta_eval[OF Eta.hyps(3,1,2) Eta.prems])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case
    by (rule trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

corollary gi_exact_pterm_signature_conversion_eval:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
    and assignment_type: "pp_e_env_typed \<Gamma> g"
  shows "pp_e_eval C g (pterm_to_oterm M) =
    pp_e_eval C g (pterm_to_oterm N)"
  by (rule gi_exact_pterm_raw_conversion_eval[
    OF pbeta_eta_equiv_in_signature_raw[OF conversion] assignment_type])

theorem gi_exact_named_denote_conversion:
  assumes rich: "sg_rich G"
    and left_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and right_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
    and raw_conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and assignment_type: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_named_denote C G g A = gi_exact_named_denote C G g B"
proof -
  obtain N where prefixes:
      "\<forall>m\<ge>N. pbeta_eta_equiv_in_signature \<Sigma> (source_prefix G m) \<tau>
        (book_named_to_pterm G A) (book_named_to_pterm G B)"
    using book_named_translation_conversion_eventual[
      OF rich raw_conversion left_language right_language]
    by (elim exE)
  have prefix_conversion:
      "pbeta_eta_equiv_in_signature \<Sigma> (source_prefix G N) \<tau>
        (book_named_to_pterm G A) (book_named_to_pterm G B)"
    by (rule mp[OF spec[where x=N, OF prefixes] order_refl])
  have prefix_assignment: "pp_e_env_typed (source_prefix G N) g"
    by (rule gi_exact_assignment_prefix[OF assignment_type])
  show ?thesis unfolding gi_exact_named_denote_def
    by (rule gi_exact_pterm_signature_conversion_eval[
      OF prefix_conversion prefix_assignment])
qed

section \<open>The book environment condition retains the intersection of free names\<close>

theorem gi_exact_named_environment:
  assumes rich: "sg_rich G"
    and left_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and right_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
    and raw_conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and left_assignment: "book_env_typed gi_exact_domain G g"
    and right_assignment: "book_env_typed gi_exact_domain G h"
    and agreement: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "gi_exact_named_denote C G g A = gi_exact_named_denote C G h B"
proof (rule gi_exact_environment_from_same_assignment_conversion[
    OF left_assignment right_assignment agreement])
  fix v
  assume assignment_type: "book_env_typed gi_exact_domain G v"
  show "gi_exact_named_denote C G v A = gi_exact_named_denote C G v B"
    by (rule gi_exact_named_denote_conversion[
      OF rich left_language right_language raw_conversion assignment_type])
qed

theorem gi_exact_book_environment_conditions:
  assumes rich: "sg_rich G"
  shows "book_environment_conditions gi_exact_domain gi_exact_app
    book_minimal_logical_type UNIV \<Sigma> G UNIV (gi_exact_named_denote C G)"
  by (unfold_locales;
    (rule gi_exact_app_closed | rule gi_exact_named_denote_type |
      rule gi_exact_named_denote_var | rule gi_exact_named_denote_app |
      rule gi_exact_named_environment[OF rich]); assumption)

theorem gi_exact_book_full_environment:
  assumes rich: "sg_rich G"
  shows "book_full_environment gi_exact_domain gi_exact_app
    book_minimal_logical_type UNIV \<Sigma> G (gi_exact_named_denote C G)"
proof -
  interpret Exact_Environment: book_environment_conditions
      gi_exact_domain gi_exact_app book_minimal_logical_type UNIV
      \<Sigma> G UNIV "gi_exact_named_denote C G"
    by (rule gi_exact_book_environment_conditions[OF rich])
  show ?thesis by unfold_locales
qed

corollary gi_exact_named_lambda_application:
  assumes rich: "sg_rich G"
    and body_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and assignment_type: "book_env_typed gi_exact_domain G g"
    and argument_member: "a \<in> gi_exact_domain (G n)"
  shows "gi_exact_app (G n) \<tau> (gi_exact_named_denote C G g (NLam n A)) a =
    gi_exact_named_denote C G (g(n := a)) A"
  by (rule book_full_environment.book_full_lambda_application[
    OF gi_exact_book_full_environment[OF rich]
      body_language assignment_type argument_member])

end

text \<open>
  The resulting interpretation satisfies Bacon's full-language environment
  condition on the exact appendix carriers, with declared-language
  endpoints and arbitrary typed raw βη conversions. Assignments need agree
  only on FV(A) ∩ FV(B), not on their union. The primitive logical truth
  clauses, native Classicist soundness, and equality of complete logical
  stocks remain separate obligations.
\<close>

end
