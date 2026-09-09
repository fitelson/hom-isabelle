theory Bacon_Book_Disjunction_Encoding_Environment
  imports Bacon_Book_Disjunction_Raw_Conversion_Transport Bacon_Book_Full_Environment
begin

section \<open>Pulling an interpretation back along the disjunction encoding\<close>

text \<open>
  Put J′g(A)=Jg(enc(A)). If J is a full conjunction-language interpretation
  of the tagged signature, then J′ is a full interpretation of the
  native vocabulary with primitive ∧ and ∨. The domains, typed application,
  and assignments are unchanged. Source role: Definition 14.13, p.302,
  with the primitive distinction of §5.2, p.104.

  Only the new ∨ symbol maps to the designated atomic constant, not a
  λ-expression; inherited ∧ stays logical. Encoding preserves type,
  declared names and free variables. Raw conversion uses the rich-stock
  transport theorem. The intersection environment condition is retained
  on both typed assignments. No disjunction truth, valuation, fixed
  axiom scheme, richer-model existence, or Functionality is assumed.
\<close>

definition book_disj_encoded_denote ::
  "((nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> 'v) \<Rightarrow>
    (nat \<Rightarrow> 'v) \<Rightarrow> 'c book_disj_term \<Rightarrow> 'v" where
  "book_disj_encoded_denote J g A = J g (book_disj_encode A)"

lemma book_disj_encoded_denote_symbols:
  "book_disj_encoded_denote J g (NLogical (BDConjunction l)) = J g (NLogical l)"
  "book_disj_encoded_denote J g (NLogical BDOr) = J g (NConst (Inr ()) book_disj_type)"
  by (simp_all add: book_disj_encoded_denote_def)

context
  fixes \<Sigma> :: "'c ssignature" and G :: sgcontext
    and D :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> 'v"
  assumes target_environment:
    "book_full_environment D app book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G J"
begin

interpretation Target: book_full_environment D app book_conj_logical_type UNIV
  "book_disj_target_signature \<Sigma>" G J
  by (rule target_environment)

lemma book_disj_encoded_type:
  assumes language: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<tau>"
    and typed: "book_env_typed D G g"
  shows "book_disj_encoded_denote J g A \<in> D \<tau>"
  unfolding book_disj_encoded_denote_def
  by (rule Target.denote_type[OF UNIV_I book_disj_encode_language[OF language] typed])

lemma book_disj_encoded_var:
  assumes typed: "book_env_typed D G g"
  shows "book_disj_encoded_denote J g (NVar n) = g n"
  by (simp only: book_disj_encoded_denote_def book_disj_encode.simps;
    rule Target.denote_var[OF UNIV_I typed])

lemma book_disj_encoded_app:
  assumes head: "book_in_language book_disj_logical_type UNIV \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<sigma>"
    and typed: "book_env_typed D G g"
  shows "book_disj_encoded_denote J g (NApp F A) =
    app \<sigma> \<tau> (book_disj_encoded_denote J g F) (book_disj_encoded_denote J g A)"
  by (simp only: book_disj_encoded_denote_def book_disj_encode.simps;
    rule Target.denote_app[OF UNIV_I UNIV_I UNIV_I book_disj_encode_language[OF head]
      book_disj_encode_language[OF argument] typed])

lemma book_disj_encoded_locality:
  assumes language: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<tau>"
    and first: "book_env_typed D G g" and second: "book_env_typed D G h"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "book_disj_encoded_denote J g A = book_disj_encoded_denote J h A"
proof (unfold book_disj_encoded_denote_def,
    rule Target.book_denote_locality[OF UNIV_I book_disj_encode_language[OF language] first second])
  fix n
  assume free: "n \<in> named_fv (book_disj_encode A)"
  have original: "n \<in> named_fv A" using free by (simp only: book_disj_encode_fv)
  show "g n = h n" by (rule agree[OF original])
qed

lemma book_disj_encoded_conversion:
  assumes rich: "sg_rich G"
    and left: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<tau>"
    and right: "book_in_language book_disj_logical_type UNIV \<Sigma> G B \<tau>"
    and conversion: "named_raw_beta_eta book_disj_logical_type G \<tau> A B"
    and typed: "book_env_typed D G g"
  shows "book_disj_encoded_denote J g A = book_disj_encoded_denote J g B"
  unfolding book_disj_encoded_denote_def
  by (rule Target.book_denote_conversion[OF UNIV_I UNIV_I book_disj_encode_language[OF left]
    book_disj_encode_language[OF right] book_disj_encode_raw_conversion[OF rich conversion] typed])

lemma book_disj_encoded_environment:
  assumes rich: "sg_rich G"
    and left: "book_in_language book_disj_logical_type UNIV \<Sigma> G A \<tau>"
    and right: "book_in_language book_disj_logical_type UNIV \<Sigma> G B \<tau>"
    and conversion: "named_raw_beta_eta book_disj_logical_type G \<tau> A B"
    and first: "book_env_typed D G g" and second: "book_env_typed D G h"
    and agree: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "book_disj_encoded_denote J g A = book_disj_encoded_denote J h B"
proof (unfold book_disj_encoded_denote_def,
    rule Target.environment[OF UNIV_I UNIV_I book_disj_encode_language[OF left]
      book_disj_encode_language[OF right] book_disj_encode_raw_conversion[OF rich conversion] first second])
  fix n
  assume overlap: "n \<in> named_fv (book_disj_encode A) \<inter> named_fv (book_disj_encode B)"
  have original: "n \<in> named_fv A \<inter> named_fv B" using overlap by (simp only: book_disj_encode_fv)
  show "g n = h n" by (rule agree[OF original])
qed

theorem book_disj_encoded_full_environment:
  assumes rich: "sg_rich G"
  shows "book_full_environment D app book_disj_logical_type UNIV \<Sigma> G (book_disj_encoded_denote J)"
  apply unfold_locales
     apply (rule book_disj_encoded_type; assumption)
    apply (rule book_disj_encoded_var; assumption)
   apply (rule book_disj_encoded_app; assumption)
  apply (rule book_disj_encoded_environment[OF rich]; assumption)
  done

end

end
