theory Goodman_Exact_Goodman_Translation
  imports Goodman_Exact_Denotation_Translation
begin

section \<open>The typed constant map commutes with the constructor translation\<close>

lemma gi_typed_name_map_or:
  "book_typed_name_map \<rho> (book_or G A B) =
    book_or G (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (simp only: book_or_def book_or_const_def book_typed_name_map.simps
      book_typed_name_map_imp book_typed_name_map_not)

lemma gi_typed_name_map_exists:
  "book_typed_name_map \<rho> (book_exists G n A) =
    book_exists G n (book_typed_name_map \<rho> A)"
  by (simp only: book_exists_def book_exists_const_def book_typed_name_map.simps
      book_typed_name_map_not)

theorem gi_typed_name_map_translation:
  "book_typed_name_map \<rho> (gi_to_book G ns k M) =
    gi_to_book G ns (\<lambda>c \<tau>. \<rho> \<tau> (k c \<tau>)) M"
  by (induction M arbitrary: ns)
    (simp_all add: Let_def book_C_typed_rename_leibniz book_typed_name_map_not
      book_C_typed_rename_and gi_typed_name_map_or book_typed_name_map_imp
      book_typed_name_map_all gi_typed_name_map_exists)

lemma gi_translation_constant_agreement:
  assumes agreement: "\<And>c \<tau>. c \<in> consts_of M \<Longrightarrow> k c \<tau> = j c \<tau>"
  shows "gi_to_book G ns k M = gi_to_book G ns j M"
  using agreement
  by (induction M arbitrary: ns) (auto simp: Let_def)

section \<open>Roundtrip on the actual Pure/Fun source vocabulary\<close>

text \<open>
  The guard below is the existing consts_of predicate restricted to the
  two original names. It is not the target admission predicate: a map into
  the two-element Goodman name type can collapse a third source name.
  Therefore target admission alone cannot establish a source-name roundtrip.

  The name equation is valid at every occurrence type. Language membership
  in gb_signature is a separate condition, since that signature declares
  Pure and Fun only at predicate types. This syntactic theorem does not
  remove that condition from the native proof or model interfaces.
\<close>

lemma gi_goodman_string_name_recovers:
  assumes names: "gi_goodman_names k" and permitted: "c \<in> {pp_pure_name, pp_fun_name}"
  shows "gi_goodman_string_name (k c \<tau>) = c"
  using names permitted unfolding gi_goodman_names_def by auto

theorem gi_goodman_translation_string_roundtrip:
  assumes names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
  shows "gi_goodman_string_term (gi_to_book G ns k M) =
    gi_to_book G ns (\<lambda>c \<tau>. c) M"
proof -
  have mapped: "gi_goodman_string_term (gi_to_book G ns k M) =
      gi_to_book G ns (\<lambda>c \<tau>. gi_goodman_string_name (k c \<tau>)) M"
    by (rule gi_typed_name_map_translation)
  have agreement: "gi_goodman_string_name (k c \<tau>) = c"
    if occurring: "c \<in> consts_of M" for c \<tau>
  proof -
    have permitted: "c \<in> {pp_pure_name, pp_fun_name}"
      by (rule subsetD[OF vocabulary occurring])
    show ?thesis by (rule gi_goodman_string_name_recovers[OF names permitted])
  qed
  have unchanged:
      "gi_to_book G ns (\<lambda>c \<tau>. gi_goodman_string_name (k c \<tau>)) M =
        gi_to_book G ns (\<lambda>c \<tau>. c) M"
    by (rule gi_translation_constant_agreement; rule agreement; assumption)
  show ?thesis by (rule trans[OF mapped unchanged])
qed

section \<open>Exact value preservation for native Goodman translations\<close>

context pp_e_constants
begin

theorem gi_exact_goodman_denotation_translation:
  assumes rich: "sg_rich G" and term_type: "\<Gamma> \<turnstile> M : \<tau>"
    and chart: "map G ns = \<Gamma>" and chart_distinct: "distinct ns"
    and typed: "book_env_typed gi_exact_domain G g"
    and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
  shows "gi_exact_goodman_denote C G g (gi_to_book G ns k M) =
    pp_e_eval C (\<lambda>i. g (ns ! i)) M"
  unfolding gi_exact_goodman_denote_def
  by (simp only: gi_goodman_translation_string_roundtrip[OF names vocabulary];
    rule gi_exact_denotation_translation[OF rich term_type chart chart_distinct typed])

corollary gi_exact_goodman_closed_denotation_translation:
  assumes rich: "sg_rich G" and term_type: "[] \<turnstile> M : \<tau>"
    and typed: "book_env_typed gi_exact_domain G g"
    and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
  shows "gi_exact_goodman_denote C G g (gi_to_book G [] k M) =
    pp_e_eval C pp_e_closed_env M"
proof -
  have translated: "gi_exact_goodman_denote C G g (gi_to_book G [] k M) =
      pp_e_eval C (\<lambda>i. g ([] ! i)) M"
    by (rule gi_exact_goodman_denotation_translation[
      OF rich term_type _ _ typed names vocabulary]; simp)
  have closed_value: "pp_e_eval C (\<lambda>i. g ([] ! i)) M = pp_e_eval C pp_e_closed_env M"
  proof (rule gi_exact_eval_agrees_on_context[
      OF term_type pp_e_empty_env_typed pp_e_empty_env_typed])
    fix n \<sigma>
    assume impossible: "lookup [] n = Some \<sigma>"
    then show "g ([] ! n) = pp_e_closed_env n" by (simp add: lookup_def)
  qed
  show ?thesis by (rule trans[OF translated closed_value])
qed

end

text \<open>
  Both semantic conclusions are equality of exact values at the displayed
  type, not only truth equivalence. Constants retain the pp_e_constants
  typing premise, charts retain their typing/distinctness conditions, and
  the source vocabulary restriction remains explicit. The closed corollary
  also verifies independence of the unused de Bruijn assignment rather
  than identifying two total assignments outside the term's context.
\<close>

end
