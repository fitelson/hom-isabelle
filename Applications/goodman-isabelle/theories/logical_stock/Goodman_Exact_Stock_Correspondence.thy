theory Goodman_Exact_Stock_Correspondence
  imports Goodman_Exact_Closed_Decoding
    Goodman_Integration_Exact_Applicative.Goodman_Exact_Denotation_Translation
begin

section \<open>Closed logical denotations in the native Goodman language\<close>

definition gi_exact_native_closed_den where
  "gi_exact_native_closed_den G A = gi_exact_goodman_denote pp_e_default_constants G
    (gi_exact_default_assignment G) A"

definition gi_exact_native_logical_denotations where
  "gi_exact_native_logical_denotations G \<sigma> =
    {x. \<exists>A. gb_closed_logical G \<sigma> A \<and> x = gi_exact_native_closed_den G A}"

definition gi_exact_native_logical_stock where
  "gi_exact_native_logical_stock G \<sigma> w x \<longleftrightarrow>
    x \<in> gi_exact_domain \<sigma> \<and>
    (\<exists>A. gb_closed_logical G \<sigma> A \<and>
      book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) \<sigma>
        x (gi_exact_native_closed_den G A))"

text \<open>
  These definitions quantify over ALL closed logical terms of the native
  named language, not just the image of gi_to_book. The first set consists
  of actual values. The second predicate is their saturation under the
  native model's local Leibniz identity at the specified world.
\<close>

lemma gi_exact_native_closed_den_decoded:
  "gb_closed_logical G \<sigma> A \<Longrightarrow>
    gi_exact_native_closed_den G A = pp_e_closed_den (gi_exact_decode G (gi_goodman_string_term A))"
  unfolding gi_exact_native_closed_den_def
  by (rule gi_goodman_closed_logical_decode_denotation(3); assumption)

lemma gi_exact_native_closed_den_member:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_native_closed_den G A \<in> gi_exact_domain \<sigma>"
  by (simp only: gi_exact_native_closed_den_decoded[OF logical] gi_exact_domain_member;
    rule pp_e_closed_den_in_domain[OF gi_goodman_closed_logical_decode_denotation(1)[OF logical]])

lemma gi_exact_native_closed_den_independent:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_goodman_denote C G g A = gi_exact_native_closed_den G A"
  by (simp only: gi_goodman_closed_logical_decode_denotation(3)[OF logical]
    gi_exact_native_closed_den_decoded[OF logical])

theorem gi_old_closed_logical_native_witness:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "\<exists>A. gb_closed_logical G \<sigma> A \<and> gi_exact_native_closed_den G A = pp_e_closed_den M"
proof -
  let ?B = "gi_to_book G [] (\<lambda>c \<tau>. c) M"
  let ?A = "gi_string_logical_to_goodman ?B"
  have admitted: "gi_constants_admitted (\<lambda>c \<tau>. c) (\<lambda>_. {}) M"
    using logical by (simp only: gi_logical_constants_iff)
  have b_logical: "gb_closed_logical G \<sigma> ?B"
    by (rule gi_closed_logical_translation[OF rich typed admitted])
  have a_logical: "gb_closed_logical G \<sigma> ?A"
    by (rule gi_empty_signature_name_map_closed_logical[OF b_logical])
  have b_signature: "named_in_signature (\<lambda>_. {}) ?B"
    using b_logical unfolding gb_closed_logical_def by (blast dest: book_language_signature)
  have roundtrip: "gi_goodman_string_term ?A = ?B"
    by (rule gi_logical_string_roundtrip[OF b_signature])
  have constants: "pp_e_constants pp_e_default_constants"
    by standard (simp add: pp_e_default_constants_def pp_e_default_in_domain)
  have forward: "gi_exact_named_denote pp_e_default_constants G (gi_exact_default_assignment G) ?B =
    pp_e_eval pp_e_default_constants (\<lambda>i. gi_exact_default_assignment G ([] ! i)) M"
    by (rule pp_e_constants.gi_exact_denotation_translation[
      OF constants rich typed _ _ gi_exact_default_assignment_typed]; simp)
  have same_value: "gi_exact_native_closed_den G ?A = pp_e_closed_den M"
    unfolding gi_exact_native_closed_den_def gi_exact_goodman_denote_def
    by (simp only: roundtrip forward gi_exact_old_closed_evaluation[OF typed logical])
  show ?thesis by (rule exI[where x="?A"], rule conjI[OF a_logical same_value])
qed

theorem gi_exact_logical_denotation_sets_equal:
  assumes rich: "sg_rich G"
  shows "gi_exact_native_logical_denotations G \<sigma> =
    {x. \<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M}"
proof (rule set_eqI)
  fix x
  show "x \<in> gi_exact_native_logical_denotations G \<sigma> \<longleftrightarrow>
    x \<in> {x. \<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M}"
  proof
    assume "x \<in> gi_exact_native_logical_denotations G \<sigma>"
    then obtain A where logical: "gb_closed_logical G \<sigma> A"
      and shape: "x = gi_exact_native_closed_den G A" unfolding gi_exact_native_logical_denotations_def by blast
    show "x \<in> {x. \<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M}"
      using gi_goodman_closed_logical_decode_denotation(1,2)[OF logical]
        gi_exact_native_closed_den_decoded[OF logical] shape by blast
  next
    assume "x \<in> {x. \<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M}"
    then obtain M where typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
      and shape: "x = pp_e_closed_den M" by blast
    obtain A where a_logical: "gb_closed_logical G \<sigma> A"
      and denotation: "gi_exact_native_closed_den G A = pp_e_closed_den M"
      using gi_old_closed_logical_native_witness[OF rich typed logical] by blast
    have x_eq: "x = gi_exact_native_closed_den G A"
      by (rule trans[OF shape denotation[symmetric]])
    show "x \<in> gi_exact_native_logical_denotations G \<sigma>"
      unfolding gi_exact_native_logical_denotations_def
      by (rule CollectI, rule exI[where x=A], rule conjI[OF a_logical x_eq])
  qed
qed

theorem gi_exact_native_stock_iff_original:
  assumes rich: "sg_rich G"
  shows "gi_exact_native_logical_stock G \<sigma> w x \<longleftrightarrow> pp_e_closed_logical_stock \<sigma> w x"
proof
  assume native: "gi_exact_native_logical_stock G \<sigma> w x"
  then obtain A where xm: "x \<in> gi_exact_domain \<sigma>" and logical: "gb_closed_logical G \<sigma> A"
    and related: "book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) \<sigma>
      x (gi_exact_native_closed_den G A)" unfolding gi_exact_native_logical_stock_def by blast
  have local: "pp_e_eqv \<sigma> w x (gi_exact_native_closed_den G A)"
    by (rule gi_exact_leibniz_implies_local_identity[OF related])
  show "pp_e_closed_logical_stock \<sigma> w x"
    using xm gi_goodman_closed_logical_decode_denotation(1,2)[OF logical]
      local gi_exact_native_closed_den_decoded[OF logical]
    unfolding pp_e_closed_logical_stock_def by (auto simp only: gi_exact_domain_member)
next
  assume original: "pp_e_closed_logical_stock \<sigma> w x"
  then obtain M where xm: "Elem x (pp_e_domain \<sigma>)" and typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M" and local: "pp_e_eqv \<sigma> w x (pp_e_closed_den M)"
    unfolding pp_e_closed_logical_stock_def by blast
  obtain A where a_logical: "gb_closed_logical G \<sigma> A"
    and denotation: "gi_exact_native_closed_den G A = pp_e_closed_den M"
    using gi_old_closed_logical_native_witness[OF rich typed logical] by blast
  have x_member: "x \<in> gi_exact_domain \<sigma>" using xm by (simp only: gi_exact_domain_member)
  have a_member: "gi_exact_native_closed_den G A \<in> gi_exact_domain \<sigma>"
    by (rule gi_exact_native_closed_den_member[OF a_logical])
  have related: "book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) \<sigma>
    x (gi_exact_native_closed_den G A)"
    by (rule gi_exact_local_identity_implies_leibniz[OF x_member a_member];
      simp only: denotation; rule local)
  show "gi_exact_native_logical_stock G \<sigma> w x"
    unfolding gi_exact_native_logical_stock_def using x_member a_logical related by blast
qed

corollary gi_exact_native_stock_independent_of_rich_names:
  "sg_rich G \<Longrightarrow> sg_rich H \<Longrightarrow>
    gi_exact_native_logical_stock G \<sigma> w x = gi_exact_native_logical_stock H \<sigma> w x"
  by (simp only: gi_exact_native_stock_iff_original)

text \<open>
  The raw denotation-set equality and the saturated-stock equivalence are
  both proved. The latter holds at every world and every represented type.
  Neither identifies every invariant value with a logical denotation,
  validates PP, or describes arbitrary enlarged Pure stocks.
\<close>

end
