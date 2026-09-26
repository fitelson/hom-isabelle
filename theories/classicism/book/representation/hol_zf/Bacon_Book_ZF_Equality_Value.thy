theory Bacon_Book_ZF_Equality_Value
  imports Bacon_Book_ZF_Application_Naturality
begin

context book_full_C_coded_frame
begin

lemma full_ZF_closed_value_representation:
  assumes admitted: "full_ZF_admitted w" and member: "a \<in> explode (full_ZF_D \<sigma> w)"
  shows "\<exists>A\<in>book_closed_terms (fst w) G \<sigma>. a = full_ZF_closed_value w \<sigma> A"
  using member unfolding full_ZF_D_elements[OF admitted] book_C_identity_domain_def full_ZF_closed_value_def by auto

definition full_ZF_equality_value where
  "full_ZF_equality_value w \<sigma> = full_ZF_closed_value w (Arr \<sigma> (Arr \<sigma> Prop)) (book_leibniz_const G \<sigma>)"

lemma full_ZF_equality_closed_term:
  "book_leibniz_const G \<sigma> \<in> book_closed_terms (fst w) G (Arr \<sigma> (Arr \<sigma> Prop))"
  by (rule book_closed_termsI[OF book_leibniz_const_language[OF rich] book_leibniz_const_closed])

theorem full_ZF_equality_value_type:
  assumes admitted: "full_ZF_admitted w"
  shows "full_ZF_equality_value w \<sigma> \<in> explode (full_ZF_D (Arr \<sigma> (Arr \<sigma> Prop)) w)"
  unfolding full_ZF_equality_value_def by (rule full_ZF_closed_value_type[OF admitted full_ZF_equality_closed_term])

theorem full_ZF_equality_value_natural:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
  shows "full_ZF_i (Arr \<sigma> (Arr \<sigma> Prop)) w v (full_ZF_equality_value w \<sigma>) = full_ZF_equality_value v \<sigma>"
  unfolding full_ZF_equality_value_def
  by (rule full_ZF_closed_value_natural[OF ww vw access full_ZF_equality_closed_term])

theorem full_ZF_equality_value_truth:
  assumes ww: "w \<in> worlds" and am: "a \<in> explode (full_ZF_D \<sigma> w)"
    and bm: "b \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_value_truth w
    (full_ZF_app w \<sigma> Prop (full_ZF_app w \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value w \<sigma>) a) b) = (a = b)"
proof -
  obtain A where ac: "A \<in> book_closed_terms (fst w) G \<sigma>" and ae: "a = full_ZF_closed_value w \<sigma> A"
    using full_ZF_closed_value_representation[OF worlds_admitted[OF ww] am] by blast
  obtain C where cc: "C \<in> book_closed_terms (fst w) G \<sigma>" and ce: "b = full_ZF_closed_value w \<sigma> C"
    using full_ZF_closed_value_representation[OF worlds_admitted[OF ww] bm] by blast
  let ?E = "book_leibniz_const G \<sigma>"
  let ?R = "book_leibniz G \<sigma> A C"
  have ec: "?E \<in> book_closed_terms (fst w) G (Arr \<sigma> (Arr \<sigma> Prop))"
    by (rule full_ZF_equality_closed_term)
  have partial: "NApp ?E A \<in> book_closed_terms (fst w) G (Arr \<sigma> Prop)"
    by (rule book_closed_terms_App[OF ec ac])
  have rc: "?R \<in> book_closed_terms (fst w) G Prop"
    unfolding book_leibniz_def by (rule book_closed_terms_App[OF partial cc])
  have evaluated: "full_ZF_app w \<sigma> Prop (full_ZF_app w \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value w \<sigma>) a) b =
    full_ZF_closed_value w Prop ?R"
    by (simp only: full_ZF_equality_value_def ae ce full_ZF_closed_value_application[OF ww ec ac]
      full_ZF_closed_value_application[OF ww partial cc] book_leibniz_def)
  obtain g where typed: "book_env_typed (\<lambda>\<tau>. explode (full_ZF_D \<tau> w)) G g"
    using book_total_assignment_exists[where D="\<lambda>\<tau>. explode (full_ZF_D \<tau> w)" and G=G,
      OF full_ZF_domains_nonempty[OF ww]] by blast
  have truth: "full_ZF_value_truth w (full_ZF_denote w g ?R) = (full_ZF_denote w g A = full_ZF_denote w g C)"
    by (rule full_ZF_identity_truth[OF ww book_closed_terms_language[OF ac] book_closed_terms_language[OF cc] typed])
  have result_truth: "full_ZF_value_truth w (full_ZF_closed_value w Prop ?R) = (a = b)"
    using truth by (simp only: full_ZF_denote_closed_value[OF rc] full_ZF_denote_closed_value[OF ac]
      full_ZF_denote_closed_value[OF cc] ae ce)
  show ?thesis by (simp only: evaluated; rule result_truth)
qed

end

text \<open>
  The equality value is the image of the literal closed Leibniz
  operator. It belongs to the full function domain, commutes with
  counterparts, and tests actual equality on every typed pair.
  Its truth calculation is derived by closed representatives from
  the all-assignment identity theorem; it is not a stipulated
  semantic equality constant. The whole future truth set is next.
\<close>

end
