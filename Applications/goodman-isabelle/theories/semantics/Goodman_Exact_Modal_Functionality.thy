theory Goodman_Exact_Modal_Functionality
  imports Goodman_Exact_Minimal_Model Goodman_Exact_Leibniz_Characterization
    "Bacon_Book_Classicism_Development.Bacon_Book_Full_Modalized_Functionality"
    "Bacon_Book_Classicism_Development.Bacon_Book_Box_Truth"
begin

section \<open>Future pointwise identity determines exact function identity\<close>

lemma gi_exact_future_pointwise_identity:
  assumes function_member: "f \<in> gi_exact_domain (Arr \<sigma> \<tau>)"
    and other_member: "h \<in> gi_exact_domain (Arr \<sigma> \<tau>)"
    and pointwise: "\<And>v x. prefix w v \<Longrightarrow> x \<in> gi_exact_domain \<sigma> \<Longrightarrow>
      pp_e_eqv \<tau> v (f \<acute> x) (h \<acute> x)"
  shows "pp_e_eqv (Arr \<sigma> \<tau>) w f h"
proof -
  have exact_f: "Elem f (pp_e_domain (Arr \<sigma> \<tau>))"
    using function_member by (simp only: gi_exact_domain_member)
  have exact_h: "Elem h (pp_e_domain (Arr \<sigma> \<tau>))"
    using other_member by (simp only: gi_exact_domain_member)
  show ?thesis
  proof (simp only: pp_e_eqv.simps, intro allI impI)
    fix v x y
    assume future: "prefix w v"
      and exact_x: "Elem x (pp_e_domain \<sigma>)"
      and exact_y: "Elem y (pp_e_domain \<sigma>)"
      and related_arguments: "pp_e_eqv \<sigma> v x y"
    have x_member: "x \<in> gi_exact_domain \<sigma>"
      using exact_x by (simp only: gi_exact_domain_member)
    have same_input: "pp_e_eqv \<tau> v (f \<acute> x) (h \<acute> x)"
      by (rule pointwise[OF future x_member])
    have reflexive_h: "pp_e_eqv (Arr \<sigma> \<tau>) v h h"
      by (rule pp_e_eqv_reflexive[OF exact_h])
    have changed_input: "pp_e_eqv \<tau> v (h \<acute> x) (h \<acute> y)"
      by (rule pp_e_app_respects[OF reflexive_h exact_x exact_y related_arguments])
    have fx_member: "Elem (f \<acute> x) (pp_e_domain \<tau>)"
      by (rule pp_e_app_closed[OF exact_f exact_x])
    have hx_member: "Elem (h \<acute> x) (pp_e_domain \<tau>)"
      by (rule pp_e_app_closed[OF exact_h exact_x])
    have hy_member: "Elem (h \<acute> y) (pp_e_domain \<tau>)"
      by (rule pp_e_app_closed[OF exact_h exact_y])
    show "pp_e_eqv \<tau> v (f \<acute> x) (h \<acute> y)"
      by (rule pp_e_eqv_transitive[
        OF fx_member hx_member hy_member same_input changed_input])
  qed
qed

section \<open>Native identity, quantifiers, and necessity at an exact world\<close>

context pp_e_constants
begin

lemma gi_exact_named_leibniz_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and left_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and right_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_leibniz G \<sigma> A B)) w \<longleftrightarrow>
    pp_e_eqv \<sigma> w (gi_exact_named_denote C G g A) (gi_exact_named_denote C G g B)"
proof -
  have left_member: "gi_exact_named_denote C G g A \<in> gi_exact_domain \<sigma>"
    by (rule gi_exact_named_denote_type[OF left_language typed])
  have right_member: "gi_exact_named_denote C G g B \<in> gi_exact_domain \<sigma>"
    by (rule gi_exact_named_denote_type[OF right_language typed])
  have native:
      "gi_exact_valuation w (gi_exact_named_denote C G g (book_leibniz G \<sigma> A B)) =
        book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) \<sigma>
          (gi_exact_named_denote C G g A) (gi_exact_named_denote C G g B)"
    by (rule book_full_minimal_model.book_leibniz_truth[
      OF gi_exact_book_minimal_model[OF rich] rich typed left_language right_language])
  show ?thesis using native
    apply (simp only: gi_exact_leibniz_iff_local_identity[OF left_member right_member])
    by (simp only: gi_exact_valuation_def)
qed

lemma gi_exact_named_imp_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and left_language: "book_theory_formula \<Sigma> G A"
    and right_language: "book_theory_formula \<Sigma> G B"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_imp A B)) w \<longleftrightarrow>
    (pp_e_holds (gi_exact_named_denote C G g A) w \<longrightarrow>
      pp_e_holds (gi_exact_named_denote C G g B) w)"
  using book_full_minimal_model.book_imp_truth[
    OF gi_exact_book_minimal_model[OF rich] typed left_language right_language]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_all_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and body_language: "book_theory_formula \<Sigma> G A"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_all G n A)) w \<longleftrightarrow>
    (\<forall>a\<in>gi_exact_domain (G n). pp_e_holds (gi_exact_named_denote C G (g(n := a)) A) w)"
  using book_full_minimal_model.book_all_truth[
    OF gi_exact_book_minimal_model[OF rich] typed body_language]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_top_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_top G)) w"
  using book_full_minimal_model.book_top_true[
    OF gi_exact_book_minimal_model[where \<Sigma>="\<lambda>_. {}", OF rich] rich typed]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_box_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and term_language: "book_theory_formula \<Sigma> G P"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_box G P)) w \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> pp_e_holds (gi_exact_named_denote C G g P) v)"
proof -
  have top_language: "book_theory_formula \<Sigma> G (book_top G)"
    by (rule book_top_language[OF rich])
  have term_member: "gi_exact_named_denote C G g P \<in> gi_exact_domain Prop"
    by (rule gi_exact_named_denote_type[OF term_language typed])
  have top_member: "gi_exact_named_denote C G g (book_top G) \<in> gi_exact_domain Prop"
    by (rule gi_exact_named_denote_type[OF top_language typed])
  have native:
      "gi_exact_valuation w (gi_exact_named_denote C G g (book_box G P)) =
        book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) Prop
          (gi_exact_named_denote C G g P) (gi_exact_named_denote C G g (book_top G))"
    by (rule book_full_minimal_model.book_box_truth[
      OF gi_exact_book_minimal_model[OF rich] rich typed term_language])
  have local:
      "pp_e_holds (gi_exact_named_denote C G g (book_box G P)) w =
        pp_e_eqv Prop w (gi_exact_named_denote C G g P)
          (gi_exact_named_denote C G g (book_top G))"
    using native
    apply (simp only: gi_exact_leibniz_iff_local_identity[OF term_member top_member])
    by (simp only: gi_exact_valuation_def)
  have top_everywhere: "pp_e_holds (gi_exact_named_denote C G g (book_top G)) v" for v
    by (rule gi_exact_named_top_holds[OF rich typed])
  show ?thesis by (simp only: local pp_e_eqv.simps top_everywhere; simp)
qed

section \<open>Modalized Functionality at every represented arrow type\<close>

theorem gi_exact_MF_body_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_MF_body G \<sigma> \<tau>)) w"
proof -
  let ?S = "(\<lambda>_. {}) :: string ssignature"
  let ?l = "book_MF_left G \<sigma> \<tau>"
  let ?r = "book_MF_right G \<sigma> \<tau>"
  let ?n = "book_MF_argument G \<sigma> \<tau>"
  let ?F = "NVar ?l :: string book_named_term"
  let ?H = "NVar ?r :: string book_named_term"
  let ?x = "NVar ?n :: string book_named_term"
  let ?point = "book_leibniz G \<tau> (NApp ?F ?x) (NApp ?H ?x)"
  let ?all = "book_all G ?n ?point"
  let ?antecedent = "book_box G ?all"
  let ?consequent = "book_leibniz G (Arr \<sigma> \<tau>) ?F ?H"
  have lt: "G ?l = Arr \<sigma> \<tau>" by (rule book_MF_names_type(1)[OF rich])
  have rt: "G ?r = Arr \<sigma> \<tau>" by (rule book_MF_names_type(2)[OF rich])
  have nt: "G ?n = \<sigma>" by (rule book_MF_names_type(3)[OF rich])
  have name_distinct: "distinct [?l, ?r, ?n]" by (rule book_MF_names_distinct[OF rich])
  have ln: "?l \<noteq> ?n" and rn: "?r \<noteq> ?n" using name_distinct by auto
  have fl: "book_in_language book_minimal_logical_type UNIV ?S G ?F (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule lt[symmetric])
  have hl: "book_in_language book_minimal_logical_type UNIV ?S G ?H (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff; rule rt[symmetric])
  have xl: "book_in_language book_minimal_logical_type UNIV ?S G ?x \<sigma>"
    by (simp only: book_language_var_iff; rule nt[symmetric])
  have fxl: "book_in_language book_minimal_logical_type UNIV ?S G (NApp ?F ?x) \<tau>"
    by (rule book_language_App[OF fl xl])
  have hxl: "book_in_language book_minimal_logical_type UNIV ?S G (NApp ?H ?x) \<tau>"
    by (rule book_language_App[OF hl xl])
  have point_language: "book_theory_formula ?S G ?point"
    by (rule book_leibniz_language[OF rich fxl hxl])
  have all_language: "book_theory_formula ?S G ?all"
    by (rule book_all_language[OF point_language])
  have antecedent_language: "book_theory_formula ?S G ?antecedent"
    by (rule book_box_language[OF rich all_language])
  have consequent_language: "book_theory_formula ?S G ?consequent"
    by (rule book_leibniz_language[OF rich fl hl])
  have f_member: "g ?l \<in> gi_exact_domain (Arr \<sigma> \<tau>)"
    using book_env_at[OF typed, where n="?l"] by (simp only: lt)
  have h_member: "g ?r \<in> gi_exact_domain (Arr \<sigma> \<tau>)"
    using book_env_at[OF typed, where n="?r"] by (simp only: rt)
  have implication:
      "pp_e_holds (gi_exact_named_denote C G g ?antecedent) w \<longrightarrow>
        pp_e_holds (gi_exact_named_denote C G g ?consequent) w"
  proof
    assume boxed: "pp_e_holds (gi_exact_named_denote C G g ?antecedent) w"
    have future_all: "\<forall>v. prefix w v \<longrightarrow>
        pp_e_holds (gi_exact_named_denote C G g ?all) v"
      by (rule iffD1[OF gi_exact_named_box_holds[OF rich typed all_language] boxed])
    have pointwise:
        "pp_e_eqv \<tau> v (g ?l \<acute> a) (g ?r \<acute> a)"
      if future: "prefix w v" and a_member: "a \<in> gi_exact_domain \<sigma>" for v a
    proof -
      have all_at_v: "pp_e_holds (gi_exact_named_denote C G g ?all) v"
        using future_all future by blast
      have named_member: "a \<in> gi_exact_domain (G ?n)"
        using a_member by (simp only: nt)
      have update_type: "book_env_typed gi_exact_domain G (g(?n := a))"
        by (rule book_env_update[OF typed named_member])
      have all_values: "\<forall>x\<in>gi_exact_domain (G ?n).
          pp_e_holds (gi_exact_named_denote C G (g(?n := x)) ?point) v"
        by (rule iffD1[OF gi_exact_named_all_holds[OF rich typed point_language] all_at_v])
      have point_at_a: "pp_e_holds (gi_exact_named_denote C G (g(?n := a)) ?point) v"
        by (rule bspec[OF all_values named_member])
      have local_outputs:
          "pp_e_eqv \<tau> v
            (gi_exact_named_denote C G (g(?n := a)) (NApp ?F ?x))
            (gi_exact_named_denote C G (g(?n := a)) (NApp ?H ?x))"
        by (rule iffD1[OF gi_exact_named_leibniz_holds[
          OF rich update_type fxl hxl] point_at_a])
      have left_value:
          "gi_exact_named_denote C G (g(?n := a)) (NApp ?F ?x) = g ?l \<acute> a"
        by (simp add: gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=\<tau>]
            gi_exact_named_denote_var ln)
      have right_value:
          "gi_exact_named_denote C G (g(?n := a)) (NApp ?H ?x) = g ?r \<acute> a"
        by (simp add: gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=\<tau>]
            gi_exact_named_denote_var rn)
      show ?thesis using local_outputs by (simp only: left_value right_value)
    qed
    have local_functions: "pp_e_eqv (Arr \<sigma> \<tau>) w (g ?l) (g ?r)"
      by (rule gi_exact_future_pointwise_identity[OF f_member h_member pointwise])
    have named_functions:
        "pp_e_eqv (Arr \<sigma> \<tau>) w (gi_exact_named_denote C G g ?F)
          (gi_exact_named_denote C G g ?H)"
      using local_functions by (simp only: gi_exact_named_denote_var)
    show "pp_e_holds (gi_exact_named_denote C G g ?consequent) w"
      by (rule iffD2[OF gi_exact_named_leibniz_holds[OF rich typed fl hl] named_functions])
  qed
  have implication_truth:
      "pp_e_holds (gi_exact_named_denote C G g (book_imp ?antecedent ?consequent)) w =
        (pp_e_holds (gi_exact_named_denote C G g ?antecedent) w \<longrightarrow>
          pp_e_holds (gi_exact_named_denote C G g ?consequent) w)"
    by (rule gi_exact_named_imp_holds[OF rich typed antecedent_language consequent_language])
  show ?thesis unfolding book_MF_body_def
    using implication_truth implication by blast
qed

theorem gi_exact_MF_axiom_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_MF_axiom G \<sigma> \<tau>)) w"
proof -
  let ?S = "(\<lambda>_. {}) :: string ssignature"
  let ?l = "book_MF_left G \<sigma> \<tau>"
  let ?r = "book_MF_right G \<sigma> \<tau>"
  let ?body = "book_MF_body G \<sigma> \<tau>"
  have body_language: "book_theory_formula ?S G ?body"
    by (rule book_MF_body_language[OF rich])
  have inner_language: "book_theory_formula ?S G (book_all G ?r ?body)"
    by (rule book_all_language[OF body_language])
  show ?thesis
    unfolding book_MF_axiom_def
  proof (simp only: gi_exact_named_all_holds[OF rich typed inner_language], intro ballI)
    fix f
    assume f_member: "f \<in> gi_exact_domain (G ?l)"
    have first_type: "book_env_typed gi_exact_domain G (g(?l := f))"
      by (rule book_env_update[OF typed f_member])
    show "pp_e_holds (gi_exact_named_denote C G (g(?l := f)) (book_all G ?r ?body)) w"
    proof (simp only: gi_exact_named_all_holds[OF rich first_type body_language], intro ballI)
      fix h
      assume h_member: "h \<in> gi_exact_domain (G ?r)"
      have second_type: "book_env_typed gi_exact_domain G ((g(?l := f))(?r := h))"
        by (rule book_env_update[OF first_type h_member])
      show "pp_e_holds (gi_exact_named_denote C G ((g(?l := f))(?r := h)) ?body) w"
        by (rule gi_exact_MF_body_holds[OF rich second_type])
    qed
  qed
qed

end

text \<open>
  This proves MFστ at every world for every represented σ and τ, including
  result types ending in e. The proof uses the exact restricted carriers:
  future pointwise identity is combined with each function's respect for
  local identity. Necessity ranges over the prefix future, and quantifiers
  range over precisely the corresponding exact domains. It does not use
  an unproved global-validity predicate or infer arbitrary full function
  spaces from a shallow HOL representation.
\<close>

end
