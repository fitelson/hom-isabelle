theory Bacon_Source_Relational_Intensional_Reverse
  imports Bacon_Source_Relational_Intension_Tail Bacon_Source_Relational_Intensional_Forward
begin

section \<open>Uniform separation by induction on relation arity\<close>

text \<open>
  In a quasi-Fregean and quasi-functional R category, equal relation
  intensions imply equal relation values. Source: Bacon–Dorr
  Definition 3.11 and footnote 72, pp.50–51.

  Induction is uniform over EVERY object M. At arity zero,
  intension equality is truth-profile equality, so quasi-Fregeanness
  applies. At positive arity, each h:M→N and each a∈Nσ yield
  equal tail intensions. The induction hypothesis at N makes the
  corresponding application values equal. Their normalized applicative
  profiles are therefore equal, and quasi-functionality applies at M.

  The hypotheses specify a selected R subcategory. Neither canonical
  object normalization nor the full collection of homomorphisms is
  required. No valuation-preservation, model-existence, fullness or
  unguarded F-type decomposition is used.
\<close>

lemma paper_R_intension_separates_from_quasi:
  fixes \<Sigma> :: "'c ssignature" and d e :: 'v
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and fregean: "paper_bbk_quasi_fregean_on Obj Arrows"
    and functional: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and types: "list_all paper_R_type \<sigma>s"
    and object: "M \<in> Obj"
    and dm: "d \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    and em: "e \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    and equal: "paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d =
      paper_R_intension_on \<Sigma> G Arrows M \<sigma>s e"
  shows "d = e"
  using types object dm em equal
proof (induction \<sigma>s arbitrary: M d e)
  case Nil
  have dp: "d \<in> paper_bbk_domain M Prop" using Nil.prems(3) by (simp only: paper_type_vector.simps)
  have ep: "e \<in> paper_bbk_domain M Prop" using Nil.prems(4) by (simp only: paper_type_vector.simps)
  have profiles: "paper_bbk_truth_profile_on Arrows M d = paper_bbk_truth_profile_on Arrows M e"
    by (rule iffD1[OF paper_R_intension_zeroary_eq_iff Nil.prems(5)])
  have injective: "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
    using fregean Nil.prems(2) unfolding paper_bbk_quasi_fregean_on_def by blast
  show ?case by (rule inj_onD[OF injective profiles dp ep])
next
  case (Cons \<sigma> \<sigma>s)
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  have tail_types: "list_all paper_R_type \<sigma>s" using Cons.prems(1) by simp
  have vector_type: "paper_R_type (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
    by (rule iffD2[OF paper_R_vector_to_Prop_iff Cons.prems(1)])
  have rt: "paper_R_type (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using vector_type by (simp only: paper_type_vector.simps)
  have dt: "d \<in> paper_bbk_domain M (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using Cons.prems(3) by (simp only: paper_type_vector.simps)
  have et: "e \<in> paper_bbk_domain M (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using Cons.prems(4) by (simp only: paper_type_vector.simps)
  let ?P = "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<sigma>s Prop)"
  let ?E = "paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain)
    (\<lambda>N. paper_bbk_domain N \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
    (\<lambda>N. paper_bbk_domain N (paper_type_vector \<sigma>s Prop))
    (\<lambda>h. paper_arrow_map h (paper_type_vector \<sigma>s Prop)) M"
  have df: "?P d \<in> ?E" by (rule paper_R_app_profile_on_exponential[OF category rt dt])
  have ef: "?P e \<in> ?E" by (rule paper_R_app_profile_on_exponential[OF category rt et])
  have profiles: "?P d = ?P e"
  proof (rule paper_exponential_fiber_ext[OF df ef])
    fix h :: "('c,'v) paper_R_bbk_arrow" and a :: 'v
    assume pair: "(h,a) \<in> paper_exponential_pairs Arrows paper_arrow_source paper_arrow_target
      (\<lambda>N. paper_bbk_domain N \<sigma>) M"
    have ha: "h \<in> Arrows" and source: "paper_arrow_source h = M"
      and am: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      using pair by (auto simp only: paper_exponential_pairs_iff)
    have target_object: "paper_arrow_target h \<in> Obj" by (rule Category.target_object[OF ha])
    have dp: "?P d (h,a) \<in> paper_bbk_domain (paper_arrow_target h) (paper_type_vector \<sigma>s Prop)"
      by (rule paper_R_app_profile_on_type[OF category rt dt ha source am])
    have ep: "?P e (h,a) \<in> paper_bbk_domain (paper_arrow_target h) (paper_type_vector \<sigma>s Prop)"
      by (rule paper_R_app_profile_on_type[OF category rt et ha source am])
    have tails: "paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s
        (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
          (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
          (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) d) a) =
      paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s
        (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
          (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
          (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) e) a)"
      by (rule paper_R_intension_transported_tail[
        OF category Cons.prems(1) Cons.prems(3) Cons.prems(4) Cons.prems(5) ha source am])
    have tail_equal: "paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s (?P d (h,a)) =
      paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s (?P e (h,a))"
      using tails by (simp only: paper_R_app_profile_on_value[OF ha source am] paper_type_vector.simps)
    show "?P d (h,a) = ?P e (h,a)"
      by (rule Cons.IH[where M="paper_arrow_target h" and d="?P d (h,a)" and e="?P e (h,a)",
        OF tail_types target_object dp ep tail_equal])
  qed
  show ?case by (rule paper_R_quasi_functional_on_separates[OF functional Cons.prems(2) rt dt et profiles])
qed

section \<open>The converse injectivity implication\<close>

theorem paper_R_quasi_conditions_imply_intensional:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and fregean: "paper_bbk_quasi_fregean_on Obj Arrows"
    and functional: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
  shows "paper_R_intensional_on \<Sigma> G Obj Arrows"
proof (unfold paper_R_intensional_on_def, intro ballI allI impI)
  fix M \<sigma>s
  assume object: "M \<in> Obj" and types: "list_all paper_R_type \<sigma>s"
  show "inj_on (paper_R_intension_on \<Sigma> G Arrows M \<sigma>s)
    (paper_bbk_domain M (paper_type_vector \<sigma>s Prop))"
  proof (rule inj_onI)
    fix d e
    assume dm: "d \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
      and em: "e \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
      and equal: "paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d =
        paper_R_intension_on \<Sigma> G Arrows M \<sigma>s e"
    show "d = e" by (rule paper_R_intension_separates_from_quasi[
      OF category fregean functional types object dm em equal])
  qed
qed

section \<open>Definition 3.11's equivalence for selected R categories\<close>

text \<open>
  A selected R BBK category is intensional if and only if it is
  both quasi-Fregean and quasi-functional (p.51, footnote 72).
  This is the equivalence of the three displayed profile-injectivity
  conditions for a supplied category. It neither constructs such a
  category nor proves Classicism soundness/completeness for that class.
\<close>

theorem paper_R_intensional_iff_quasi_conditions:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
  shows "paper_R_intensional_on \<Sigma> G Obj Arrows \<longleftrightarrow>
    paper_bbk_quasi_fregean_on Obj Arrows \<and> paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
proof
  assume intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  show "paper_bbk_quasi_fregean_on Obj Arrows \<and> paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    by (rule paper_R_intensional_implies_quasi_conditions[OF intensional])
next
  assume both: "paper_bbk_quasi_fregean_on Obj Arrows \<and> paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
  show "paper_R_intensional_on \<Sigma> G Obj Arrows"
    by (rule paper_R_quasi_conditions_imply_intensional[
      OF category conjunct1[OF both] conjunct2[OF both]])
qed

end
