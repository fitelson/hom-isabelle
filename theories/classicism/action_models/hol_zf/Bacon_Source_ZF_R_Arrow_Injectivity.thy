theory Bacon_Source_ZF_R_Arrow_Injectivity
  imports Bacon_Source_ZF_R_Type_Recursion
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Application_Profile_Action
begin

section \<open>Recover source applicative profiles from coded tests\<close>

text \<open>
  Equal graphs have equal values at ⟨e(h),fσ(a)⟩. If these
  values are fτ(appᴺ(hσ→τ(d),a)), injectivity of fτ on Nτ
  recovers the original application values. Quasi-functionality
  then recovers d. Source: the translated-application equation in
  the proof of Proposition 3.22, p.72.

  This first lemma isolates the separation argument from the concrete
  encoder. Its displayed test equation must be proved for that encoder;
  it is not a new model field or a recursion invariant assumed without
  proof. It needs neither full ambient exponential membership nor
  naturality of the child representations.
\<close>

context paper_ZF_R_profile_encoding
begin

lemma paper_ZF_R_arrow_test_separates:
  assumes quasi: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and em: "e \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and result_injective: "\<And>N. N \<in> objects \<Longrightarrow> inj_on (result_code N) (paper_bbk_domain N \<tau>)"
    and tests: "\<And>x h a. x \<in> paper_bbk_domain M (Arr \<sigma> \<tau>) \<Longrightarrow>
      h \<in> arrows \<Longrightarrow> paper_arrow_source h = M \<Longrightarrow>
      a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma> \<Longrightarrow>
      app (C M x) (Opair (encode h) (argument_code (paper_arrow_target h) a)) =
      result_code (paper_arrow_target h) (paper_R_app_profile_on signature stock arrows M \<sigma> \<tau> x (h,a))"
    and equal: "C M d = C M e"
  shows "d = e"
proof -
  let ?P = "paper_R_app_profile_on signature stock arrows M \<sigma> \<tau>"
  let ?E = "paper_exponential_fiber arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain)
    (\<lambda>N. paper_bbk_domain N \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
    (\<lambda>N. paper_bbk_domain N \<tau>) (\<lambda>h. paper_arrow_map h \<tau>) M"
  have df: "?P d \<in> ?E" by (rule paper_R_app_profile_on_exponential[OF R_category rt dm])
  have ef: "?P e \<in> ?E" by (rule paper_R_app_profile_on_exponential[OF R_category rt em])
  have profiles: "?P d = ?P e"
  proof (rule paper_exponential_fiber_ext[OF df ef])
    fix h :: "('c,'v) paper_R_bbk_arrow" and a :: 'v
    assume pair: "(h,a) \<in> paper_exponential_pairs arrows paper_arrow_source paper_arrow_target
      (\<lambda>N. paper_bbk_domain N \<sigma>) M"
    have ha: "h \<in> arrows" and source: "paper_arrow_source h = M"
      and am: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      using pair by (auto simp only: paper_exponential_pairs_iff)
    have target_object: "paper_arrow_target h \<in> objects" by (rule Encoding.target_object[OF ha])
    have dp: "?P d (h,a) \<in> paper_bbk_domain (paper_arrow_target h) \<tau>"
      by (rule paper_R_app_profile_on_type[OF R_category rt dm ha source am])
    have ep: "?P e (h,a) \<in> paper_bbk_domain (paper_arrow_target h) \<tau>"
      by (rule paper_R_app_profile_on_type[OF R_category rt em ha source am])
    have coded_equal: "result_code (paper_arrow_target h) (?P d (h,a)) =
      result_code (paper_arrow_target h) (?P e (h,a))"
    proof -
      have left: "app (C M d) (Opair (encode h) (argument_code (paper_arrow_target h) a)) =
        result_code (paper_arrow_target h) (?P d (h,a))"
        by (rule tests[OF dm ha source am])
      have right: "app (C M e) (Opair (encode h) (argument_code (paper_arrow_target h) a)) =
        result_code (paper_arrow_target h) (?P e (h,a))"
        by (rule tests[OF em ha source am])
      show ?thesis
      proof -
        have common: "app (C M d) (Opair (encode h) (argument_code (paper_arrow_target h) a)) =
          app (C M e) (Opair (encode h) (argument_code (paper_arrow_target h) a))"
          by (simp only: equal)
        show ?thesis by (rule trans[OF left[symmetric] trans[OF common right]])
      qed
    qed
    show "?P d (h,a) = ?P e (h,a)"
      by (rule inj_onD[OF result_injective[OF target_object] coded_equal dp ep])
  qed
  show ?thesis by (rule paper_R_quasi_functional_on_separates[OF quasi object rt dm em profiles])
qed

end

section \<open>The raw arrow encoder has the required on-image tests\<close>

lemma paper_ZF_R_arrow_encode_source_argument:
  fixes X Y :: "'c paper_ZF_R_representation"
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound"
    and input_typed: "\<And>N a. N \<in> Obj \<Longrightarrow> a \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      paper_ZF_rep_encode X N a \<in> explode (paper_ZF_rep_domain X N)"
    and input_inverse: "\<And>N a. N \<in> Obj \<Longrightarrow> a \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X N (paper_ZF_rep_encode X N a) = a"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  shows "app (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M d)
      (Opair (encode h) (paper_ZF_rep_encode X (paper_arrow_target h) a)) =
    paper_ZF_rep_encode Y (paper_arrow_target h)
      (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> \<tau> (paper_arrow_map h (Arr \<sigma> \<tau>) d) a)"
proof -
  interpret Source: paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound by (rule encoding)
  have object: "paper_arrow_target h \<in> Obj" by (rule Source.Encoding.target_object[OF arrow])
  have coded_arrow: "encode h \<in> Source.Encoding.coded_arrows"
    by (rule Source.Encoding.paper_ZF_encode_arrow_type[OF arrow])
  have coded_source: "Source.Encoding.coded_source (encode h) = M"
    by (simp only: Source.Encoding.paper_ZF_coded_source_on[OF arrow] source)
  have coded_target: "Source.Encoding.coded_target (encode h) = paper_arrow_target h"
    by (rule Source.Encoding.paper_ZF_coded_target_on[OF arrow])
  have coded_argument: "paper_ZF_rep_encode X (paper_arrow_target h) a \<in>
    explode (paper_ZF_rep_domain X (Source.Encoding.coded_target (encode h)))"
    by (simp only: coded_target; rule input_typed[OF object argument])
  have pair: "Elem (Opair (encode h) (paper_ZF_rep_encode X (paper_arrow_target h) a))
    (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode Arrows)
      Source.Encoding.coded_source Source.Encoding.coded_target (paper_ZF_rep_domain X) M)"
    by (simp only: paper_ZF_pair_code_member; rule conjI[OF coded_arrow conjI[OF coded_source coded_argument]])
  have inverse: "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X (paper_arrow_target h)
    (paper_ZF_rep_encode X (paper_arrow_target h) a) = a"
    by (rule input_inverse[OF object argument])
  show ?thesis
    by (simp only: paper_ZF_R_arrow_encode_value[OF pair] paper_ZF_R_arrow_body_on[OF pair]
      coded_target paper_ZF_recode_transport_def Source.Encoding.paper_ZF_decode_encode_arrow[OF arrow] inverse)
qed

text \<open>
  The following injectivity theorem is a single arrow-step result.
  It uses only the child σ inverse on original-domain images and
  child τ injectivity, together with source quasi-functionality.
  The σ inverse is not an inverse of the newly constructed arrow
  representation. Hence no own-type decoding law is used circularly.
  Exponential membership, coherence and the simultaneous recursion
  invariants remain separate proofs.
\<close>

theorem paper_ZF_R_arrow_encode_injective:
  fixes X Y :: "'c paper_ZF_R_representation"
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound"
    and quasi: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and input_typed: "\<And>N a. N \<in> Obj \<Longrightarrow> a \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      paper_ZF_rep_encode X N a \<in> explode (paper_ZF_rep_domain X N)"
    and input_inverse: "\<And>N a. N \<in> Obj \<Longrightarrow> a \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X N (paper_ZF_rep_encode X N a) = a"
    and output_injective: "\<And>N. N \<in> Obj \<Longrightarrow> inj_on (paper_ZF_rep_encode Y N) (paper_bbk_domain N \<tau>)"
  shows "inj_on (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M)
    (paper_bbk_domain M (Arr \<sigma> \<tau>))"
proof -
  interpret Source: paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound by (rule encoding)
  show ?thesis
  proof (rule inj_onI)
    fix d e
    assume dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and em: "e \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
      and equal: "paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M d =
        paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M e"
    show "d = e"
    proof (rule Source.paper_ZF_R_arrow_test_separates[
        where C="paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y"
          and argument_code="paper_ZF_rep_encode X" and result_code="paper_ZF_rep_encode Y",
        OF quasi object rt dm em output_injective _ equal])
      fix x h a
      assume xm: "x \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and ha: "h \<in> Arrows"
        and source: "paper_arrow_source h = M" and am: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      show "app (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M x)
          (Opair (encode h) (paper_ZF_rep_encode X (paper_arrow_target h) a)) =
        paper_ZF_rep_encode Y (paper_arrow_target h) (paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> x (h,a))"
        by (simp only: paper_R_app_profile_on_value[OF ha source am];
          rule paper_ZF_R_arrow_encode_source_argument[OF encoding input_typed input_inverse ha source am])
    qed
  qed
qed

corollary paper_ZF_R_arrow_encode_injective_from_children:
  fixes X Y :: "'c paper_ZF_R_representation"
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound"
    and quasi: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and input_typed: "\<And>N a. N \<in> Obj \<Longrightarrow> a \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      paper_ZF_rep_encode X N a \<in> explode (paper_ZF_rep_domain X N)"
    and input_injective: "\<And>N. N \<in> Obj \<Longrightarrow> inj_on (paper_ZF_rep_encode X N) (paper_bbk_domain N \<sigma>)"
    and output_injective: "\<And>N. N \<in> Obj \<Longrightarrow> inj_on (paper_ZF_rep_encode Y N) (paper_bbk_domain N \<tau>)"
  shows "inj_on (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M)
    (paper_bbk_domain M (Arr \<sigma> \<tau>))"
proof (rule paper_ZF_R_arrow_encode_injective[OF encoding quasi object rt input_typed _ output_injective])
  fix N a
  assume no: "N \<in> Obj" and am: "a \<in> paper_bbk_domain N \<sigma>"
  show "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X N (paper_ZF_rep_encode X N a) = a"
    unfolding paper_ZF_rep_inverse_def
    by (rule inv_into_f_f[where f="paper_ZF_rep_encode X N" and A="paper_bbk_domain N \<sigma>" and x=a,
      OF input_injective[OF no] am])
qed

end
