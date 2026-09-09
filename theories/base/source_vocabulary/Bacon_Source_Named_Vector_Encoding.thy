theory Bacon_Source_Named_Vector_Encoding
  imports Bacon_Source_Named_Vectors Bacon_Source_Named_Decoder_Roundtrip
    Bacon_Source_Named_Alpha_Characterization
begin

section \<open>Closing a decoded chart gives a fixed source abstraction\<close>

text \<open>
  Encoding λy₁…yₙ.A beneath a stack xs produces source abstractions
  of types G(y₁),…,G(yₙ), with body encoded beneath rev(ys) @ xs.
  A chart ns lists free slots from nearest to outermost; therefore
  λrev(ns).decodeₙₛ(M) encodes to the fixed closed abstraction of Γ.
  Source role: Bacon–Dorr §1.1's binding convention, p.5, and the
  finite abstraction argument for Definition 3.1(ii.b–d), p.44.

  Representation: the encoding equation is literal syntax equality.
  Equal encodings give generated named α under rich G. Neither model
  denotation nor pointwise Functionality is used; chart independence of
  the subsequently interpreted open terms remains a semantic step.
\<close>

theorem named_lam_vec_encoding:
  "named_to_source G xs (named_lam_vec ys A) =
    slam_vec (map G ys) (named_to_source G (rev ys @ xs) A)"
proof (induction ys arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  have body: "named_to_source G (n # xs) (named_lam_vec ns A) =
    slam_vec (map G ns) (named_to_source G (rev ns @ (n # xs)) A)"
    by (rule Cons.IH)
  show ?case by (simp add: body)
qed

lemma named_chart_map_types:
  assumes chart: "named_chart G \<Gamma> ns"
  shows "map G ns = \<Gamma>"
proof -
  have types: "list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) ns \<Gamma>"
    by (rule named_chart_types[OF chart])
  then show ?thesis
  proof (induction ns arbitrary: \<Gamma>)
    case Nil
    show ?case using Nil.prems by simp
  next
    case (Cons n ns)
    obtain \<sigma> \<Delta> where frame: "\<Gamma> = \<sigma> # \<Delta>"
      using Cons.prems by (cases \<Gamma>) auto
    have at_head: "G n = \<sigma>"
      and tail: "list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) ns \<Delta>"
      using Cons.prems by (simp_all add: frame)
    have mapped: "map G ns = \<Delta>" by (rule Cons.IH[OF tail])
    show ?case by (simp only: list.map at_head mapped frame)
  qed
qed

theorem source_to_named_closed_abstraction_encoding:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_to_source G [] (named_lam_vec (rev ns) (source_to_named G ns M)) =
    sabstract_prefix \<Gamma> M"
proof -
  have relative: "named_to_source G ns (source_to_named G ns M) = M"
    by (rule source_to_named_relative_roundtrip[OF typed chart rich])
  have types: "map G ns = \<Gamma>" by (rule named_chart_map_types[OF chart])
  show ?thesis by (simp only: named_lam_vec_encoding rev_rev_ident append_Nil2
    relative rev_map[symmetric] types sabstract_prefix_def)
qed

lemma source_to_named_closed_abstraction_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> M \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_in_language L \<Sigma> G
    (named_lam_vec (rev ns) (source_to_named G ns M)) (sarrow_type (rev \<Gamma>) \<tau>)"
proof -
  have decoded: "named_in_language L \<Sigma> G (source_to_named G ns M) \<tau>"
    by (rule source_to_named_language[OF language chart rich])
  have abstracted: "named_in_language L \<Sigma> G
    (named_lam_vec (rev ns) (source_to_named G ns M)) (sarrow_type (map G (rev ns)) \<tau>)"
    by (rule named_lam_vec_language[OF decoded])
  show ?thesis using abstracted
    by (simp only: rev_map[symmetric] named_chart_map_types[OF chart])
qed

lemma source_to_named_closed_abstraction_fv:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_fv (named_lam_vec (rev ns) (source_to_named G ns M)) = {}"
proof -
  have support: "named_fv (source_to_named G ns M) \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF typed chart rich])
  have reverse_support: "named_fv (source_to_named G ns M) \<subseteq> set (rev ns)"
    using support by (simp only: set_rev)
  show ?thesis by (rule named_lam_vec_closed[OF reverse_support])
qed

theorem named_chart_closed_abstractions_alpha:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
    and first: "named_chart G \<Gamma> ns" and second: "named_chart G \<Gamma> ms"
    and rich: "sg_rich G"
  shows "named_alpha G (named_lam_vec (rev ns) (source_to_named G ns M))
    (named_lam_vec (rev ms) (source_to_named G ms M))"
proof -
  have left: "named_to_source G [] (named_lam_vec (rev ns) (source_to_named G ns M)) =
    sabstract_prefix \<Gamma> M"
    by (rule source_to_named_closed_abstraction_encoding[OF typed first rich])
  have right: "named_to_source G [] (named_lam_vec (rev ms) (source_to_named G ms M)) =
    sabstract_prefix \<Gamma> M"
    by (rule source_to_named_closed_abstraction_encoding[OF typed second rich])
  have encodings:
    "named_to_source G [] (named_lam_vec (rev ns) (source_to_named G ns M)) =
     named_to_source G [] (named_lam_vec (rev ms) (source_to_named G ms M))"
    by (rule trans[OF left sym[OF right]])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich encodings])
qed

end
