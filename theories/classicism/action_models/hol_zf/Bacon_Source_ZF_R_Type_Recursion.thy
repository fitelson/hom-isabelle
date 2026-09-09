theory Bacon_Source_ZF_R_Type_Recursion
  imports Bacon_Source_ZF_Identity_Individual_Base Bacon_Source_ZF_R_Proposition_Range
    Bacon_Source_ZF_Exponential_Action
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Application
begin

section \<open>The raw simultaneous type-indexed construction\<close>

text \<open>
  Proposition 3.22 is constructed on p.72 by
  fᵉM(a)=a, fᵗM(p)=val𝒞M(p), and
  fσ→τM(d)(h,a)=fτN(appᴺ(hσ→τ(d), (fσN)⁻¹(a))), where N=target(h).
  The new domain at each type is the RANGE of that map, not the whole
  surrounding powerset or exponential. The functions and their injectivity
  must ultimately be justified simultaneously.

  This leaf defines concrete raw data by structural recursion on otype.
  Each recursive result is an entire object-indexed family. Original BBK
  values are already ZF values. The individual bound and the bounded arrow
  encoding are explicit parameters; their correctness is not inferred from
  arbitrary HOL sethood. Only the child input inverse is used in an arrow
  clause. There is no inverse field or assumed all-type decoding law.

  The interpretation of these data requires an independent R category,
  an injective arrow encoding into ArrowBound, a bound on every individual
  fiber, and the source intensionality conditions. None is a field of the
  raw record. The theorems here are defining equations only: range exactness,
  injectivity, action laws, naturality and interpretation remain obligations.
  The construction is relative to standard HOL-ZF, not a pure-HOL universe.
\<close>

record 'o paper_ZF_type_representation =
  paper_ZF_rep_bound :: "'o \<Rightarrow> ZF"
  paper_ZF_rep_domain :: "'o \<Rightarrow> ZF"
  paper_ZF_rep_encode :: "'o \<Rightarrow> ZF \<Rightarrow> ZF"
  paper_ZF_rep_transport :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"

type_synonym 'c paper_ZF_R_representation =
  "('c,ZF) paper_bbk_model_data paper_ZF_type_representation"

definition paper_ZF_rep_inverse ::
  "('o \<Rightarrow> ZF set) \<Rightarrow> 'o paper_ZF_type_representation \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_rep_inverse D R M = inv_into (D M) (paper_ZF_rep_encode R M)"

definition paper_ZF_empty_type_representation :: "'o paper_ZF_type_representation" where
  "paper_ZF_empty_type_representation =
    \<lparr>paper_ZF_rep_bound = (\<lambda>_. Empty), paper_ZF_rep_domain = (\<lambda>_. Empty),
     paper_ZF_rep_encode = (\<lambda>_ _. undefined), paper_ZF_rep_transport = (\<lambda>_ _. undefined)\<rparr>"

definition paper_ZF_R_individual_representation ::
  "ZF \<Rightarrow> (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow>
    ('c,ZF) paper_R_bbk_arrow set \<Rightarrow> 'c paper_ZF_R_representation" where
  "paper_ZF_R_individual_representation IndividualBound e Arrows =
    \<lparr>paper_ZF_rep_bound = (\<lambda>_. IndividualBound),
     paper_ZF_rep_domain = paper_ZF_identity_fiber_code IndividualBound (\<lambda>M. paper_bbk_domain M Ind),
     paper_ZF_rep_encode = (\<lambda>M d. d),
     paper_ZF_rep_transport = paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h Ind)\<rparr>"

definition paper_ZF_R_proposition_representation ::
  "ZF \<Rightarrow> (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow>
    ('c,ZF) paper_R_bbk_arrow set \<Rightarrow> 'c paper_ZF_R_representation" where
  "paper_ZF_R_proposition_representation ArrowBound e Arrows =
    \<lparr>paper_ZF_rep_bound = paper_ZF_powerset_code (paper_ZF_image_code ArrowBound e Arrows)
       (paper_ZF_recode_source Arrows e paper_arrow_source),
     paper_ZF_rep_domain = paper_ZF_R_proposition_range_code ArrowBound e Arrows,
     paper_ZF_rep_encode = paper_ZF_R_truth_profile_code ArrowBound e Arrows,
     paper_ZF_rep_transport = paper_ZF_powerset_transport_code (paper_ZF_image_code ArrowBound e Arrows)
       (paper_ZF_recode_source Arrows e paper_arrow_source)
       (paper_ZF_recode_target Arrows e paper_arrow_target)
       (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain))\<rparr>"

section \<open>The arrow step uses only the two child records\<close>

definition paper_ZF_R_arrow_body ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow>
    (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow>
    ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF \<Rightarrow> (ZF \<times> ZF) \<Rightarrow> ZF" where
  "paper_ZF_R_arrow_body \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d p =
    (let A = paper_ZF_image_code ArrowBound e Arrows;
         s = paper_ZF_recode_source Arrows e paper_arrow_source;
         t = paper_ZF_recode_target Arrows e paper_arrow_target
     in case p of (h,z) \<Rightarrow>
       if (h,z) \<in> paper_exponential_pairs (explode A) s t (\<lambda>N. explode (paper_ZF_rep_domain X N)) M
       then paper_ZF_rep_encode Y (t h)
         (paper_R_application \<Sigma> G (paper_bbk_domain (t h)) (paper_bbk_denote (t h)) \<sigma> \<tau>
           (paper_ZF_recode_transport Arrows e (\<lambda>f. paper_arrow_map f (Arr \<sigma> \<tau>)) h d)
           (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X (t h) z))
       else undefined)"

definition paper_ZF_R_arrow_bound ::
  "ZF \<Rightarrow> (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    'c paper_ZF_R_representation \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow>
    ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF" where
  "paper_ZF_R_arrow_bound ArrowBound e Arrows X Y =
    paper_ZF_exponential_code (paper_ZF_image_code ArrowBound e Arrows)
      (paper_ZF_recode_source Arrows e paper_arrow_source)
      (paper_ZF_recode_target Arrows e paper_arrow_target)
      (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain))
      (paper_ZF_rep_domain X) (paper_ZF_rep_transport X)
      (paper_ZF_rep_domain Y) (paper_ZF_rep_transport Y)"

definition paper_ZF_R_arrow_encode ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow>
    (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow>
    ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d =
    paper_ZF_encode_exponential (paper_ZF_image_code ArrowBound e Arrows)
      (paper_ZF_recode_source Arrows e paper_arrow_source)
      (paper_ZF_recode_target Arrows e paper_arrow_target) (paper_ZF_rep_domain X) M
      (paper_ZF_R_arrow_body \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d)"

definition paper_ZF_R_arrow_representation ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow>
    (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow> 'c paper_ZF_R_representation \<Rightarrow>
    'c paper_ZF_R_representation" where
  "paper_ZF_R_arrow_representation \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y =
    \<lparr>paper_ZF_rep_bound = paper_ZF_R_arrow_bound ArrowBound e Arrows X Y,
     paper_ZF_rep_domain = paper_ZF_range_code (paper_ZF_R_arrow_bound ArrowBound e Arrows X Y)
       (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y)
       (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)),
     paper_ZF_rep_encode = paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y,
     paper_ZF_rep_transport = paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound e Arrows)
       (paper_ZF_recode_source Arrows e paper_arrow_source)
       (paper_ZF_recode_target Arrows e paper_arrow_target)
       (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain)) (paper_ZF_rep_domain X)\<rparr>"

fun paper_ZF_R_type_representation ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow>
    (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    otype \<Rightarrow> 'c paper_ZF_R_representation" where
  "paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows Ind =
    paper_ZF_R_individual_representation IndividualBound e Arrows"
| "paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows Prop =
    paper_ZF_R_proposition_representation ArrowBound e Arrows"
| "paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows (Arr \<sigma> \<tau>) =
    (if paper_R_type (Arr \<sigma> \<tau>) then
      paper_ZF_R_arrow_representation \<Sigma> G ArrowBound e Arrows \<sigma> \<tau>
        (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<sigma>)
        (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<tau>)
     else paper_ZF_empty_type_representation)"

section \<open>Defining equations and the remaining proof frontier\<close>

lemma paper_ZF_R_type_representation_Ind_encode:
  "paper_ZF_rep_encode (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows Ind) M d = d"
  by (simp only: paper_ZF_R_type_representation.simps paper_ZF_R_individual_representation_def
    paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_type_representation_Prop_domain:
  "paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows Prop) M =
    paper_ZF_R_proposition_range_code ArrowBound e Arrows M"
  by (simp only: paper_ZF_R_type_representation.simps paper_ZF_R_proposition_representation_def
    paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_type_representation_arrow:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows (Arr \<sigma> \<tau>) =
    paper_ZF_R_arrow_representation \<Sigma> G ArrowBound e Arrows \<sigma> \<tau>
      (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<sigma>)
      (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<tau>)"
  by (simp only: paper_ZF_R_type_representation.simps if_P[OF rt])

lemma paper_ZF_R_arrow_body_on:
  assumes pair: "Elem (Opair h z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound e Arrows)
    (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
    (paper_ZF_rep_domain X) M)"
  shows "paper_ZF_R_arrow_body \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d (h,z) =
    paper_ZF_rep_encode Y (paper_ZF_recode_target Arrows e paper_arrow_target h)
      (paper_R_application \<Sigma> G
        (paper_bbk_domain (paper_ZF_recode_target Arrows e paper_arrow_target h))
        (paper_bbk_denote (paper_ZF_recode_target Arrows e paper_arrow_target h)) \<sigma> \<tau>
        (paper_ZF_recode_transport Arrows e (\<lambda>f. paper_arrow_map f (Arr \<sigma> \<tau>)) h d)
        (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) X
          (paper_ZF_recode_target Arrows e paper_arrow_target h) z))"
proof -
  have admissible: "(h,z) \<in> paper_exponential_pairs (explode (paper_ZF_image_code ArrowBound e Arrows))
      (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) M"
    by (rule iffD1[OF paper_ZF_pair_code_iff_exponential pair])
  show ?thesis by (simp only: paper_ZF_R_arrow_body_def Let_def prod.case if_P[OF admissible])
qed

lemma paper_ZF_R_arrow_encode_value:
  assumes pair: "Elem (Opair h z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound e Arrows)
    (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
    (paper_ZF_rep_domain X) M)"
  shows "app (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d) (Opair h z) =
    paper_ZF_R_arrow_body \<Sigma> G ArrowBound e Arrows \<sigma> \<tau> X Y M d (h,z)"
  unfolding paper_ZF_R_arrow_encode_def by (rule paper_ZF_encode_exponential_value[OF pair])

text \<open>
  Required simultaneous invariants, for every R type and every original
  category object: (1) encoded values belong to the displayed bound;
  (2) the domain code is exactly their image, with no truncation;
  (3) encoding is injective, hence bijective onto that image;
  (4) canonical transport makes those images actual actions/subactions;
  (5) encoding and its image-guarded inverse commute with every arrow.

  At an arrow type, bound membership and coherence must use the child
  action/inverse laws and original R application preservation. Injectivity
  uses original quasi-functionality and child injectivity. Only AFTER
  those results may the own-type inverse receive its laws. The raw
  separation constructor alone cannot certify exact image membership.
  Non-R arrow types receive empty data and no source-semantic assertion.
  Constants at a root, partial interpretation and totality are not defined
  here; neither an action premodel nor Proposition 3.22 is yet claimed.
\<close>

end
