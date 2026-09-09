theory Bacon_Source_ZF_R_Type_Invariant
  imports Bacon_Source_ZF_R_Type_Recursion
begin

section \<open>A minimal invariant for the simultaneous type construction\<close>

text \<open>
  At one type ρ, require an actual action on the coded domains,
  equivariance of fρM from the original reindexed action, and a
  bijection from each original Mρ onto its coded domain. These are
  the three inductive properties needed for the recursion on p.72
  in the proof of Proposition 3.22.

  The predicate has no BBK-model, soundness, intensionality or
  interpretation premise, and no inverse-law field. It does not
  assert that the raw recursion satisfies it. Inverse laws below
  follow from the displayed fiber bijections. For inverse equivariance
  we separately supply the actual original action; forward equivariance
  alone does not guarantee that arbitrary original maps preserve types.
  No ambient set bound is needed for these implications.
\<close>

definition paper_ZF_R_type_invariant ::
  "('c,ZF) paper_bbk_model_data set \<Rightarrow> ('c,ZF) paper_R_bbk_arrow set \<Rightarrow>
    (('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow>
    'c paper_ZF_R_representation \<Rightarrow> bool" where
  "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R \<longleftrightarrow>
    (let A = explode (paper_ZF_image_code ArrowBound e Arrows);
         s = paper_ZF_recode_source Arrows e paper_arrow_source;
         t = paper_ZF_recode_target Arrows e paper_arrow_target;
         c = paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain);
         i = paper_ZF_recode_identity e (paper_typed_identity paper_bbk_domain);
         D = (\<lambda>M. paper_bbk_domain M \<rho>);
         u = paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>);
         E = (\<lambda>M. explode (paper_ZF_rep_domain R M))
     in paper_action Obj A s t c i E (paper_ZF_rep_transport R) \<and>
       paper_action_map Obj A s t D u E (paper_ZF_rep_transport R) (paper_ZF_rep_encode R) \<and>
       (\<forall>M\<in>Obj. bij_betw (paper_ZF_rep_encode R M) (D M) (E M)))"

lemma paper_ZF_R_type_invariantI:
  assumes action: "paper_action Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
      (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
      (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain))
      (paper_ZF_recode_identity e (paper_typed_identity paper_bbk_domain))
      (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R)"
    and forward: "paper_action_map Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
      (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
      (\<lambda>M. paper_bbk_domain M \<rho>) (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>))
      (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R) (paper_ZF_rep_encode R)"
    and bijections: "\<And>M. M \<in> Obj \<Longrightarrow>
      bij_betw (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>) (explode (paper_ZF_rep_domain R M))"
  shows "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
  using action forward bijections unfolding paper_ZF_R_type_invariant_def Let_def by blast

lemma paper_ZF_R_type_invariant_action:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
  shows "paper_action Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
    (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
    (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain))
    (paper_ZF_recode_identity e (paper_typed_identity paper_bbk_domain))
    (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R)"
  using invariant unfolding paper_ZF_R_type_invariant_def Let_def by blast

lemma paper_ZF_R_type_invariant_forward:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
  shows "paper_action_map Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
    (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
    (\<lambda>M. paper_bbk_domain M \<rho>) (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>))
    (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R) (paper_ZF_rep_encode R)"
  using invariant unfolding paper_ZF_R_type_invariant_def Let_def by blast

lemma paper_ZF_R_type_invariant_bijection:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R" and object: "M \<in> Obj"
  shows "bij_betw (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>) (explode (paper_ZF_rep_domain R M))"
  using invariant object unfolding paper_ZF_R_type_invariant_def Let_def by blast

lemma paper_ZF_R_type_invariant_injective:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R" and object: "M \<in> Obj"
  shows "inj_on (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>)"
  using paper_ZF_R_type_invariant_bijection[OF invariant object]
  unfolding bij_betw_def by (rule conjunct1)

lemma paper_ZF_R_type_invariant_image:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R" and object: "M \<in> Obj"
  shows "image (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>) = explode (paper_ZF_rep_domain R M)"
  using paper_ZF_R_type_invariant_bijection[OF invariant object]
  unfolding bij_betw_def by (rule conjunct2)

lemma paper_ZF_R_type_invariant_encode_type:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
    and object: "M \<in> Obj" and member: "d \<in> paper_bbk_domain M \<rho>"
  shows "paper_ZF_rep_encode R M d \<in> explode (paper_ZF_rep_domain R M)"
proof -
  have image_member: "paper_ZF_rep_encode R M d \<in> image (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>)"
    by (rule imageI[OF member])
  show ?thesis using image_member by (simp only: paper_ZF_R_type_invariant_image[OF invariant object])
qed

section \<open>The inverse is derived on each original domain\<close>

lemma paper_ZF_R_type_invariant_decode_type:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
    and object: "M \<in> Obj" and member: "z \<in> explode (paper_ZF_rep_domain R M)"
  shows "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<rho>) R M z \<in> paper_bbk_domain M \<rho>"
proof -
  have image_member: "z \<in> image (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>)"
    using member by (simp only: paper_ZF_R_type_invariant_image[OF invariant object])
  show ?thesis unfolding paper_ZF_rep_inverse_def
    by (rule inv_into_into[where f="paper_ZF_rep_encode R M" and A="paper_bbk_domain M \<rho>" and x=z, OF image_member])
qed

lemma paper_ZF_R_type_invariant_decode_encode:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
    and object: "M \<in> Obj" and member: "d \<in> paper_bbk_domain M \<rho>"
  shows "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<rho>) R M (paper_ZF_rep_encode R M d) = d"
  unfolding paper_ZF_rep_inverse_def
  by (rule inv_into_f_f[where f="paper_ZF_rep_encode R M" and A="paper_bbk_domain M \<rho>" and x=d,
    OF paper_ZF_R_type_invariant_injective[OF invariant object] member])

lemma paper_ZF_R_type_invariant_encode_decode:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
    and object: "M \<in> Obj" and member: "z \<in> explode (paper_ZF_rep_domain R M)"
  shows "paper_ZF_rep_encode R M (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<rho>) R M z) = z"
proof -
  have image_member: "z \<in> image (paper_ZF_rep_encode R M) (paper_bbk_domain M \<rho>)"
    using member by (simp only: paper_ZF_R_type_invariant_image[OF invariant object])
  show ?thesis unfolding paper_ZF_rep_inverse_def
    by (rule f_inv_into_f[where f="paper_ZF_rep_encode R M" and A="paper_bbk_domain M \<rho>" and y=z, OF image_member])
qed

theorem paper_ZF_R_type_invariant_inverse_map:
  assumes invariant: "paper_ZF_R_type_invariant Obj Arrows e ArrowBound \<rho> R"
    and source_action: "paper_action Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
      (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
      (paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain))
      (paper_ZF_recode_identity e (paper_typed_identity paper_bbk_domain))
      (\<lambda>M. paper_bbk_domain M \<rho>) (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>))"
  shows "paper_action_map Obj (explode (paper_ZF_image_code ArrowBound e Arrows))
    (paper_ZF_recode_source Arrows e paper_arrow_source) (paper_ZF_recode_target Arrows e paper_arrow_target)
    (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R)
    (\<lambda>M. paper_bbk_domain M \<rho>) (paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>))
    (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M \<rho>) R)"
proof -
  let ?A = "explode (paper_ZF_image_code ArrowBound e Arrows)"
  let ?s = "paper_ZF_recode_source Arrows e paper_arrow_source"
  let ?t = "paper_ZF_recode_target Arrows e paper_arrow_target"
  let ?c = "paper_ZF_recode_compose Arrows e (paper_typed_compose paper_bbk_domain)"
  let ?i = "paper_ZF_recode_identity e (paper_typed_identity paper_bbk_domain)"
  let ?D = "\<lambda>M. paper_bbk_domain M \<rho>"
  let ?u = "paper_ZF_recode_transport Arrows e (\<lambda>h. paper_arrow_map h \<rho>)"
  interpret Target: paper_action Obj ?A ?s ?t ?c ?i "\<lambda>M. explode (paper_ZF_rep_domain R M)" "paper_ZF_rep_transport R"
    by (rule paper_ZF_R_type_invariant_action[OF invariant])
  have target_action: "paper_action Obj ?A ?s ?t ?c ?i
      (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R)" by unfold_locales
  have forward: "paper_action_map Obj ?A ?s ?t ?D ?u
      (\<lambda>M. explode (paper_ZF_rep_domain R M)) (paper_ZF_rep_transport R) (paper_ZF_rep_encode R)"
    by (rule paper_ZF_R_type_invariant_forward[OF invariant])
  have inverse: "paper_action_map Obj ?A ?s ?t (paper_action_image (paper_ZF_rep_encode R) ?D)
      (paper_ZF_rep_transport R) ?D ?u (paper_action_image_inverse (paper_ZF_rep_encode R) ?D)"
  proof (rule paper_action_image_inverse_map[OF source_action target_action forward])
    fix M
    assume object: "M \<in> Obj"
    show "inj_on (paper_ZF_rep_encode R M) (?D M)"
      by (rule paper_ZF_R_type_invariant_injective[OF invariant object])
  qed
  show ?thesis
  proof (rule paper_action_mapI)
    fix M z
    assume object: "M \<in> Obj" and member: "z \<in> explode (paper_ZF_rep_domain R M)"
    show "paper_ZF_rep_inverse ?D R M z \<in> ?D M"
      by (rule paper_ZF_R_type_invariant_decode_type[OF invariant object member])
  next
    fix h z
    assume arrow: "h \<in> ?A" and member: "z \<in> explode (paper_ZF_rep_domain R (?s h))"
    have object: "?s h \<in> Obj" by (rule Target.source_object[OF arrow])
    have image_member: "z \<in> paper_action_image (paper_ZF_rep_encode R) ?D (?s h)"
      using member by (simp only: paper_action_image_def paper_ZF_R_type_invariant_image[OF invariant object])
    have equation: "paper_action_image_inverse (paper_ZF_rep_encode R) ?D (?t h) (paper_ZF_rep_transport R h z) =
        ?u h (paper_action_image_inverse (paper_ZF_rep_encode R) ?D (?s h) z)"
      by (rule paper_action_map_equivariant[OF inverse arrow image_member])
    show "paper_ZF_rep_inverse ?D R (?t h) (paper_ZF_rep_transport R h z) = ?u h (paper_ZF_rep_inverse ?D R (?s h) z)"
      using equation by (simp only: paper_ZF_rep_inverse_def paper_action_image_inverse_def)
  qed
qed

end
