theory Bacon_Source_BBK_Subcategory
  imports Bacon_Source_BBK_Category
begin

section \<open>Specified collections of BBK homomorphisms\<close>

text \<open>
  Bacon–Dorr §3.3, pp.49–50, permits a CHOSEN collection of
  homomorphisms, provided it contains identities and is composition-closed.
  It need not contain every homomorphism between its objects.
  The predicate below states this choice explicitly. The full-homomorphism
  category is a special case, not the definition of every BBK category.

  Objects are validated model records on the specified common carrier;
  maps are normalized typed functions carrying their source and target.
  Canonical object normalization is a separate representation condition.
  These set-indexed results do not assert proper-class universality.
\<close>

definition paper_bbk_subcategory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_bbk_arrow set \<Rightarrow> bool" where
  "paper_bbk_subcategory \<Sigma> G Obj Arrows \<longleftrightarrow>
    (\<forall>M\<in>Obj. paper_bbk_data_valid \<Sigma> G M) \<and>
    Arrows \<subseteq> paper_bbk_arrows \<Sigma> G Obj \<and>
    (\<forall>M\<in>Obj. paper_typed_identity paper_bbk_domain M \<in> Arrows) \<and>
    (\<forall>f\<in>Arrows. \<forall>g\<in>Arrows. paper_arrow_target f = paper_arrow_source g \<longrightarrow>
      paper_typed_compose paper_bbk_domain g f \<in> Arrows)"

lemma paper_bbk_subcategory_models:
  assumes subcategory: "paper_bbk_subcategory \<Sigma> G Obj Arrows" and member: "M \<in> Obj"
  shows "paper_bbk_data_valid \<Sigma> G M"
  using subcategory member unfolding paper_bbk_subcategory_def by blast

lemma paper_bbk_subcategory_arrow:
  assumes subcategory: "paper_bbk_subcategory \<Sigma> G Obj Arrows" and arrow: "f \<in> Arrows"
  shows "f \<in> paper_bbk_arrows \<Sigma> G Obj"
  using subcategory arrow unfolding paper_bbk_subcategory_def by blast

theorem paper_bbk_full_subcategory:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
  shows "paper_bbk_subcategory \<Sigma> G Obj (paper_bbk_arrows \<Sigma> G Obj)"
proof (unfold paper_bbk_subcategory_def, intro conjI)
  show "\<forall>M\<in>Obj. paper_bbk_data_valid \<Sigma> G M"
    by (intro ballI, rule models, assumption)
next
  show "paper_bbk_arrows \<Sigma> G Obj \<subseteq> paper_bbk_arrows \<Sigma> G Obj" by (rule subset_refl)
next
  show "\<forall>M\<in>Obj. paper_typed_identity paper_bbk_domain M \<in> paper_bbk_arrows \<Sigma> G Obj"
    by (intro ballI, rule paper_bbk_identity_arrow, assumption, rule models, assumption)
next
  show "\<forall>f\<in>paper_bbk_arrows \<Sigma> G Obj. \<forall>g\<in>paper_bbk_arrows \<Sigma> G Obj.
    paper_arrow_target f = paper_arrow_source g \<longrightarrow>
    paper_typed_compose paper_bbk_domain g f \<in> paper_bbk_arrows \<Sigma> G Obj"
    by (intro ballI impI, rule paper_bbk_compose_arrow; assumption)
qed

theorem paper_bbk_subcategory_category:
  assumes subcategory: "paper_bbk_subcategory \<Sigma> G Obj Arrows"
  shows "paper_category Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
proof -
  have models: "paper_bbk_data_valid \<Sigma> G M" if "M \<in> Obj" for M
    by (rule paper_bbk_subcategory_models[OF subcategory that])
  interpret Full: paper_category Obj "paper_bbk_arrows \<Sigma> G Obj" paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_bbk_record_category[OF models])
  have subset: "Arrows \<subseteq> paper_bbk_arrows \<Sigma> G Obj"
    using subcategory unfolding paper_bbk_subcategory_def by blast
  have ids: "paper_typed_identity paper_bbk_domain M \<in> Arrows" if "M \<in> Obj" for M
    using subcategory that unfolding paper_bbk_subcategory_def by blast
  have comps: "paper_typed_compose paper_bbk_domain g f \<in> Arrows"
    if "f \<in> Arrows" "g \<in> Arrows" "paper_arrow_target f = paper_arrow_source g" for f g
    using subcategory that unfolding paper_bbk_subcategory_def by blast
  show ?thesis by (rule Full.paper_category_restrict_arrows[OF subset ids comps])
qed

theorem paper_bbk_selected_type_action:
  assumes subcategory: "paper_bbk_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)"
proof -
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_bbk_subcategory_category[OF subcategory])
  show ?thesis
  proof unfold_locales
    fix h a
    assume arrow: "h \<in> Arrows" and member: "a \<in> paper_bbk_domain (paper_arrow_source h) \<sigma>"
    have typed_arrow: "h \<in> paper_typed_arrows Obj paper_bbk_domain"
      by (rule paper_bbk_arrows_typed[OF paper_bbk_subcategory_arrow[OF subcategory arrow]])
    show "paper_arrow_map h \<sigma> a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      by (rule paper_typed_arrows_map[OF typed_arrow member])
  next
    fix M a
    assume object: "M \<in> Obj" and member: "a \<in> paper_bbk_domain M \<sigma>"
    show "paper_arrow_map (paper_typed_identity paper_bbk_domain M) \<sigma> a = a"
      by (rule paper_typed_identity_map_on[where D=paper_bbk_domain and A=M and \<sigma>=\<sigma>, OF member])
  next
    fix f g a
    assume first: "f \<in> Arrows" and second: "g \<in> Arrows"
      and meeting: "paper_arrow_target f = paper_arrow_source g"
      and member: "a \<in> paper_bbk_domain (paper_arrow_source f) \<sigma>"
    show "paper_arrow_map (paper_typed_compose paper_bbk_domain g f) \<sigma> a =
      paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a)"
      by (rule paper_typed_compose_map_on[where D=paper_bbk_domain and f=f and \<sigma>=\<sigma>, OF member])
  qed
qed

end
