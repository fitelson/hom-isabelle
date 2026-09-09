theory Bacon_Source_BBK_Category
  imports Bacon_Source_BBK_Arrows Bacon_Source_Typed_Map_Category Bacon_Source_Subcategory
    Bacon_Source_Action
begin

section \<open>Assembling the category of denotation-preserving maps\<close>

text \<open>
  Let Obj be a set of validated BBK model records for the common
  signature Σ and stock G. Their normalized, denotation-preserving
  typed maps form a category. Source: Bacon–Dorr §3.3, pp.49–50.
  Identity and composition closure are proved in the arrow leaf.
  The generic subcategory theorem supplies the remaining category laws.

  The carrier is common to this specified small collection; no assertion
  about the proper class of all models is made. At this stage the objects
  are formal model records. Restricting to their canonical normalizations
  is the separate step that removes irrelevant record-field extensions.
  No quasi-Fregean, quasi-functional or intensional assumption occurs.
\<close>

theorem paper_bbk_record_category:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
  shows "paper_category Obj (paper_bbk_arrows \<Sigma> G Obj) paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
proof -
  interpret Typed: paper_category Obj "paper_typed_arrows Obj paper_bbk_domain"
    paper_arrow_source paper_arrow_target "paper_typed_compose paper_bbk_domain"
    "paper_typed_identity paper_bbk_domain"
    by (rule paper_typed_map_category)
  show ?thesis
  proof (rule Typed.paper_category_restrict_arrows[OF paper_bbk_arrows_subset])
    fix M
    assume member: "M \<in> Obj"
    show "paper_typed_identity paper_bbk_domain M \<in> paper_bbk_arrows \<Sigma> G Obj"
      by (rule paper_bbk_identity_arrow[OF member models[OF member]])
  next
    fix f g
    assume first: "f \<in> paper_bbk_arrows \<Sigma> G Obj"
      and second: "g \<in> paper_bbk_arrows \<Sigma> G Obj"
      and meeting: "paper_arrow_target f = paper_arrow_source g"
    show "paper_typed_compose paper_bbk_domain g f \<in> paper_bbk_arrows \<Sigma> G Obj"
      by (rule paper_bbk_compose_arrow[OF first second meeting])
  qed
qed

section \<open>Each type determines an action\<close>

text \<open>
  Assign Mσ to M and hσ to h:M→N. These displayed sets and
  maps constitute an action. Source: Example 3.14, pp.53–54.
  On actual domain elements, the normalized identity acts as identity
  and normalized composition acts as ordinary composition. The result
  is proved from the constructed category, not assumed as a new field.
\<close>

theorem paper_bbk_type_action:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
  shows "paper_action Obj (paper_bbk_arrows \<Sigma> G Obj) paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)"
proof -
  interpret Category: paper_category Obj "paper_bbk_arrows \<Sigma> G Obj"
    paper_arrow_source paper_arrow_target "paper_typed_compose paper_bbk_domain"
    "paper_typed_identity paper_bbk_domain"
    by (rule paper_bbk_record_category[OF models])
  show ?thesis
  proof unfold_locales
    fix h a
    assume arrow: "h \<in> paper_bbk_arrows \<Sigma> G Obj"
      and member: "a \<in> paper_bbk_domain (paper_arrow_source h) \<sigma>"
    show "paper_arrow_map h \<sigma> a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      by (rule paper_typed_arrows_map[OF paper_bbk_arrows_typed[OF arrow] member])
  next
    fix M a
    assume object: "M \<in> Obj" and member: "a \<in> paper_bbk_domain M \<sigma>"
    show "paper_arrow_map (paper_typed_identity paper_bbk_domain M) \<sigma> a = a"
      by (rule paper_typed_identity_map_on[where D=paper_bbk_domain and A=M and \<sigma>=\<sigma>, OF member])
  next
    fix f g a
    assume first: "f \<in> paper_bbk_arrows \<Sigma> G Obj"
      and second: "g \<in> paper_bbk_arrows \<Sigma> G Obj"
      and meeting: "paper_arrow_target f = paper_arrow_source g"
      and member: "a \<in> paper_bbk_domain (paper_arrow_source f) \<sigma>"
    show "paper_arrow_map (paper_typed_compose paper_bbk_domain g f) \<sigma> a =
      paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a)"
      by (rule paper_typed_compose_map_on[where D=paper_bbk_domain and f=f and \<sigma>=\<sigma>, OF member])
  qed
qed

end
