theory Bacon_Source_Relational_Application_Profile
  imports Bacon_Source_Relational_Application_Morphism Bacon_Source_Relational_Subcategory
begin

section \<open>Applicative behaviour over a chosen collection of arrows\<close>

text \<open>
  app𝒞M(d)(h,a)=appᴺ(hσ→τ(d),a), where h:M→N and a∈Nσ.
  Source: Bacon–Dorr Definition 3.10, p.50. The arrow collection
  is selected, not necessarily the set of all homomorphisms.

  The HOL function takes pairs (h,a). Its extension is fixed to
  undefined outside the displayed pair domain. Consequently irrelevant
  off-domain values cannot distinguish two profiles. The category
  certificate below validates independent R model records and selected
  arrows on a common arbitrary carrier; it does not encode a proper
  class of models. The interpretation and application are the R operations;
  every semantic theorem retains σ→τ∈R. No F model, Functionality,
  fullness or separation is assumed.
\<close>

definition paper_R_app_profile_on ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_R_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow>
    'v \<Rightarrow> (('c,'v) paper_R_bbk_arrow \<times> 'v) \<Rightarrow> 'v" where
  "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d x =
    (case x of (h,a) \<Rightarrow>
      if h \<in> Arrows \<and> paper_arrow_source h = M \<and> a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>
      then paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h)) \<sigma> \<tau> (paper_arrow_map h (Arr \<sigma> \<tau>) d) a
      else undefined)"

lemma paper_R_app_profile_on_value:
  assumes arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  shows "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a) =
    paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h)) \<sigma> \<tau> (paper_arrow_map h (Arr \<sigma> \<tau>) d) a"
  by (simp only: paper_R_app_profile_on_def prod.case arrow source argument; simp)

lemma paper_R_app_profile_on_outside:
  assumes outside: "\<not> (h \<in> Arrows \<and> paper_arrow_source h = M \<and>
    a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>)"
  shows "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a) = undefined"
  by (simp only: paper_R_app_profile_on_def prod.case if_not_P[OF outside])

lemma paper_R_app_profile_on_head_type:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
  shows "paper_arrow_map h (Arr \<sigma> \<tau>) d \<in> paper_bbk_domain (paper_arrow_target h) (Arr \<sigma> \<tau>)"
proof -
  have selected: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    by (rule category)
  have typed_arrow: "h \<in> paper_typed_arrows Obj paper_bbk_domain"
    by (rule paper_R_bbk_arrows_typed[OF paper_R_bbk_subcategory_arrow[OF selected arrow]])
  have source_member: "d \<in> paper_bbk_domain (paper_arrow_source h) (Arr \<sigma> \<tau>)"
    by (simp only: source; rule member)
  show ?thesis by (rule paper_typed_arrows_map[OF typed_arrow source_member])
qed

theorem paper_R_app_profile_on_type:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  shows "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a) \<in>
    paper_bbk_domain (paper_arrow_target h) \<tau>"
proof -
  have selected: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    by (rule category)
  have morphism: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source h) (paper_arrow_target h) (paper_arrow_map h)"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF selected arrow]])
  have target_valid: "paper_R_bbk_data_valid \<Sigma> G (paper_arrow_target h)"
    by (rule paper_R_bbk_data_morphism_target[OF morphism])
  have head: "paper_arrow_map h (Arr \<sigma> \<tau>) d \<in> paper_bbk_domain (paper_arrow_target h) (Arr \<sigma> \<tau>)"
    by (rule paper_R_app_profile_on_head_type[OF category rt member arrow source])
  interpret Target: paper_R_bbk_model \<Sigma> G
    "paper_bbk_domain (paper_arrow_target h)" "paper_bbk_denote (paper_arrow_target h)"
    "paper_bbk_valuation (paper_arrow_target h)"
    by (rule paper_R_bbk_data_model[OF target_valid])
  show ?thesis
    by (simp only: paper_R_app_profile_on_value[OF arrow source argument];
      rule Target.paper_R_application_type[OF rt head argument])
qed

section \<open>Coherence under a further homomorphism\<close>

text \<open>
  For h:M→N, k:N→P and a∈Nσ,
  kτ(app𝒞M(d)(h,a))=app𝒞M(d)(k∘h,kσ(a)).
  This is the well-behavedness condition of p.52 and Example 3.16,
  p.54. It follows from the derived application-preservation theorem,
  not from an added semantic closure or Functionality assumption.
\<close>

theorem paper_R_app_profile_on_coherent:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and first: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
    and second: "k \<in> Arrows" and meeting: "paper_arrow_target h = paper_arrow_source k"
  shows "paper_arrow_map k \<tau> (paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a)) =
    paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d
      (paper_typed_compose paper_bbk_domain k h, paper_arrow_map k \<sigma> a)"
proof -
  have selected: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    by (rule category)
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  have kfull: "k \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    by (rule paper_R_bbk_subcategory_arrow[OF selected second])
  have kmorphism: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_target h) (paper_arrow_target k) (paper_arrow_map k)"
    using paper_R_bbk_arrows_morphism[OF kfull] by (simp only: meeting)
  have km: "paper_R_bbk_model_morphism \<Sigma> G
      (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
      (paper_bbk_valuation (paper_arrow_target h))
      (paper_bbk_domain (paper_arrow_target k)) (paper_bbk_denote (paper_arrow_target k))
      (paper_bbk_valuation (paper_arrow_target k)) (paper_arrow_map k)"
    using kmorphism unfolding paper_R_bbk_data_morphism_def by assumption
  have head: "paper_arrow_map h (Arr \<sigma> \<tau>) d \<in> paper_bbk_domain (paper_arrow_target h) (Arr \<sigma> \<tau>)"
    by (rule paper_R_app_profile_on_head_type[OF category rt member first source])
  have application: "paper_arrow_map k \<tau>
      (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h)) \<sigma> \<tau> (paper_arrow_map h (Arr \<sigma> \<tau>) d) a) =
    paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target k)) (paper_bbk_denote (paper_arrow_target k)) \<sigma> \<tau>
      (paper_arrow_map k (Arr \<sigma> \<tau>) (paper_arrow_map h (Arr \<sigma> \<tau>) d)) (paper_arrow_map k \<sigma> a)"
    by (rule paper_R_application_morphism[OF km rt head argument])
  have ka_source: "a \<in> paper_bbk_domain (paper_arrow_source k) \<sigma>"
    using argument by (simp only: meeting)
  have ka: "paper_arrow_map k \<sigma> a \<in> paper_bbk_domain (paper_arrow_target k) \<sigma>"
    by (rule paper_typed_arrows_map[OF paper_R_bbk_arrows_typed[OF kfull] ka_source])
  have composite: "paper_typed_compose paper_bbk_domain k h \<in> Arrows"
    by (rule Category.compose_arrow[OF first second meeting])
  have composite_source: "paper_arrow_source (paper_typed_compose paper_bbk_domain k h) = M"
    by (simp only: paper_typed_compose_endpoints source)
  have composite_argument: "paper_arrow_map k \<sigma> a \<in>
    paper_bbk_domain (paper_arrow_target (paper_typed_compose paper_bbk_domain k h)) \<sigma>"
    by (simp only: paper_typed_compose_endpoints; rule ka)
  have source_member: "d \<in> paper_bbk_domain (paper_arrow_source h) (Arr \<sigma> \<tau>)"
    by (simp only: source; rule member)
  have composite_head: "paper_arrow_map (paper_typed_compose paper_bbk_domain k h) (Arr \<sigma> \<tau>) d =
    paper_arrow_map k (Arr \<sigma> \<tau>) (paper_arrow_map h (Arr \<sigma> \<tau>) d)"
    by (rule paper_typed_compose_map_on[
      where D=paper_bbk_domain and f=h and \<sigma>="Arr \<sigma> \<tau>", OF source_member])
  show ?thesis
    by (simp only: paper_R_app_profile_on_value[OF first source argument]
      paper_R_app_profile_on_value[OF composite composite_source composite_argument]
      paper_typed_compose_endpoints composite_head; rule application)
qed

end
