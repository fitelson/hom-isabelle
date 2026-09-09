theory Bacon_Source_BBK_Application_Profile_Action
  imports Bacon_Source_BBK_Application_Profile Bacon_Source_Exponential_Action
begin

section \<open>Applicative profiles inhabit the displayed exponential fiber\<close>

text \<open>
  For d∈Mσ→τ, app𝒞M(d) belongs to (−σ⇒−τ)M.
  Source: Bacon–Dorr Definition 3.10, p.50, the well-behavedness
  condition on p.52, and Example 3.16, p.54.

  Fiber membership supplies all three conditions: normalization outside
  the actual pair domain, result typing, and coherence under subsequent
  arrows. The general exponential-action construction is independent
  of BBK models. This leaf connects its concrete fiber and transport
  functions to the selected BBK category; no fullness is inferred.
\<close>

theorem paper_bbk_app_profile_on_exponential:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
    and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  shows "paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d \<in>
    paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain)
      (\<lambda>N. paper_bbk_domain N \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>N. paper_bbk_domain N \<tau>) (\<lambda>h. paper_arrow_map h \<tau>) M"
proof (rule paper_exponential_fiberI)
  fix p
  assume outside: "p \<notin> paper_exponential_pairs Arrows paper_arrow_source paper_arrow_target
    (\<lambda>N. paper_bbk_domain N \<sigma>) M"
  show "paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d p = undefined"
  proof (cases p)
    case (Pair h a)
    have absent: "\<not> (h \<in> Arrows \<and> paper_arrow_source h = M \<and>
      a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>)"
      using outside by (simp add: Pair paper_exponential_pairs_iff)
    show ?thesis by (simp only: Pair; rule paper_bbk_app_profile_on_outside[OF absent])
  qed
next
  fix h a
  assume arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  show "paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a) \<in>
    paper_bbk_domain (paper_arrow_target h) \<tau>"
    by (rule paper_bbk_app_profile_on_type[OF category member arrow source argument])
next
  fix h k a
  assume first: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and second: "k \<in> Arrows" and meeting: "paper_arrow_target h = paper_arrow_source k"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  show "paper_arrow_map k \<tau> (paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d (h,a)) =
    paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d
      (paper_typed_compose paper_bbk_domain k h, paper_arrow_map k \<sigma> a)"
    by (rule paper_bbk_app_profile_on_coherent[OF category member first source argument second meeting])
qed

section \<open>Naturality includes equality off the pair domain\<close>

text \<open>
  For f:M→N, app𝒞N(fσ→τ(d))=fσ⇒τ(app𝒞M(d)).
  Both sides evaluate an admissible (h,a) using the composite h∘f.
  Outside N's pair domain, both normalized functions are undefined.
  Thus this is actual equality of the represented functions, not
  an assertion that leaves their irrelevant extensions unconstrained.
\<close>

theorem paper_bbk_app_profile_on_naturality:
  fixes \<Sigma> :: "'c ssignature" and d :: 'v
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
    and arrow: "f \<in> Arrows"
    and member: "d \<in> paper_bbk_domain (paper_arrow_source f) (Arr \<sigma> \<tau>)"
  shows "paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_target f) \<sigma> \<tau>
      (paper_arrow_map f (Arr \<sigma> \<tau>) d) =
    paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>N. paper_bbk_domain N \<sigma>) f
      (paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_source f) \<sigma> \<tau> d)"
proof -
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_bbk_canonical_subcategory_category[OF category])
  show ?thesis
  proof (rule ext)
    fix p :: "('c,'v) paper_bbk_arrow \<times> 'v"
    obtain h a where pair: "p = (h,a)" by (cases p) auto
    show "paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_target f) \<sigma> \<tau>
        (paper_arrow_map f (Arr \<sigma> \<tau>) d) p =
      paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
        (paper_typed_compose paper_bbk_domain) (\<lambda>N. paper_bbk_domain N \<sigma>) f
        (paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_source f) \<sigma> \<tau> d) p"
    proof (cases "(h,a) \<in> paper_exponential_pairs Arrows paper_arrow_source paper_arrow_target
      (\<lambda>N. paper_bbk_domain N \<sigma>) (paper_arrow_target f)")
      case True
      have ha: "h \<in> Arrows" and source: "paper_arrow_source h = paper_arrow_target f"
        and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
        using True by (auto simp only: paper_exponential_pairs_iff)
      have meeting: "paper_arrow_target f = paper_arrow_source h" by (rule source[symmetric])
      have composite: "paper_typed_compose paper_bbk_domain h f \<in> Arrows"
        by (rule Category.compose_arrow[OF arrow ha meeting])
      have composite_source: "paper_arrow_source (paper_typed_compose paper_bbk_domain h f) = paper_arrow_source f"
        by (simp only: paper_typed_compose_endpoints)
      have composite_argument: "a \<in>
        paper_bbk_domain (paper_arrow_target (paper_typed_compose paper_bbk_domain h f)) \<sigma>"
        by (simp only: paper_typed_compose_endpoints; rule argument)
      have composite_head: "paper_arrow_map (paper_typed_compose paper_bbk_domain h f) (Arr \<sigma> \<tau>) d =
        paper_arrow_map h (Arr \<sigma> \<tau>) (paper_arrow_map f (Arr \<sigma> \<tau>) d)"
        by (rule paper_typed_compose_map_on[
          where D=paper_bbk_domain and f=f and \<sigma>="Arr \<sigma> \<tau>", OF member])
      show ?thesis
        by (simp only: pair paper_exponential_transport_on[OF True]
          paper_bbk_app_profile_on_value[OF ha source argument]
          paper_bbk_app_profile_on_value[OF composite composite_source composite_argument]
          paper_typed_compose_endpoints composite_head)
    next
      case False
      have absent: "\<not> (h \<in> Arrows \<and> paper_arrow_source h = paper_arrow_target f \<and>
        a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>)"
        using False by (simp add: paper_exponential_pairs_iff)
      show ?thesis by (simp only: pair paper_exponential_transport_off[OF False]
        paper_bbk_app_profile_on_outside[OF absent])
    qed
  qed
qed

section \<open>The target is an actual action, not an assumed exponential\<close>

theorem paper_bbk_profile_exponential_action:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain)
      (\<lambda>N. paper_bbk_domain N \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>N. paper_bbk_domain N \<tau>) (\<lambda>h. paper_arrow_map h \<tau>))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>N. paper_bbk_domain N \<sigma>))"
  by (rule paper_exponential_action_from_actions[
    OF paper_bbk_canonical_subcategory_type_action[where \<sigma>=\<sigma>, OF category]
      paper_bbk_canonical_subcategory_type_action[where \<sigma>=\<tau>, OF category]])

section \<open>Quasi-functionality remains a separate condition\<close>

text \<open>
  A category is quasi-functional when app𝒞M is injective at every
  functional type (Definition 3.11, p.50). Because profiles have
  fixed off-domain values, this injectivity cannot be witnessed by
  arbitrary choices on irrelevant pairs. The following declaration
  and its conditional elimination rule prove no category to be
  quasi-functional. In particular no fullness or separation theorem
  follows from the profile construction alone.
  The displayed quantification is the full-F version of the condition.
  The paper's default R system requires the corresponding type restriction
  before using its comparisons with relational intensions. An independent
  R language/model correspondence is not asserted by this declaration.
\<close>

definition paper_bbk_quasi_functional_on ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_bbk_arrow set \<Rightarrow> bool" where
  "paper_bbk_quasi_functional_on \<Sigma> G Obj Arrows \<longleftrightarrow>
    (\<forall>M\<in>Obj. \<forall>\<sigma> \<tau>. inj_on (paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)
      (paper_bbk_domain M (Arr \<sigma> \<tau>)))"

lemma paper_bbk_quasi_functional_on_separates:
  assumes quasi: "paper_bbk_quasi_functional_on \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and em: "e \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and profiles: "paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d =
      paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> e"
  shows "d = e"
proof -
  have injective: "inj_on (paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)
    (paper_bbk_domain M (Arr \<sigma> \<tau>))"
    using quasi object unfolding paper_bbk_quasi_functional_on_def by blast
  show ?thesis by (rule inj_onD[OF injective profiles dm em])
qed

end
