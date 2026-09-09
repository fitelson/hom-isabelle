theory Bacon_Source_Relational_Intensional_Forward
  imports Bacon_Source_Relational_Intension Bacon_Source_Relational_Application_Profile_Action
begin

section \<open>Equal applicative profiles have equal relation intensions\<close>

text \<open>
  If app𝒞M(d)=app𝒞M(e) at σ→(τ₁→⋯→τₙ→t), then
  int𝒞M(d)=int𝒞M(e) at that same relational type: for each
  outgoing h:M→N and each tuple (a,x₁,…,xₙ) in N, the first
  application values are equal, so the remaining applications have
  the same truth value. Source: Definitions 3.10–3.11, pp.50–51.

  This implication is about the actual raw definitions. It needs no
  category laws, model premise, or preservation of valuation. Tuples
  range over ALL target-domain arguments. Their order is unchanged.
\<close>

lemma paper_R_equal_app_profiles_intensions:
  fixes \<Sigma> :: "'c ssignature" and d :: 'v
  assumes profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) d =
    paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) e"
  shows "paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) d =
    paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) e"
proof (rule set_eqI)
  fix z :: "('c,'v) paper_R_bbk_arrow \<times> 'v list"
  obtain h xs where pair: "z = (h,xs)" by (cases z) auto
  show "(z \<in> paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) d) =
    (z \<in> paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) e)"
  proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M \<and>
      paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) (\<sigma>#\<tau>s) xs")
    case True
    have arrow: "h \<in> Arrows" and src: "paper_arrow_source h = M"
      and args: "paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) (\<sigma>#\<tau>s) xs"
      using True by blast+
    obtain a ys where shape: "xs = a#ys"
      and am: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
      and tail: "paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) \<tau>s ys"
      using args by (cases xs) auto
    have at_pair: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) d (h,a) =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) e (h,a)"
      by (rule fun_cong[OF profiles])
    have first_app: "paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<tau>s Prop)
        (paper_arrow_map h (Arr \<sigma> (paper_type_vector \<tau>s Prop)) d) a =
      paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<tau>s Prop)
        (paper_arrow_map h (Arr \<sigma> (paper_type_vector \<tau>s Prop)) e) a"
      using at_pair by (simp only: paper_R_app_profile_on_value[OF arrow src am])
    show ?thesis by (simp only: pair paper_R_intension_on_member shape
      paper_type_vector.simps paper_R_apply_vector.simps first_app)
  next
    case False
    show ?thesis using False by (auto simp only: pair paper_R_intension_on_member)
  qed
qed

section \<open>The forward direction of Definition 3.11's equivalence\<close>

text \<open>
  In R every function type σ→τ has relational codomain τ, hence
  τ=τ₁→⋯→τₙ→t for a finite list of R types. Intensionality
  therefore makes the applicative profile injective at every R arrow
  type. Its empty-vector case already gives quasi-Fregeanness.
  Source: p.51, including footnote 72.

  The raw injectivity implication is proved without a category or model
  assumption. To call the data an intensional BBK category, the separate
  R category certificate is still required. This is not the converse,
  existence of such a category, or Theorem 3.12.
\<close>

theorem paper_R_intensional_implies_quasi_functional:
  assumes intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  shows "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
proof (unfold paper_R_quasi_functional_on_def, intro ballI allI impI)
  fix M \<sigma> \<tau>
  assume object: "M \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  have domain_R: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  have codomain_R: "paper_R_relational \<tau>" by (rule paper_R_arrow_codomain[OF rt])
  obtain \<tau>s where types: "list_all paper_R_type \<tau>s" and codomain: "\<tau> = paper_type_vector \<tau>s Prop"
    using paper_R_relational_decomposition[OF codomain_R] by (elim exE conjE)
  have all_types: "list_all paper_R_type (\<sigma>#\<tau>s)" using domain_R types by simp
  have injective: "inj_on (paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s))
      (paper_bbk_domain M (paper_type_vector (\<sigma>#\<tau>s) Prop))"
    using intensional object all_types unfolding paper_R_intensional_on_def by blast
  show "inj_on (paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>) (paper_bbk_domain M (Arr \<sigma> \<tau>))"
  proof (rule inj_onI)
    fix d e
    assume dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
      and em: "e \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
      and profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> e"
    have profiles_tail: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) d =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> (paper_type_vector \<tau>s Prop) e"
      using profiles by (simp only: codomain)
    have intensions: "paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) d =
        paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<tau>s) e"
      by (rule paper_R_equal_app_profiles_intensions[OF profiles_tail])
    have dv: "d \<in> paper_bbk_domain M (paper_type_vector (\<sigma>#\<tau>s) Prop)"
      using dm by (simp only: paper_type_vector.simps codomain)
    have ev: "e \<in> paper_bbk_domain M (paper_type_vector (\<sigma>#\<tau>s) Prop)"
      using em by (simp only: paper_type_vector.simps codomain)
    show "d = e" by (rule inj_onD[OF injective intensions dv ev])
  qed
qed

corollary paper_R_intensional_implies_quasi_conditions:
  assumes intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  shows "paper_bbk_quasi_fregean_on Obj Arrows \<and> paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
  by (rule conjI[OF paper_R_intensional_implies_quasi_fregean[OF intensional]
    paper_R_intensional_implies_quasi_functional[OF intensional]])

end
