theory Bacon_Source_Relational_Quasi_Functional_Denotation
  imports Bacon_Source_Relational_Application_Profile_Action
begin

section \<open>Fresh-variable application under a partial assignment\<close>

text \<open>
  If x∉FV(F), then app(⟦F⟧ᵍ,a)=⟦Fx⟧ᵍ⁽ˣ↦ᵃ⁾.
  Here F:σ→τ, x:σ, a∈Dσ, and g is typed and adequate for F.
  Source: Definition 3.1(ii.a–c), pp.43–44, and the application
  interpretation of Definition 3.3, pp.45–46. The update may replace
  an existing value of x; no freshness for dom(g) is required.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_fresh_application_denote:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
    and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F" and am: "a \<in> domain \<sigma>"
  shows "paper_R_application signature stock domain denote \<sigma> \<tau> (denote g F) a =
    denote (g(n := Some a)) (NApp F (NVar n))"
proof -
  let ?k = "g(n := Some a)"
  have aslot: "a \<in> domain (stock n)" using am by (simp only: nt)
  have kt: "named_env_typed domain stock ?k"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed aslot])
  have kf: "named_adequate ?k F" by (rule named_adequate_update[OF adequate])
  have ka: "named_adequate ?k (NApp F (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  have unchanged: "denote ?k F = denote g F"
  proof (rule denote_locality[OF fl kt typed kf adequate])
    fix m
    assume fm: "m \<in> named_fv F"
    show "?k m = g m" by (rule named_update_fresh_agreement[OF fresh fm])
  qed
  have assigned: "?k n = Some a" by simp
  have variable_value: "denote ?k (NVar n) = a" by (rule denote_var[OF kt assigned])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  have vl: "paper_R_in_language signature stock (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt rt])
  have application: "paper_R_application signature stock domain denote \<sigma> \<tau>
      (denote ?k F) (denote ?k (NVar n)) = denote ?k (NApp F (NVar n))"
    by (rule paper_R_application_denote[OF fl vl kt ka])
  show ?thesis using application by (simp only: unchanged variable_value)
qed

end

section \<open>Common application equality gives equality of denotations\<close>

text \<open>
  The common theory of a quasi-functional category is closed under the
  rule from Fx=Hx to F=H, with x∉FV(F)∪FV(H).
  Source: the rule on p.15 and Theorem 3.12's soundness argument, p.51.
  F and H may be open. The common premise below ranges over every
  category object and every typed partial assignment adequate for both
  applications, not only assignments transported from the source object.

  Representation: paper_R_quasi_functional_denotation states the semantic
  denotation step before wrapping it in the literal identity-truth clause.
  Every target argument is tested by updating a transported assignment.
  No surjectivity, map injectivity, quasi-Fregeanness, canonical objects,
  total completion, F model, or object-language proof rule is assumed.
\<close>

theorem paper_R_quasi_functional_denotation:
  fixes \<Sigma> :: "'c ssignature" and M :: "('c,'v) paper_bbk_model_data"
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and quasi: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and nt: "G n = \<sigma>" and freshF: "n \<notin> named_fv F" and freshH: "n \<notin> named_fv H"
    and common: "\<And>N k. N \<in> Obj \<Longrightarrow> named_env_typed (paper_bbk_domain N) G k \<Longrightarrow>
      named_adequate k (NApp F (NVar n)) \<Longrightarrow> named_adequate k (NApp H (NVar n)) \<Longrightarrow>
      paper_bbk_denote N k (NApp F (NVar n)) = paper_bbk_denote N k (NApp H (NVar n))"
    and object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequateF: "named_adequate g F" and adequateH: "named_adequate g H"
  shows "paper_bbk_denote M g F = paper_bbk_denote M g H"
proof -
  have valid: "paper_R_bbk_data_valid \<Sigma> G M"
    by (rule paper_R_bbk_subcategory_models[OF category object])
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have fm: "paper_bbk_denote M g F \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    by (rule paper_R_bbk_data_denote_type[OF valid fl typed adequateF])
  have hm: "paper_bbk_denote M g H \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    by (rule paper_R_bbk_data_denote_type[OF valid hl typed adequateH])
  have profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g F) =
      paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g H)"
  proof (rule ext)
    fix z :: "('c,'v) paper_R_bbk_arrow \<times> 'v"
    obtain h a where shape: "z = (h,a)" by (cases z) auto
    show "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g F) z =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g H) z"
    proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M \<and> a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>")
      case False
      show ?thesis by (simp only: shape paper_R_app_profile_on_outside[OF False])
    next
      case True
      have arrow: "h \<in> Arrows" and origin: "paper_arrow_source h = M"
        and am: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>" using True by blast+
      let ?N = "paper_arrow_target h"
      let ?k = "paper_hom_assignment G (paper_arrow_map h) g"
      let ?u = "?k(n := Some a)"
      have full_arrow: "h \<in> paper_R_bbk_arrows \<Sigma> G Obj"
        by (rule paper_R_bbk_subcategory_arrow[OF category arrow])
      have typed_arrow: "h \<in> paper_typed_arrows Obj paper_bbk_domain"
        by (rule paper_R_bbk_arrows_typed[OF full_arrow])
      have target_object: "?N \<in> Obj"
        using typed_arrow unfolding paper_typed_arrows_def by blast
      have morphism: "paper_R_bbk_data_morphism \<Sigma> G M ?N (paper_arrow_map h)"
        using paper_R_bbk_arrows_morphism[OF full_arrow] by (simp only: origin)
      have hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
          (paper_bbk_domain ?N) (paper_bbk_denote ?N) (paper_arrow_map h)"
        by (rule paper_R_bbk_data_morphism_raw[OF morphism])
      interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain ?N"
        "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
        by (rule paper_R_bbk_data_model[OF paper_R_bbk_data_morphism_target[OF morphism]])
      have kt: "named_env_typed (paper_bbk_domain ?N) G ?k"
        by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
      have kf: "named_adequate ?k F"
        by (rule paper_R_bbk_homomorphism_assignment_adequate[OF adequateF])
      have kh: "named_adequate ?k H"
        by (rule paper_R_bbk_homomorphism_assignment_adequate[OF adequateH])
      have aslot: "a \<in> paper_bbk_domain ?N (G n)" using am by (simp only: nt)
      have ut: "named_env_typed (paper_bbk_domain ?N) G ?u"
        by (rule named_assignment_update_typed[where D="paper_bbk_domain ?N" and G=G and n=n, OF kt aslot])
      have uf: "named_adequate ?u (NApp F (NVar n))"
        by (rule named_quantifier_application_adequate[OF kf])
      have uh: "named_adequate ?u (NApp H (NVar n))"
        by (rule named_quantifier_application_adequate[OF kh])
      have tested: "paper_bbk_denote ?N ?u (NApp F (NVar n)) =
          paper_bbk_denote ?N ?u (NApp H (NVar n))"
        by (rule common[OF target_object ut uf uh])
      have transportedF: "paper_arrow_map h (Arr \<sigma> \<tau>) (paper_bbk_denote M g F) = paper_bbk_denote ?N ?k F"
        by (rule paper_R_bbk_homomorphism_denote[OF hom fl typed adequateF])
      have transportedH: "paper_arrow_map h (Arr \<sigma> \<tau>) (paper_bbk_denote M g H) = paper_bbk_denote ?N ?k H"
        by (rule paper_R_bbk_homomorphism_denote[OF hom hl typed adequateH])
      have evalF: "paper_R_application \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N)
          \<sigma> \<tau> (paper_bbk_denote ?N ?k F) a = paper_bbk_denote ?N ?u (NApp F (NVar n))"
        by (rule Target.paper_R_fresh_application_denote[OF fl kt kf nt freshF am])
      have evalH: "paper_R_application \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N)
          \<sigma> \<tau> (paper_bbk_denote ?N ?k H) a = paper_bbk_denote ?N ?u (NApp H (NVar n))"
        by (rule Target.paper_R_fresh_application_denote[OF hl kt kh nt freshH am])
      show ?thesis by (simp only: shape paper_R_app_profile_on_value[OF arrow origin am]
        transportedF transportedH evalF evalH tested)
    qed
  qed
  show ?thesis by (rule paper_R_quasi_functional_on_separates[OF quasi object rt fm hm profiles])
qed

end
