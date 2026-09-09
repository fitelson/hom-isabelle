theory Bacon_Source_Relational_Intensional_Abstraction
  imports Bacon_Source_Relational_Vector_Abstraction_Denotation
    Bacon_Source_Relational_Intension Bacon_Source_Relational_Subcategory
begin

section \<open>Common body truth determines abstraction intensions\<close>

text \<open>
  If P and Q agree in truth at every object and every typed assignment
  adequate for both, then λn₁…nₖ.P and λn₁…nₖ.Q have the same
  intension. Source: Equivalence on p.14, Definition 3.10 on p.50,
  and Theorem 3.12's common-theory soundness argument on p.51.

  Representation: each outgoing arrow transports the original partial
  assignment. Every typed tuple in the target domains is then tested by
  sequential outer-to-inner updates. Empty vectors and repeated names
  are allowed; inner updates take precedence. The bodies may be open,
  and the original assignment need only cover their abstractions.
  No canonicality, total completion, F model, or map surjectivity is used.
\<close>

lemma paper_R_common_truth_abstraction_intensions:
  fixes \<Sigma> :: "'c ssignature" and M :: "('c,'v) paper_bbk_model_data"
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and common: "\<And>N k. N \<in> Obj \<Longrightarrow> named_env_typed (paper_bbk_domain N) G k \<Longrightarrow>
      named_adequate k P \<Longrightarrow> named_adequate k Q \<Longrightarrow>
      paper_bbk_valuation N (paper_bbk_denote N k P) = paper_bbk_valuation N (paper_bbk_denote N k Q)"
    and object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and pa: "named_adequate g (named_lam_vec ns P)" and qa: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_R_intension_on \<Sigma> G Arrows M (map G ns) (paper_bbk_denote M g (named_lam_vec ns P)) =
    paper_R_intension_on \<Sigma> G Arrows M (map G ns) (paper_bbk_denote M g (named_lam_vec ns Q))"
proof -
  let ?LP = "named_lam_vec ns P"
  let ?LQ = "named_lam_vec ns Q"
  let ?types = "map G ns"
  let ?t = "paper_type_vector ?types Prop"
  have lpl: "paper_R_in_language \<Sigma> G ?LP ?t" by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lql: "paper_R_in_language \<Sigma> G ?LQ ?t" by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  show ?thesis
  proof (rule set_eqI)
    fix z :: "('c,'v) paper_R_bbk_arrow \<times> 'v list"
    obtain h xs where shape: "z = (h,xs)" by (cases z) auto
    show "(z \<in> paper_R_intension_on \<Sigma> G Arrows M ?types (paper_bbk_denote M g ?LP)) =
        (z \<in> paper_R_intension_on \<Sigma> G Arrows M ?types (paper_bbk_denote M g ?LQ))"
    proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M \<and>
        paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) ?types xs")
      case False
      then show ?thesis by (auto simp only: shape paper_R_intension_on_member)
    next
      case True
      have arrow: "h \<in> Arrows" and origin: "paper_arrow_source h = M"
        and args: "paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) ?types xs"
        using True by blast+
      let ?N = "paper_arrow_target h"
      let ?k = "paper_hom_assignment G (paper_arrow_map h) g"
      let ?u = "paper_R_update_vector ?k ns xs"
      have full_arrow: "h \<in> paper_R_bbk_arrows \<Sigma> G Obj"
        by (rule paper_R_bbk_subcategory_arrow[OF category arrow])
      have typed_arrow: "h \<in> paper_typed_arrows Obj paper_bbk_domain"
        by (rule paper_R_bbk_arrows_typed[OF full_arrow])
      have target_object: "?N \<in> Obj" using typed_arrow unfolding paper_typed_arrows_def by blast
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
      have kp: "named_adequate ?k ?LP"
        by (rule paper_R_bbk_homomorphism_assignment_adequate[OF pa])
      have kq: "named_adequate ?k ?LQ"
        by (rule paper_R_bbk_homomorphism_assignment_adequate[OF qa])
      have lengths: "length ns = length xs" using paper_R_vector_args_length[OF args] by simp
      have ut: "named_env_typed (paper_bbk_domain ?N) G ?u"
        by (rule paper_R_update_vector_typed[OF kt args])
      have up: "named_adequate ?u P"
        by (rule iffD2[OF paper_R_update_vector_adequate_iff[OF lengths] kp])
      have uq: "named_adequate ?u Q"
        by (rule iffD2[OF paper_R_update_vector_adequate_iff[OF lengths] kq])
      have tested: "paper_bbk_valuation ?N (paper_bbk_denote ?N ?u P) =
          paper_bbk_valuation ?N (paper_bbk_denote ?N ?u Q)"
        by (rule common[OF target_object ut up uq])
      have transportedP: "paper_arrow_map h ?t (paper_bbk_denote M g ?LP) = paper_bbk_denote ?N ?k ?LP"
        by (rule paper_R_bbk_homomorphism_denote[OF hom lpl typed pa])
      have transportedQ: "paper_arrow_map h ?t (paper_bbk_denote M g ?LQ) = paper_bbk_denote ?N ?k ?LQ"
        by (rule paper_R_bbk_homomorphism_denote[OF hom lql typed qa])
      have evaluatedP: "paper_R_apply_vector \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N)
          ?types (paper_bbk_denote ?N ?k ?LP) xs = paper_bbk_denote ?N ?u P"
        by (rule Target.paper_R_lam_vec_application_denote[OF pl binders kt kp args])
      have evaluatedQ: "paper_R_apply_vector \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N)
          ?types (paper_bbk_denote ?N ?k ?LQ) xs = paper_bbk_denote ?N ?u Q"
        by (rule Target.paper_R_lam_vec_application_denote[OF ql binders kt kq args])
      show ?thesis by (simp only: shape paper_R_intension_on_member arrow origin args
        transportedP transportedQ evaluatedP evaluatedQ tested)
    qed
  qed
qed

section \<open>Intensionality yields equality of the abstractions\<close>

text \<open>
  Injectivity of int𝒞M at G(n₁)→⋯→G(nₖ)→t turns the preceding
  equality of intensions into equality of denotations. The empty vector
  includes propositional equivalence. Status: the semantic denotation
  step for vector Equivalence, not a native C presentation equivalence
  or a completeness theorem.
\<close>

theorem paper_R_intensional_abstraction_denotation:
  fixes \<Sigma> :: "'c ssignature" and M :: "('c,'v) paper_bbk_model_data"
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and common: "\<And>N k. N \<in> Obj \<Longrightarrow> named_env_typed (paper_bbk_domain N) G k \<Longrightarrow>
      named_adequate k P \<Longrightarrow> named_adequate k Q \<Longrightarrow>
      paper_bbk_valuation N (paper_bbk_denote N k P) = paper_bbk_valuation N (paper_bbk_denote N k Q)"
    and object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and pa: "named_adequate g (named_lam_vec ns P)" and qa: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_bbk_denote M g (named_lam_vec ns P) = paper_bbk_denote M g (named_lam_vec ns Q)"
proof -
  let ?t = "paper_type_vector (map G ns) Prop"
  have valid: "paper_R_bbk_data_valid \<Sigma> G M" by (rule paper_R_bbk_subcategory_models[OF category object])
  have lpl: "paper_R_in_language \<Sigma> G (named_lam_vec ns P) ?t"
    by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lql: "paper_R_in_language \<Sigma> G (named_lam_vec ns Q) ?t"
    by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have pm: "paper_bbk_denote M g (named_lam_vec ns P) \<in> paper_bbk_domain M ?t"
    by (rule paper_R_bbk_data_denote_type[OF valid lpl typed pa])
  have qm: "paper_bbk_denote M g (named_lam_vec ns Q) \<in> paper_bbk_domain M ?t"
    by (rule paper_R_bbk_data_denote_type[OF valid lql typed qa])
  have equal: "paper_R_intension_on \<Sigma> G Arrows M (map G ns) (paper_bbk_denote M g (named_lam_vec ns P)) =
      paper_R_intension_on \<Sigma> G Arrows M (map G ns) (paper_bbk_denote M g (named_lam_vec ns Q))"
    by (rule paper_R_common_truth_abstraction_intensions[OF category pl ql binders common object typed pa qa])
  have injective: "inj_on (paper_R_intension_on \<Sigma> G Arrows M (map G ns)) (paper_bbk_domain M ?t)"
    using intensional object binders unfolding paper_R_intensional_on_def by blast
  show ?thesis by (rule inj_onD[OF injective equal pm qm])
qed

end
