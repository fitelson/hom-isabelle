theory Bacon_Source_Relational_Quantifier_Profile
  imports Bacon_Source_Relational_Negation_Profile
    Bacon_Source_Relational_Quantifier_Axiom_Truth
begin

section \<open>Quantifiers applied to arbitrary predicate values\<close>

text \<open>
  For every d∈Mσ→t, ∀σ(d) is true exactly when every a∈Mσ
  makes d(a) true; ∃σ uses some a∈Mσ. A fresh predicate variable
  realizes d under a one-variable partial assignment. The existing
  term-level quantifier lemma separately chooses a fresh σ-variable.
  Thus neither closed denotability nor a full function space is used.
  Source: Definition 3.1(iii), p.44, and Definition 3.19, p.56.
  The Boolean parameter only packages the two displayed source clauses.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_quantifier_value_truth:
  assumes rt: "paper_R_type \<sigma>" and member: "d \<in> domain (Arr \<sigma> Prop)"
  shows "valuation (paper_R_application signature stock domain denote (Arr \<sigma> Prop) Prop
      (denote Map.empty (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) d) =
    (if universal then \<forall>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop d a)
     else \<exists>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop d a))"
proof -
  let ?l = "if universal then SAll \<sigma> else SEx \<sigma>"
  have pr: "paper_R_type (Arr \<sigma> Prop)" using rt by simp
  have qr: "paper_R_type (paper_logical_type ?l)" using rt by (cases universal; simp)
  obtain n where nt: "stock n = Arr \<sigma> Prop" and nf: "n \<notin> {}"
    by (rule paper_R_rich_fresh[OF stock_rich pr finite.emptyI])
  let ?g = "Map.empty(n := Some d)"
  have dt: "d \<in> domain (stock n)" by (simp only: nt; rule member)
  have gt: "named_env_typed domain stock ?g"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF paper_R_empty_assignment_typed dt])
  have vl: "paper_R_in_language signature stock (NVar n) (Arr \<sigma> Prop)"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt pr])
  have ql: "paper_R_in_language signature stock (NLogical ?l) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_logical_language[where \<Sigma>=signature and G=stock, OF qr]
    by (cases universal; simp)
  have va: "named_adequate ?g (NVar n :: 'c paper_named_term)"
    by (simp add: named_adequate_def dom_def)
  have whole: "named_adequate ?g (NApp (NLogical ?l) (NVar n) :: 'c paper_named_term)"
    by (simp add: named_adequate_def dom_def)
  have vv: "denote ?g (NVar n) = d" by (rule denote_var[OF gt]; simp)
  have qv: "denote ?g (NLogical ?l) = denote Map.empty (NLogical ?l)"
    by (rule paper_R_logical_denote_empty[OF qr gt])
  have applied: "paper_R_application signature stock domain denote (Arr \<sigma> Prop) Prop
      (denote Map.empty (NLogical ?l)) d = denote ?g (NApp (NLogical ?l) (NVar n))"
    using paper_R_application_denote[OF ql vl gt whole] by (simp only: qv vv)
  have all: "valuation (denote ?g (NApp (NLogical (SAll \<sigma>)) (NVar n))) =
      (\<forall>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop d a))"
    using paper_R_forall_application_truth[OF vl gt va] by (simp only: named_paper_all_def vv)
  have ex: "valuation (denote ?g (NApp (NLogical (SEx \<sigma>)) (NVar n))) =
      (\<exists>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop d a))"
    using paper_R_exists_application_truth[OF vl gt va] by (simp only: named_paper_ex_def vv)
  show ?thesis by (simp only: applied; cases universal; simp only: if_True if_False all ex)
qed

end

section \<open>Every outgoing test uses the entire target domain\<close>

lemma paper_R_quantifier_profile_value:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and object: "M \<in> Obj" and rt: "paper_R_type \<sigma>"
    and member: "d \<in> paper_bbk_domain M (Arr \<sigma> Prop)"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
  shows "paper_bbk_valuation (paper_arrow_target h)
      (paper_arrow_map h Prop (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
        (Arr \<sigma> Prop) Prop (paper_bbk_denote M Map.empty
          (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) d)) =
    (if universal then \<forall>a\<in>paper_bbk_domain (paper_arrow_target h) \<sigma>.
       paper_bbk_valuation (paper_arrow_target h) (paper_R_application \<Sigma> G
         (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
         \<sigma> Prop (paper_arrow_map h (Arr \<sigma> Prop) d) a)
     else \<exists>a\<in>paper_bbk_domain (paper_arrow_target h) \<sigma>.
       paper_bbk_valuation (paper_arrow_target h) (paper_R_application \<Sigma> G
         (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
         \<sigma> Prop (paper_arrow_map h (Arr \<sigma> Prop) d) a))"
proof -
  let ?l = "if universal then SAll \<sigma> else SEx \<sigma>"
  interpret Source: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF category object]])
  have morphism: "paper_R_bbk_model_morphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
    (paper_bbk_valuation (paper_arrow_target h)) (paper_arrow_map h)"
    using paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF category arrow]]
    by (simp only: paper_R_bbk_data_morphism_def source)
  interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain (paper_arrow_target h)"
    "paper_bbk_denote (paper_arrow_target h)" "paper_bbk_valuation (paper_arrow_target h)"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  have qr: "paper_R_type (paper_logical_type ?l)" and ar: "paper_R_type (Arr (Arr \<sigma> Prop) Prop)"
    using rt by (cases universal; simp)+
  have qt: "paper_bbk_denote M Map.empty (NLogical ?l) \<in> paper_bbk_domain M (Arr (Arr \<sigma> Prop) Prop)"
    using Source.paper_R_logical_denote_type[OF qr] by (cases universal; simp)
  have dm: "paper_arrow_map h (Arr \<sigma> Prop) d \<in> paper_bbk_domain (paper_arrow_target h) (Arr \<sigma> Prop)"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] member])
  have logical: "paper_arrow_map h (Arr (Arr \<sigma> Prop) Prop) (paper_bbk_denote M Map.empty (NLogical ?l)) =
    paper_bbk_denote (paper_arrow_target h) Map.empty (NLogical ?l)"
    using paper_R_logical_morphism_empty[OF morphism qr] by (cases universal; simp)
  have applied: "paper_arrow_map h Prop (paper_R_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (Arr \<sigma> Prop) Prop (paper_bbk_denote M Map.empty (NLogical ?l)) d) =
    paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
      (Arr \<sigma> Prop) Prop (paper_bbk_denote (paper_arrow_target h) Map.empty (NLogical ?l))
      (paper_arrow_map h (Arr \<sigma> Prop) d)"
    using paper_R_application_morphism[OF morphism ar qt member] by (simp only: logical)
  show ?thesis by (simp only: applied; rule Target.paper_R_quantifier_value_truth[OF rt dm])
qed

end
