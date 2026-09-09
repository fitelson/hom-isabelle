theory Bacon_Source_Relational_Application
  imports Bacon_Source_Relational_Application_Graph
begin

section \<open>Application is reconstructed inside an independent R model\<close>

text \<open>
  For σ→τ∈R, d∈Dσ→τ and a∈Dσ, the value appσ,τ(d,a)
  exists and is independent of the chosen application witness.
  Source: Bacon–Dorr Definition 3.1(ii.b), pp.43–44, and
  Definition 3.3 with footnote 65, pp.45–46.

  Every theorem in this context uses only paper_R_bbk_model. Existence
  uses its R-rich stock and an explicit finite partial assignment.
  Total-assignment completion is neither used nor assumed; non-R
  variable names remain unassigned. The chosen operation is unconstrained
  outside its displayed R-type and domain guards. No F model, Functionality,
  fullness or closed representation of arbitrary domain elements is used.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_application_graph_exists:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and dm: "d \<in> domain (Arr \<sigma> \<tau>)" and am: "a \<in> domain \<sigma>"
  shows "\<exists>b. paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a b"
proof -
  have argument_type: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  obtain x where xt: "stock x = Arr \<sigma> \<tau>" and xf: "x \<notin> {}"
    by (rule paper_R_rich_fresh[OF stock_rich rt finite.emptyI])
  have finite_x: "finite {x}" by simp
  obtain y where yt: "stock y = \<sigma>" and yf: "y \<notin> {x}"
    by (rule paper_R_rich_fresh[OF stock_rich argument_type finite_x])
  have distinct: "x \<noteq> y" using yf by auto
  let ?g = "(Map.empty(x := Some d))(y := Some a)"
  have empty_typed: "named_env_typed domain stock Map.empty"
    by (simp only: named_env_typed_def; simp)
  have dx: "d \<in> domain (stock x)" by (simp only: xt; rule dm)
  have ay: "a \<in> domain (stock y)" by (simp only: yt; rule am)
  have first_typed: "named_env_typed domain stock (Map.empty(x := Some d))"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF empty_typed dx])
  have typed: "named_env_typed domain stock ?g"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF first_typed ay])
  have gx: "?g x = Some d" by (simp add: distinct)
  have gy: "?g y = Some a" by simp
  have head: "paper_R_in_language signature stock (NVar x) (Arr \<sigma> \<tau>)"
    by (rule paper_R_language_Var[where G=stock and n=x, OF xt rt])
  have argument: "paper_R_in_language signature stock (NVar y) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=y, OF yt argument_type])
  have adequate: "named_adequate ?g (NApp (NVar x) (NVar y) :: 'c paper_named_term)"
    by (simp add: named_adequate_def named_fv.simps dom_def distinct)
  have head_value: "denote ?g (NVar x) = d" by (rule denote_var[OF typed gx])
  have arg_value: "denote ?g (NVar y) = a" by (rule denote_var[OF typed gy])
  have graph: "paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a
    (denote ?g (NApp (NVar x) (NVar y)))"
    by (rule paper_R_application_graphI[where J=denote and D=domain and g="?g",
      OF head argument typed adequate head_value arg_value refl])
  show ?thesis by (rule exI[where x="denote ?g (NApp (NVar x) (NVar y))"], rule graph)
qed

lemma paper_R_application_graph_unique:
  assumes first: "paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a b"
    and second: "paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a c"
  shows "b = c"
proof -
  obtain g F A where fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and gt: "named_env_typed domain stock g" and ga: "named_adequate g (NApp F A)"
    and fv: "denote g F = d" and av: "denote g A = a" and bv: "denote g (NApp F A) = b"
    by (rule paper_R_application_graphE[OF first])
  obtain h H B where hl: "paper_R_in_language signature stock H (Arr \<sigma> \<tau>)"
    and bl: "paper_R_in_language signature stock B \<sigma>"
    and ht: "named_env_typed domain stock h" and ha: "named_adequate h (NApp H B)"
    and hv: "denote h H = d" and avb: "denote h B = a" and cv: "denote h (NApp H B) = c"
    by (rule paper_R_application_graphE[OF second])
  have heads: "denote g F = denote h H" by (simp only: fv hv)
  have args: "denote g A = denote h B" by (simp only: av avb)
  have apps: "denote g (NApp F A) = denote h (NApp H B)"
    by (rule denote_application_cong[OF fl al hl bl gt ht ga ha heads args])
  show ?thesis using apps by (simp only: bv cv)
qed

lemma paper_R_application_graph_type:
  assumes graph: "paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a b"
  shows "b \<in> domain \<tau>"
proof -
  obtain g F A where fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g (NApp F A)"
    and app_value: "denote g (NApp F A) = b"
    by (rule paper_R_application_graphE[OF graph]; rule that; assumption)
  have application: "paper_R_in_language signature stock (NApp F A) \<tau>"
    by (rule paper_R_language_App[OF fl al])
  have member: "denote g (NApp F A) \<in> domain \<tau>" by (rule denote_type[OF application typed adequate])
  show ?thesis using member by (simp only: app_value)
qed

section \<open>The chosen result and denotation recovery\<close>

text \<open>
  Hilbert choice now selects the uniquely witnessed result. For each
  R-language application FA under a typed adequate g, the selected
  operation applied to ⟦F⟧ᵍ and ⟦A⟧ᵍ returns ⟦FA⟧ᵍ.
  The R arrow guard in that recovery theorem follows from F's
  independent R-language typing, not merely from its F result type.
\<close>

lemma paper_R_application_graph_chosen:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and dm: "d \<in> domain (Arr \<sigma> \<tau>)" and am: "a \<in> domain \<sigma>"
  shows "paper_R_application_graph signature stock domain denote \<sigma> \<tau> d a
    (paper_R_application signature stock domain denote \<sigma> \<tau> d a)"
  unfolding paper_R_application_def
  by (rule someI_ex[OF paper_R_application_graph_exists[OF rt dm am]])

lemma paper_R_application_type:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and dm: "d \<in> domain (Arr \<sigma> \<tau>)" and am: "a \<in> domain \<sigma>"
  shows "paper_R_application signature stock domain denote \<sigma> \<tau> d a \<in> domain \<tau>"
  by (rule paper_R_application_graph_type[OF paper_R_application_graph_chosen[OF rt dm am]])

theorem paper_R_application_denote:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g (NApp F A)"
  shows "paper_R_application signature stock domain denote \<sigma> \<tau> (denote g F) (denote g A) =
    denote g (NApp F A)"
proof -
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have fa: "named_adequate g F" and aa: "named_adequate g A"
    using adequate by (auto simp: named_adequate_def)
  have dm: "denote g F \<in> domain (Arr \<sigma> \<tau>)" by (rule denote_type[OF fl typed fa])
  have am: "denote g A \<in> domain \<sigma>" by (rule denote_type[OF al typed aa])
  have chosen: "paper_R_application_graph signature stock domain denote \<sigma> \<tau>
    (denote g F) (denote g A)
    (paper_R_application signature stock domain denote \<sigma> \<tau> (denote g F) (denote g A))"
    by (rule paper_R_application_graph_chosen[OF rt dm am])
  have original: "paper_R_application_graph signature stock domain denote \<sigma> \<tau>
    (denote g F) (denote g A) (denote g (NApp F A))"
    by (rule paper_R_application_graphI[OF fl al typed adequate refl refl refl])
  show ?thesis by (rule paper_R_application_graph_unique[OF chosen original])
qed

end

end
