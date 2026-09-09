theory Bacon_Source_Relational_Naming_Coordinate_Denotation
  imports Bacon_Source_Relational_Naming_Coordinate_Syntax
    Bacon_Source_Relational_Naming_Coordinate_Assignments
    Bacon_Source_Relational_Substitution_Denotation
begin

section \<open>One-coordinate chart independence in an arbitrary R BBK model\<close>

text \<open>
  Changing x(k) to y(k) amounts to free-for variable substitution.
  The y-chart assignment supplies the same value snd(k), and after the
  corresponding update it agrees with the x-chart assignment on every
  free variable of the x-replacement. Substitution and locality therefore
  give equality. Both chart images may overlap and g may already assign
  either marker. Full independence of arbitrary charts is not assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_chart_coordinate_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and first: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) y"
    and key: "k \<in> paper_R_naming_support A"
    and agree: "\<And>j. j \<in> paper_R_naming_support A \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
  shows "denote (paper_R_naming_override (paper_R_naming_support A) y g) (paper_R_naming_replace y A) =
    denote (paper_R_naming_override (paper_R_naming_support A) x g) (paper_R_naming_replace x A)"
proof -
  let ?K = "paper_R_naming_support A"
  let ?Ax = "paper_R_naming_replace x A"
  let ?gx = "paper_R_naming_override ?K x g"
  let ?gy = "paper_R_naming_override ?K y g"
  let ?h = "?gy(x k := Some (snd k))"
  have xi: "inj_on x ?K" by (rule paper_R_naming_chart_injective[OF first])
  have yi: "inj_on y ?K" by (rule paper_R_naming_chart_injective[OF second])
  have xt: "stock (x k) = fst k" by (rule paper_R_naming_chart_type[OF first key])
  have yt: "stock (y k) = fst k" by (rule paper_R_naming_chart_type[OF second key])
  have xf: "x k \<notin> named_vars A" by (rule paper_R_naming_chart_fresh[OF first key])
  have yf: "y k \<notin> named_vars A" by (rule paper_R_naming_chart_fresh[OF second key])
  have original_type: "paper_R_has_type stock A \<tau>"
    and names: "named_in_signature (paper_R_naming_signature signature domain) A"
    using language unfolding paper_R_in_language_def by blast+
  have rt: "paper_R_type (fst k)" using paper_R_naming_support_R_types[OF original_type] key by blast
  have payload_member: "snd k \<in> domain (stock (x k))"
    using paper_R_naming_support_values[OF names] key by (simp only: xt; blast)
  have gx_type: "named_env_typed domain stock ?gx"
    by (rule paper_R_naming_term_override_typed[OF language first typed])
  have gy_type: "named_env_typed domain stock ?gy"
    by (rule paper_R_naming_term_override_typed[OF language second typed])
  have h_type: "named_env_typed domain stock ?h"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n="x k", OF gy_type payload_member])
  have ax_language: "paper_R_in_language signature stock ?Ax \<tau>"
    by (rule paper_R_naming_replace_language[OF language first subset_refl])
  have variable: "paper_R_in_language signature stock (NVar (y k)) (stock (x k))"
    by (simp only: xt; rule paper_R_language_Var[where G=stock and n="y k", OF yt rt])
  have assigned: "?gy (y k) = Some (snd k)" by (rule paper_R_naming_override_lookup[OF yi key])
  have variable_value: "denote ?gy (NVar (y k)) = snd k" by (rule denote_var[OF gy_type assigned])
  have variable_adequate: "named_adequate ?gy (NVar (y k))"
    using assigned by (auto simp: named_adequate_def dom_def)
  have coverage: "named_fv ?Ax - {x k} \<subseteq> dom ?gy"
    by (rule paper_R_naming_coordinate_coverage[OF adequate agree])
  have free_for: "named_free_for (NVar (y k)) (x k) ?Ax"
    by (rule paper_R_naming_replace_variable_free_for[OF yf])
  have replacement: "paper_R_naming_replace y A = named_subst (x k) (NVar (y k)) ?Ax"
    by (rule paper_R_naming_replace_coordinate[OF subset_refl xi key xf agree])
  have substitution: "denote ?gy (paper_R_naming_replace y A) = denote ?h ?Ax"
    using paper_R_substitution_denote[OF ax_language variable gy_type coverage variable_adequate free_for]
    by (simp only: replacement variable_value)
  have gx_adequate: "named_adequate ?gx ?Ax"
    by (rule paper_R_naming_override_adequate[OF adequate subset_refl])
  have h_adequate: "named_adequate ?h ?Ax"
    using coverage unfolding named_adequate_def named_assignment_update_domain by blast
  have local: "denote ?h ?Ax = denote ?gx ?Ax"
  proof (rule denote_locality[OF ax_language h_type gx_type h_adequate gx_adequate])
    fix n
    assume free: "n \<in> named_fv ?Ax"
    show "?h n = ?gx n" by (rule paper_R_naming_coordinate_assignment_agrees[OF first second key agree free])
  qed
  show ?thesis by (rule trans[OF substitution local])
qed

end

end
