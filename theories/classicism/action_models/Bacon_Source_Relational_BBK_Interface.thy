theory Bacon_Source_Relational_BBK_Interface
  imports Bacon_Source_Relational_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>Independent named BBK clauses for the default R language\<close>

text \<open>
  M=⟨D,⟦·⟧,V⟩ interprets R terms under typed partial assignments
  adequate for the interpreted terms. Source: Bacon–Dorr §1.1, p.5,
  and Definition 3.1, pp.43–44. The stock is rich at R types, and
  Dσ is nonempty for every σ∈R. Identity truth is actual identity;
  application congruence retains the printed heterogeneous type guards.

  Representation: paper_R_bbk_model repeats the thirteen independent
  source fields with R language and R conversion guards. The additional
  domain_empty field fixes Dσ={} outside R, extending the source's
  R-indexed family to the ambient F datatype. This is an off-index
  representation convention, not an additional condition on R domains.
  It prevents typed partial assignments from assigning non-R variables.

  Conversion is paper_R_raw_beta_eta, with R-typed intermediates and no
  signature restriction internally; only interpreted endpoints belong to Σ.
  The F model predicate and F conversion invariance are not assumptions.
  Status: independent interface only, not existence, soundness, an R↔F
  model bridge, or conservativity. No Functionality or disjoint-domain
  condition is added, and no total-assignment completion is presumed.
\<close>

locale paper_R_bbk_model =
  fixes signature :: "'c ssignature" and stock :: sgcontext
    and domain :: "otype \<Rightarrow> 'v set"
    and denote :: "'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool"
  assumes stock_rich: "paper_R_rich stock"
    and domain_nonempty: "paper_R_type \<sigma> \<Longrightarrow> domain \<sigma> \<noteq> {}"
    and domain_empty: "\<not> paper_R_type \<sigma> \<Longrightarrow> domain \<sigma> = {}"
    and denote_type:
      "paper_R_in_language signature stock A \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       denote g A \<in> domain \<sigma>"
    and denote_var:
      "named_env_typed domain stock g \<Longrightarrow> g n = Some a \<Longrightarrow> denote g (NVar n) = a"
    and denote_application_cong:
      "paper_R_in_language signature stock F (Arr \<sigma> \<tau>) \<Longrightarrow>
       paper_R_in_language signature stock A \<sigma> \<Longrightarrow>
       paper_R_in_language signature stock H (Arr \<upsilon> \<rho>) \<Longrightarrow>
       paper_R_in_language signature stock B \<upsilon> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_env_typed domain stock h \<Longrightarrow>
       named_adequate g (NApp F A) \<Longrightarrow> named_adequate h (NApp H B) \<Longrightarrow>
       denote g F = denote h H \<Longrightarrow> denote g A = denote h B \<Longrightarrow>
       denote g (NApp F A) = denote h (NApp H B)"
    and denote_locality:
      "paper_R_in_language signature stock A \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_env_typed domain stock h \<Longrightarrow>
       named_adequate g A \<Longrightarrow> named_adequate h A \<Longrightarrow>
       (\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n) \<Longrightarrow> denote g A = denote h A"
    and denote_beta_eta:
      "paper_R_raw_beta_eta stock \<sigma> A B \<Longrightarrow>
       paper_R_in_language signature stock A \<sigma> \<Longrightarrow>
       paper_R_in_language signature stock B \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> denote g A = denote g B"
    and valuation_neg:
      "paper_R_in_language signature stock A Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       valuation (denote g (NApp (NLogical SNot) A)) = (\<not> valuation (denote g A))"
    and valuation_conj:
      "paper_R_in_language signature stock A Prop \<Longrightarrow>
       paper_R_in_language signature stock B Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> valuation (denote g (NApp (NApp (NLogical SAnd) A) B)) =
       (valuation (denote g A) \<and> valuation (denote g B))"
    and valuation_disj:
      "paper_R_in_language signature stock A Prop \<Longrightarrow>
       paper_R_in_language signature stock B Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> valuation (denote g (NApp (NApp (NLogical SOr) A) B)) =
       (valuation (denote g A) \<or> valuation (denote g B))"
    and valuation_forall:
      "paper_R_in_language signature stock F (Arr \<sigma> Prop) \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g F \<Longrightarrow>
       stock n = \<sigma> \<Longrightarrow> n \<notin> named_fv F \<Longrightarrow>
       valuation (denote g (NApp (NLogical (SAll \<sigma>)) F)) =
       (\<forall>a \<in> domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    and valuation_exists:
      "paper_R_in_language signature stock F (Arr \<sigma> Prop) \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g F \<Longrightarrow>
       stock n = \<sigma> \<Longrightarrow> n \<notin> named_fv F \<Longrightarrow>
       valuation (denote g (NApp (NLogical (SEx \<sigma>)) F)) =
       (\<exists>a \<in> domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    and valuation_identity:
      "paper_R_in_language signature stock A \<sigma> \<Longrightarrow>
       paper_R_in_language signature stock B \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow>
       valuation (denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (denote g A = denote g B)"
begin

definition paper_R_satisfies :: "'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_R_satisfies g A \<longleftrightarrow> valuation (denote g A)"

definition paper_R_valid :: "'c paper_named_term \<Rightarrow> bool" where
  "paper_R_valid A \<longleftrightarrow> paper_R_in_language signature stock A Prop \<and>
    (\<forall>g. named_env_typed domain stock g \<longrightarrow> named_adequate g A \<longrightarrow> paper_R_satisfies g A)"

lemma paper_R_domain_member_type:
  assumes member: "a \<in> domain \<sigma>"
  shows "paper_R_type \<sigma>"
proof (rule ccontr)
  assume outside: "\<not> paper_R_type \<sigma>"
  have "domain \<sigma> = {}" by (rule domain_empty[OF outside])
  with member show False by simp
qed

lemma paper_R_assigned_variable_type:
  assumes typed: "named_env_typed domain stock g" and assigned: "g n = Some a"
  shows "paper_R_type (stock n)"
  by (rule paper_R_domain_member_type[OF named_env_value[OF typed assigned]])

lemma paper_R_assignment_undefined_outside:
  assumes typed: "named_env_typed domain stock g" and outside: "\<not> paper_R_type (stock n)"
  shows "g n = None"
proof (cases "g n")
  case None
  then show ?thesis .
next
  case (Some a)
  have "paper_R_type (stock n)" by (rule paper_R_assigned_variable_type[OF typed Some])
  with outside show ?thesis by contradiction
qed

lemma paper_R_predicate_domain_nonempty:
  assumes language: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
  shows "domain \<sigma> \<noteq> {}"
proof -
  have arrow_type: "paper_R_type (Arr \<sigma> Prop)"
    by (rule paper_R_language_result_type[OF language])
  have argument_type: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF arrow_type])
  show ?thesis by (rule domain_nonempty[OF argument_type])
qed

end

end
