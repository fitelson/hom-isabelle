theory Bacon_Source_Named_Type_Tags
  imports Bacon_Source_Named_Completion_Denotation
begin

section \<open>Explicit type tags on named semantic values\<close>

text \<open>
  Replace each Dσ by D′σ = {(σ,a) | a ∈ Dσ}. Within each type,
  a ↦ (σ,a) retains the original value; domains with distinct types are
  now disjoint. Source role: representing the typed collections of
  Bacon–Dorr Definition 3.1(i–ii), pp.43–44, while retaining its literal
  application-congruence clause even when compared terms have different
  types. No disjointness condition is imposed on the original domains.

  Isabelle representation. The carrier is otype × value. Undefined
  partial assignments remain undefined when their tags are removed.
  A named term has a selected type, which equals its unique derivable
  type whenever it is well typed. Off that guard the selected type and
  the resulting totalized denotation carry no semantic claim.

  Status. This leaf constructs tags and proves assignment, denotation
  typing, and variable facts under the weak finite-frame structure.
  It does not assume a named model or prove application, truth clauses,
  model assembly, or the converse model-class correspondence.
\<close>

definition named_tag_domain :: "(otype \<Rightarrow> 'v set) \<Rightarrow> otype \<Rightarrow> (otype \<times> 'v) set" where
  "named_tag_domain D \<sigma> = {(\<sigma>, a) |a. a \<in> D \<sigma>}"

lemma named_tag_domain_pair_iff:
  "(\<tau>, a) \<in> named_tag_domain D \<sigma> \<longleftrightarrow> \<tau> = \<sigma> \<and> a \<in> D \<sigma>"
  by (auto simp: named_tag_domain_def)

lemma named_tag_domain_iff:
  "v \<in> named_tag_domain D \<sigma> \<longleftrightarrow> fst v = \<sigma> \<and> snd v \<in> D \<sigma>"
  by (cases v) (simp only: named_tag_domain_pair_iff fst_conv snd_conv)

lemma named_tag_domain_fst:
  "v \<in> named_tag_domain D \<sigma> \<Longrightarrow> fst v = \<sigma>"
  by (simp only: named_tag_domain_iff; rule conjunct1)

lemma named_tag_domain_snd:
  "v \<in> named_tag_domain D \<sigma> \<Longrightarrow> snd v \<in> D \<sigma>"
  by (simp only: named_tag_domain_iff; rule conjunct2)

lemma named_tag_domain_disjoint:
  assumes distinct: "\<sigma> \<noteq> \<tau>"
  shows "named_tag_domain D \<sigma> \<inter> named_tag_domain D \<tau> = {}"
  using distinct by (auto simp: named_tag_domain_iff)

lemma named_tag_domain_nonempty:
  assumes nonempty: "D \<sigma> \<noteq> {}"
  shows "named_tag_domain D \<sigma> \<noteq> {}"
proof -
  obtain a where member: "a \<in> D \<sigma>" using nonempty by blast
  have tagged: "(\<sigma>, a) \<in> named_tag_domain D \<sigma>"
    using member by (simp add: named_tag_domain_pair_iff)
  show ?thesis using tagged by blast
qed

definition named_untag_assignment :: "(otype \<times> 'v) named_assignment \<Rightarrow> 'v named_assignment" where
  "named_untag_assignment g n = map_option snd (g n)"

lemma named_untag_assignment_value:
  assumes assigned: "g n = Some v"
  shows "named_untag_assignment g n = Some (snd v)"
  by (simp add: named_untag_assignment_def assigned)

lemma named_untag_assignment_value_obtain:
  assumes assigned: "named_untag_assignment g n = Some a"
  obtains v where "g n = Some v" and "snd v = a"
  using assigned unfolding named_untag_assignment_def by (cases "g n") auto

lemma named_untag_assignment_typed:
  assumes typed: "named_env_typed (named_tag_domain D) G g"
  shows "named_env_typed D G (named_untag_assignment g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "named_untag_assignment g n = Some a"
  obtain v where original: "g n = Some v" and payload: "snd v = a"
    by (rule named_untag_assignment_value_obtain[OF assigned])
  have member: "v \<in> named_tag_domain D (G n)"
    by (rule named_env_value[OF typed original])
  show "a \<in> D (G n)" using named_tag_domain_snd[OF member] by (simp only: payload)
qed

lemma named_untag_assignment_domain:
  "dom (named_untag_assignment g) = dom g"
  by (auto simp: dom_def named_untag_assignment_def split: option.splits)

lemma named_untag_assignment_adequate:
  "named_adequate (named_untag_assignment g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def named_untag_assignment_domain)

lemma named_untag_assignment_update:
  "named_untag_assignment (g(n := Some v)) = (named_untag_assignment g)(n := Some (snd v))"
  by (rule ext, rename_tac k, case_tac "k = n") (simp_all add: named_untag_assignment_def)

subsection \<open>Selecting the unique type of a well-typed named term\<close>

definition named_type_of ::
  "('l \<Rightarrow> otype) \<Rightarrow> sgcontext \<Rightarrow> ('c, 'l) named_term \<Rightarrow> otype" where
  "named_type_of L G A = (SOME \<sigma>. has_ntype L G A \<sigma>)"

lemma named_type_of_typed:
  assumes typed: "has_ntype L G A \<sigma>"
  shows "has_ntype L G A (named_type_of L G A)"
proof -
  have exists_type: "\<exists>\<tau>. has_ntype L G A \<tau>" by (rule exI[where x=\<sigma>], rule typed)
  show ?thesis unfolding named_type_of_def by (rule someI_ex[OF exists_type])
qed

lemma named_type_of_eq:
  assumes typed: "has_ntype L G A \<sigma>"
  shows "named_type_of L G A = \<sigma>"
  by (rule named_type_unique[OF named_type_of_typed[OF typed] typed])

lemma named_type_of_language:
  assumes language: "named_in_language L \<Sigma> G A \<sigma>"
  shows "named_type_of L G A = \<sigma>"
proof -
  have typed: "has_ntype L G A \<sigma>"
    using language unfolding named_in_language_def by (rule conjunct1)
  show ?thesis by (rule named_type_of_eq[OF typed])
qed

context paper_db_bbk_structure
begin

subsection \<open>Tagged denotation from the completion-independent value\<close>

definition tagged_named_denote ::
  "sgcontext \<Rightarrow> (otype \<times> 'v) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> (otype \<times> 'v)" where
  "tagged_named_denote G g A =
    (named_type_of paper_logical_type G A, named_denote G (named_untag_assignment g) A)"

lemma tagged_named_denote_eq:
  assumes typed: "has_ntype paper_logical_type G A \<sigma>"
  shows "tagged_named_denote G g A = (\<sigma>, named_denote G (named_untag_assignment g) A)"
  by (simp only: tagged_named_denote_def named_type_of_eq[OF typed])

lemma tagged_named_denote_language_eq:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
  shows "tagged_named_denote G g A = (\<sigma>, named_denote G (named_untag_assignment g) A)"
  by (simp only: tagged_named_denote_def named_type_of_language[OF language])

theorem tagged_named_denote_type:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g A"
  shows "tagged_named_denote G g A \<in> named_tag_domain domain \<sigma>"
proof -
  have untyped: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have unadequate: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have member: "named_denote G (named_untag_assignment g) A \<in> domain \<sigma>"
    by (rule paper_db_named_denote_type[OF language untyped unadequate])
  show ?thesis using member
    by (simp add: tagged_named_denote_language_eq[OF language] named_tag_domain_pair_iff)
qed

theorem tagged_named_denote_var:
  assumes typed: "named_env_typed (named_tag_domain domain) G g"
    and assigned: "g n = Some v"
  shows "tagged_named_denote G g (NVar n) = v"
proof -
  have member: "v \<in> named_tag_domain domain (G n)"
    by (rule named_env_value[OF typed assigned])
  have tag: "fst v = G n" by (rule named_tag_domain_fst[OF member])
  have untyped: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have unassigned: "named_untag_assignment g n = Some (snd v)"
    by (rule named_untag_assignment_value[where g=g and n=n and v=v, OF assigned])
  have payload: "named_denote G (named_untag_assignment g) (NVar n) = snd v"
    by (rule paper_db_named_denote_variable[OF untyped unassigned])
  have variable_type: "has_ntype paper_logical_type G (NVar n) (G n)"
    by (rule has_ntype.Var)
  have pair_eq: "(G n, snd v) = v" using tag by (cases v) simp
  show ?thesis by (simp only: tagged_named_denote_eq[OF variable_type] payload pair_eq)
qed

end

end
