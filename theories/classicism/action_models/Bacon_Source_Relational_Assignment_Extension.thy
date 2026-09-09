theory Bacon_Source_Relational_Assignment_Extension
  imports Bacon_Source_Relational_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>R terms use only R-typed free variables\<close>

text \<open>
  If A:σ in R and n∈FV(A), then G(n)∈R. This follows from the
  independent R grammar, not merely from the result type of A.
  Source: Bacon–Dorr §1.1, p.5. This support fact permits adequate
  partial assignments without values for variables of non-R types.
\<close>

lemma paper_R_has_type_fv_types:
  assumes typed: "paper_R_has_type G A \<sigma>"
  shows "\<forall>n\<in>named_fv A. paper_R_type (G n)"
  using typed by (induction rule: paper_R_has_type.induct) auto

lemma paper_R_language_fv_type:
  assumes language: "paper_R_in_language \<Sigma> G A \<sigma>" and free: "n \<in> named_fv A"
  shows "paper_R_type (G n)"
  using language free paper_R_has_type_fv_types
  unfolding paper_R_in_language_def by blast

section \<open>Fill missing R slots and preserve every existing value\<close>

text \<open>
  Extend g by choosing a value in D(G(n)) at each missing R-typed
  slot. Keep every old value, and leave missing non-R slots undefined.
  Source role: the adequate-assignment convention of Definition 3.1,
  pp.43–44. This is a derived assignment construction, not a model field.

  Representation: paper_R_complete_assignment remains option-valued.
  Its typedness uses nonempty domains only at R types. It is not the
  existing full-G total-completion notion and requires no F model.
\<close>

definition paper_R_complete_assignment ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow> 'v named_assignment \<Rightarrow> 'v named_assignment" where
  "paper_R_complete_assignment D G g n =
    (case g n of Some a \<Rightarrow> Some a
     | None \<Rightarrow> if paper_R_type (G n) then Some (SOME a. a \<in> D (G n)) else None)"

lemma paper_R_complete_assignment_Some:
  assumes assigned: "g n = Some a"
  shows "paper_R_complete_assignment D G g n = Some a"
  by (simp add: paper_R_complete_assignment_def assigned)

lemma paper_R_complete_assignment_None_iff:
  "paper_R_complete_assignment D G g n = None \<longleftrightarrow> g n = None \<and> \<not> paper_R_type (G n)"
  by (cases "g n") (simp_all add: paper_R_complete_assignment_def)

lemma paper_R_complete_assignment_domain:
  "dom (paper_R_complete_assignment D G g) = dom g \<union> {n. paper_R_type (G n)}"
  by (auto simp: dom_def paper_R_complete_assignment_None_iff)

lemma paper_R_complete_assignment_typed:
  assumes nonempty: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> D \<sigma> \<noteq> {}"
    and typed: "named_env_typed D G g"
  shows "named_env_typed D G (paper_R_complete_assignment D G g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "paper_R_complete_assignment D G g n = Some a"
  show "a \<in> D (G n)"
  proof (cases "g n")
    case (Some b)
    have equal: "a = b" using assigned
      by (simp only: paper_R_complete_assignment_Some[where g=g and n=n, OF Some] option.inject)
    have member: "b \<in> D (G n)" by (rule named_env_value[OF typed Some])
    show ?thesis by (simp only: equal; rule member)
  next
    case None
    have rt: "paper_R_type (G n)" and chosen: "a = (SOME b. b \<in> D (G n))"
      using assigned by (auto simp: paper_R_complete_assignment_def None split: if_splits)
    have exists: "\<exists>b. b \<in> D (G n)" using nonempty[OF rt] by blast
    have member: "(SOME b. b \<in> D (G n)) \<in> D (G n)" by (rule someI_ex[OF exists])
    show ?thesis by (simp only: chosen; rule member)
  qed
qed

lemma paper_R_complete_assignment_adequate:
  assumes typed: "paper_R_has_type G A \<sigma>"
  shows "named_adequate (paper_R_complete_assignment D G g) A"
  using paper_R_has_type_fv_types[OF typed]
  by (auto simp: named_adequate_def paper_R_complete_assignment_domain)

lemma paper_R_complete_assignment_language_adequate:
  assumes language: "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "named_adequate (paper_R_complete_assignment D G g) A"
  using language unfolding paper_R_in_language_def
  by (blast intro: paper_R_complete_assignment_adequate)

lemma paper_R_complete_assignment_agrees:
  assumes adequate: "named_adequate g A" and free: "n \<in> named_fv A"
  shows "paper_R_complete_assignment D G g n = g n"
proof -
  have defined: "n \<in> dom g" using adequate free unfolding named_adequate_def by blast
  obtain a where assigned: "g n = Some a" using defined by blast
  show ?thesis by (simp only: assigned paper_R_complete_assignment_Some[where g=g and n=n, OF assigned])
qed

text \<open>
  Adequacy of the constructed assignment is syntactic and needs no
  nonemptiness hypothesis. Nonemptiness is essential for its typedness.
  These two claims are intentionally separate: an arbitrary Hilbert-choice
  value from an empty domain would give adequacy but not a typed assignment.
\<close>

end
