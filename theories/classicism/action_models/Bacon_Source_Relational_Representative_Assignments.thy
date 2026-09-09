theory Bacon_Source_Relational_Representative_Assignments
  imports Bacon_Source_Relational_Identity_Representatives
begin

section \<open>Partial assignments of closed representatives\<close>

definition paper_R_representative_assignment ::
  "('c paper_named_term set) named_assignment \<Rightarrow> ('c paper_named_term) named_assignment" where
  "paper_R_representative_assignment g n = map_option paper_R_identity_rep (g n)"

definition paper_R_closed_term_assignment ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c paper_named_term) named_assignment \<Rightarrow> bool" where
  "paper_R_closed_term_assignment \<Sigma> G r \<longleftrightarrow>
    (\<forall>n A. r n = Some A \<longrightarrow> A \<in> paper_R_closed_terms \<Sigma> G (G n))"

lemma paper_R_representative_assignment_apply:
  "paper_R_representative_assignment g n = map_option paper_R_identity_rep (g n)"
  by (simp only: paper_R_representative_assignment_def)

lemma paper_R_representative_assignment_domain:
  "dom (paper_R_representative_assignment g) = dom g"
  by (rule set_eqI; simp add: dom_def paper_R_representative_assignment_def split: option.splits)

lemma paper_R_representative_assignment_adequate_iff:
  "named_adequate (paper_R_representative_assignment g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_R_representative_assignment_domain)

lemma paper_R_representative_assignment_update:
  "paper_R_representative_assignment (g(n := Some X)) =
    (paper_R_representative_assignment g)(n := Some (paper_R_identity_rep X))"
  by (rule ext; simp add: paper_R_representative_assignment_def)

lemma paper_R_representative_assignment_delete:
  "paper_R_representative_assignment (g(n := None)) = (paper_R_representative_assignment g)(n := None)"
  by (rule ext; simp add: paper_R_representative_assignment_def)

lemma paper_R_closed_term_assignmentD:
  "paper_R_closed_term_assignment \<Sigma> G r \<Longrightarrow> r n = Some A \<Longrightarrow>
    A \<in> paper_R_closed_terms \<Sigma> G (G n)"
  unfolding paper_R_closed_term_assignment_def by blast

lemma paper_R_closed_term_assignment_delete:
  assumes typed: "paper_R_closed_term_assignment \<Sigma> G r"
  shows "paper_R_closed_term_assignment \<Sigma> G (r(n := None))"
  using typed unfolding paper_R_closed_term_assignment_def by auto

theorem paper_R_representative_assignment_typed:
  assumes typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
  shows "paper_R_closed_term_assignment \<Sigma> G (paper_R_representative_assignment g)"
proof (unfold paper_R_closed_term_assignment_def, intro allI impI)
  fix n A
  assume assigned: "paper_R_representative_assignment g n = Some A"
  obtain X where original: "g n = Some X" and shape: "A = paper_R_identity_rep X"
    using assigned by (cases "g n") (auto simp: paper_R_representative_assignment_def)
  have domain: "X \<in> paper_R_identity_domain \<Sigma> G S (G n)" by (rule named_env_value[OF typed original])
  show "A \<in> paper_R_closed_terms \<Sigma> G (G n)"
    by (simp only: shape; rule paper_R_identity_rep_closed_terms[OF domain])
qed

text \<open>
  Every defined entry is replaced by a member of its actual identity
  class; undefined entries remain undefined. Domain and adequacy are
  unchanged, and each assigned representative is closed and R-typed at
  the variable's fixed type. Source: the interpretation described in
  Theorem 3.2, p.45 n.64. No total variable stock, completion, consistency,
  Henkin property or representative-independence theorem is assumed.
\<close>

end
