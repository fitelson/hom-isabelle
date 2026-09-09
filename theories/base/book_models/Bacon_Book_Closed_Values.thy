theory Bacon_Book_Closed_Values
  imports Bacon_Book_Environment
begin

section \<open>Defined closed denotations and assignment availability\<close>

text \<open>
  Convention 14.3, p.298, suppresses an assignment for a closed term.
  Record a closed value a by exhibiting a typed assignment at which the
  term denotes a. The environment condition then makes that value unique
  and the same at every typed assignment.

  The existential witness is not hidden by a choice from an empty set.
  For an admitted closed well-typed term, existence of such a value is
  equivalent to existence of a typed assignment. In a rich stock, the
  latter is equivalent to nonempty domains at all types. These are
  explicit definedness facts; the raw environment condition does not by
  itself assert that any such assignment or closed value exists.
\<close>

context book_environment_conditions
begin

definition book_closed_value where
  "book_closed_value \<sigma> A a \<longleftrightarrow>
    A \<in> admitted \<and> book_in_language logical_type logical_signature signature stock A \<sigma> \<and>
    named_fv A = {} \<and> (\<exists>g. book_env_typed domain stock g \<and> denote g A = a)"

lemma book_closed_value_intro:
  assumes member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and closed: "named_fv A = {}" and typed: "book_env_typed domain stock g"
  shows "book_closed_value \<sigma> A (denote g A)"
  unfolding book_closed_value_def
  by (rule conjI[OF member], rule conjI[OF language], rule conjI[OF closed],
    rule exI[where x=g], rule conjI[OF typed refl])

theorem book_closed_value_at:
  assumes closed_value: "book_closed_value \<sigma> A a" and typed: "book_env_typed domain stock g"
  shows "denote g A = a"
proof -
  have member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and closed: "named_fv A = {}" using closed_value unfolding book_closed_value_def by auto
  obtain h where ht: "book_env_typed domain stock h" and ha: "denote h A = a"
    using closed_value unfolding book_closed_value_def by blast
  have equal: "denote g A = denote h A"
    by (rule book_denote_locality[OF member language typed ht]) (simp add: closed)
  show ?thesis by (rule trans[OF equal ha])
qed

theorem book_closed_value_unique:
  assumes first: "book_closed_value \<sigma> A a" and second: "book_closed_value \<sigma> A b"
  shows "a = b"
proof -
  obtain g where typed: "book_env_typed domain stock g" and ga: "denote g A = a"
    using first unfolding book_closed_value_def by blast
  have gb: "denote g A = b" by (rule book_closed_value_at[OF second typed])
  show ?thesis by (rule trans[OF sym[OF ga] gb])
qed

theorem book_closed_value_type:
  assumes closed_value: "book_closed_value \<sigma> A a"
  shows "a \<in> domain \<sigma>"
proof -
  have member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    using closed_value unfolding book_closed_value_def by auto
  obtain g where typed: "book_env_typed domain stock g" and ga: "denote g A = a"
    using closed_value unfolding book_closed_value_def by blast
  have belongs: "denote g A \<in> domain \<sigma>" by (rule denote_type[OF member language typed])
  show ?thesis using belongs by (simp only: ga)
qed

theorem book_closed_value_exists_iff:
  assumes member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and closed: "named_fv A = {}"
  shows "(\<exists>a. book_closed_value \<sigma> A a) \<longleftrightarrow> (\<exists>g. book_env_typed domain stock g)"
proof
  assume exists_value: "\<exists>a. book_closed_value \<sigma> A a"
  show "\<exists>g. book_env_typed domain stock g" using exists_value unfolding book_closed_value_def by blast
next
  assume exists_assignment: "\<exists>g. book_env_typed domain stock g"
  obtain g where typed: "book_env_typed domain stock g" using exists_assignment by (elim exE)
  show "\<exists>a. book_closed_value \<sigma> A a"
    by (rule exI[where x="denote g A"], rule book_closed_value_intro[OF member language closed typed])
qed

corollary book_closed_value_exists_iff_domains:
  assumes member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and closed: "named_fv A = {}" and rich: "sg_rich stock"
  shows "(\<exists>a. book_closed_value \<sigma> A a) \<longleftrightarrow> (\<forall>\<tau>. domain \<tau> \<noteq> {})"
  by (rule trans[OF book_closed_value_exists_iff[OF member language closed]
    book_total_assignment_exists_iff[OF rich]])

end

end
