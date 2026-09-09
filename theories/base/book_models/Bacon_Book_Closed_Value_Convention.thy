theory Bacon_Book_Closed_Value_Convention
  imports Bacon_Book_Closed_Values
begin

section \<open>Defined closed values and assignment-independent notation\<close>

text \<open>
  For an admitted closed A:τ, the notation J(A)=a can be read either
  as an actual defined closed value or as Jg(A)=a at every typed g,
  PROVIDED a typed assignment exists. It can equivalently be checked
  at any specified typed assignment g₀.
  Source: Bacon, Convention 14.3, p.298.

  Representation. The two equivalences below retain admission, language
  membership and closedness. Assignment availability is explicit: an
  all-assignment equation could otherwise be vacuous, whereas
  book_closed_value records an actual witness. No richness, full-language,
  domain-nonemptiness, or logical-model assumption replaces this guard.
  The existing environment condition supplies assignment independence.
\<close>

context book_environment_conditions
begin

theorem book_closed_value_iff_all_assignments:
  assumes member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<tau>"
    and closed: "named_fv A = {}"
    and available: "\<exists>g. book_env_typed domain stock g"
  shows "book_closed_value \<tau> A a \<longleftrightarrow>
    (\<forall>g. book_env_typed domain stock g \<longrightarrow> denote g A = a)"
proof
  assume defined: "book_closed_value \<tau> A a"
  show "\<forall>g. book_env_typed domain stock g \<longrightarrow> denote g A = a"
  proof (intro allI impI)
    fix g
    assume typed: "book_env_typed domain stock g"
    show "denote g A = a" by (rule book_closed_value_at[OF defined typed])
  qed
next
  assume all_assignments: "\<forall>g. book_env_typed domain stock g \<longrightarrow> denote g A = a"
  obtain g0 where typed: "book_env_typed domain stock g0" using available by (elim exE)
  have equation: "denote g0 A = a" by (rule mp[OF spec[where x=g0, OF all_assignments] typed])
  have defined: "book_closed_value \<tau> A (denote g0 A)"
    by (rule book_closed_value_intro[OF member language closed typed])
  show "book_closed_value \<tau> A a" using defined by (simp only: equation)
qed

theorem book_closed_value_iff_at:
  assumes member: "A \<in> admitted"
    and language: "book_in_language logical_type logical_signature signature stock A \<tau>"
    and closed: "named_fv A = {}"
    and typed: "book_env_typed domain stock g0"
  shows "book_closed_value \<tau> A a \<longleftrightarrow> denote g0 A = a"
proof
  assume defined: "book_closed_value \<tau> A a"
  show "denote g0 A = a" by (rule book_closed_value_at[OF defined typed])
next
  assume equation: "denote g0 A = a"
  have defined: "book_closed_value \<tau> A (denote g0 A)"
    by (rule book_closed_value_intro[OF member language closed typed])
  show "book_closed_value \<tau> A a" using defined by (simp only: equation)
qed

end

end
