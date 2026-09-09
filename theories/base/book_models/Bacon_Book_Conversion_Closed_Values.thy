theory Bacon_Book_Conversion_Closed_Values
  imports Bacon_Book_Conversion_Denotation Bacon_Book_Conversion_Domain_Inhabitation
    Bacon_Book_Conversion_Logical_Values Bacon_Book_Conversion_Environment Bacon_Book_Closed_Values
begin

section \<open>An actual total assignment in the full witness signature\<close>

text \<open>
  Every Dσ in the constructed full witness signature is nonempty.
  Select g₀(n)∈DG(n); this gives an actual typed total assignment,
  not a choice from a possibly empty collection of assignments.
  Source role: Definition 14.11, p.296, and the defined closed-denotation
  convention on p.298, applied to the term construction on pp.320–321.

  Representation. The choice function below is total, but its claimed
  domain membership is guarded by richness of G, which supplies the
  independently proved closed-term inhabitation of every full-signature
  domain. No consistency, valuation, or model assumption is needed.
\<close>

definition book_henkin_conversion_assignment ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c book_henkin_name) book_named_term set" where
  "book_henkin_conversion_assignment \<Sigma> G n =
    (SOME X. X \<in> book_conversion_domain (book_henkin_full_signature \<Sigma> G) G (G n))"

theorem book_henkin_conversion_assignment_typed:
  assumes rich: "sg_rich G"
  shows "book_env_typed (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
    (book_henkin_conversion_assignment \<Sigma> G)"
proof (unfold book_env_typed_def, rule allI)
  fix n
  have nonempty: "book_conversion_domain (book_henkin_full_signature \<Sigma> G) G (G n) \<noteq> {}"
    by (rule book_henkin_conversion_domain_nonempty[OF rich])
  show "book_henkin_conversion_assignment \<Sigma> G n \<in>
    book_conversion_domain (book_henkin_full_signature \<Sigma> G) G (G n)"
    unfolding book_henkin_conversion_assignment_def
    by (rule book_domain_choice[where D="book_conversion_domain (book_henkin_full_signature \<Sigma> G) G"
      and \<sigma>="G n", OF nonempty])
qed

corollary book_henkin_conversion_assignment_exists:
  assumes rich: "sg_rich G"
  shows "\<exists>g. book_env_typed (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G g"
  by (rule exI[where x="book_henkin_conversion_assignment \<Sigma> G"];
      rule book_henkin_conversion_assignment_typed[OF rich])

section \<open>Logical-symbol denotations and their definedness witnesses\<close>

text \<open>
  Jg(l)=κ(l)=[l]type(l) for every assignment g, since l is closed.
  In the full witness signature, the displayed g₀ is a typed assignment
  witnessing this equation simultaneously for every minimal logical symbol.

  These are the actual assignment and denotation witnesses used by
  book_closed_value_intro below. The separately proved full-environment
  theorem supplies its interpretation; it is not an added hypothesis.
  The resulting defined closed values do not by themselves establish a
  logical model or its truth clauses.
\<close>

theorem book_conversion_logical_denote:
  "book_conversion_denote \<Sigma> G g (NLogical l) = book_conversion_logical_value \<Sigma> G l"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical l) (book_minimal_logical_type l)"
    by (rule book_closed_terms_language[OF book_conversion_logical_closed_terms])
  have closed: "named_fv (NLogical l) = {}" by simp
  show ?thesis unfolding book_conversion_logical_value_def
    by (rule book_conversion_denote_closed[OF language closed])
qed

theorem book_henkin_conversion_logical_witness:
  assumes rich: "sg_rich G"
  shows "\<exists>g. book_env_typed (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G g \<and>
    (\<forall>l. book_conversion_denote (book_henkin_full_signature \<Sigma> G) G g (NLogical l) =
      book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G l)"
  by (rule exI[where x="book_henkin_conversion_assignment \<Sigma> G"],
      rule conjI[OF book_henkin_conversion_assignment_typed[OF rich]],
      rule allI, rule book_conversion_logical_denote)

theorem book_henkin_conversion_closed_witness:
  assumes rich: "sg_rich G"
    and language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G A \<tau>"
    and closed: "named_fv A = {}"
  shows "\<exists>g. book_env_typed (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G g \<and>
    book_conversion_denote (book_henkin_full_signature \<Sigma> G) G g A =
      book_conversion_class (book_henkin_full_signature \<Sigma> G) G \<tau> A"
  by (rule exI[where x="book_henkin_conversion_assignment \<Sigma> G"],
      rule conjI[OF book_henkin_conversion_assignment_typed[OF rich]],
      rule book_conversion_denote_closed[OF language closed])

section \<open>Defined closed values in the independently constructed environment\<close>

context
  fixes \<Sigma> :: "'c ssignature" and G :: sgcontext
begin

interpretation Book_Henkin_Conversion: book_full_environment
  "book_conversion_domain (book_henkin_full_signature \<Sigma> G) G"
  "book_conversion_app (book_henkin_full_signature \<Sigma> G) G"
  book_minimal_logical_type UNIV "book_henkin_full_signature \<Sigma> G" G
  "book_conversion_denote (book_henkin_full_signature \<Sigma> G) G"
  by (rule book_conversion_full_environment)

theorem book_henkin_conversion_closed_value:
  assumes rich: "sg_rich G"
    and language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G A \<tau>"
    and closed: "named_fv A = {}"
  shows "Book_Henkin_Conversion.book_closed_value \<tau> A
    (book_conversion_class (book_henkin_full_signature \<Sigma> G) G \<tau> A)"
proof -
  let ?g = "book_henkin_conversion_assignment \<Sigma> G"
  have typed: "book_env_typed (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G ?g"
    by (rule book_henkin_conversion_assignment_typed[OF rich])
  have defined: "Book_Henkin_Conversion.book_closed_value \<tau> A
    (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G ?g A)"
    by (rule Book_Henkin_Conversion.book_closed_value_intro[OF UNIV_I language closed typed])
  show ?thesis using defined by (simp only: book_conversion_denote_closed[OF language closed])
qed

theorem book_henkin_conversion_logical_closed_value:
  assumes rich: "sg_rich G"
  shows "Book_Henkin_Conversion.book_closed_value (book_minimal_logical_type l) (NLogical l)
    (book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G l)"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV
    (book_henkin_full_signature \<Sigma> G) G (NLogical l) (book_minimal_logical_type l)"
    by (rule book_language_Logical[OF UNIV_I])
  have closed: "named_fv (NLogical l) = {}" by simp
  show ?thesis unfolding book_conversion_logical_value_def
    by (rule book_henkin_conversion_closed_value[OF rich language closed])
qed

end

end
