theory Bacon_Book_Conversion_Domain_Inhabitation
  imports Bacon_Book_Conversion_Classes Bacon_Book_Henkin_Closed_Terms
begin

section \<open>Actual nonempty canonical domains in the full signature\<close>

text \<open>
  The constructed full witness signature contains a closed term of every
  type. Its conversion class is therefore an actual member of the
  corresponding canonical domain. This discharges domain nonemptiness
  for this signature; it is not inserted into the generic quotient
  definitions or assumed from a model.
\<close>

theorem book_henkin_conversion_domain_nonempty:
  assumes rich: "sg_rich G"
  shows "book_conversion_domain (book_henkin_full_signature \<Sigma> G) G \<sigma> \<noteq> {}"
proof -
  obtain A where language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G A \<sigma>" and closed: "named_fv A = {}"
    using book_henkin_full_closed_term_exists[where \<Sigma>=\<Sigma> and \<sigma>=\<sigma>, OF rich] by blast
  have closed_term: "A \<in> book_closed_terms (book_henkin_full_signature \<Sigma> G) G \<sigma>"
    by (rule book_closed_termsI[OF language closed])
  have member: "book_conversion_class (book_henkin_full_signature \<Sigma> G) G \<sigma> A
    \<in> book_conversion_domain (book_henkin_full_signature \<Sigma> G) G \<sigma>"
    by (rule book_conversion_domainI[OF closed_term])
  show ?thesis using member by blast
qed

end
