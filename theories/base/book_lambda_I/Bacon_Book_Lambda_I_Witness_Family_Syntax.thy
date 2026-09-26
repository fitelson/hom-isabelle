theory Bacon_Book_Lambda_I_Witness_Family_Syntax
  imports Bacon_Book_Lambda_I_Conditional_Witness
    Bacon_Book_Environment_Development.Bacon_Book_Witness_Family_Syntax
begin

section \<open>Witness families of λI predicates stay inside the λI language\<close>

text \<open>
  The family signature and the family axioms are those of the
  unrestricted development. When every predicate F i is a λI term, each
  family axiom is a λI formula of the family signature, and so is every
  premise of a λI premise set.
\<close>

lemma book_lambda_I_witness_family_axiom_language:
  assumes rich: "sg_rich G" and member: "i \<in> I"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and lambda_I: "book_lambda_I (F i)"
  shows "book_lambda_I_formula (book_witness_family_signature \<Sigma> \<tau> c I) G
    (book_witness_axiom G (\<tau> i) (F i) (c i))"
  by (rule conjI[OF book_witness_family_axiom_language[where \<Sigma>=\<Sigma> and G=G and \<tau>=\<tau>
      and F=F and c=c and I=I and i=i, OF rich member predicate]
    book_lambda_I_witness_axiom[OF rich lambda_I]])

lemma book_lambda_I_witness_family_premises_language:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and lambda_I: "\<And>i. i \<in> I \<Longrightarrow> book_lambda_I (F i)"
    and member: "A \<in> S \<union> book_witness_family_axioms G \<tau> F c I"
  shows "book_lambda_I_formula (book_witness_family_signature \<Sigma> \<tau> c I) G A"
proof (cases "A \<in> S")
  case True
  show ?thesis by (rule book_lambda_I_formula_signature_mono[OF language[OF True]];
    rule book_witness_family_signature_inclusion)
next
  case False
  obtain i where index: "i \<in> I" and shape: "A = book_witness_axiom G (\<tau> i) (F i) (c i)"
    using member False unfolding book_witness_family_axioms_def by blast
  show ?thesis by (simp only: shape,
    rule book_lambda_I_witness_family_axiom_language[where \<Sigma>=\<Sigma> and G=G and \<tau>=\<tau>
      and F=F and c=c and I=I and i=i, OF rich index predicates[OF index] lambda_I[OF index]])
qed

end
