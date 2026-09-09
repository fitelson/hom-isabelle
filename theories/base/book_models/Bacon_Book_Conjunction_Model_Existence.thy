theory Bacon_Book_Conjunction_Model_Existence
  imports Bacon_Book_Conjunction_Proof_Correspondence Bacon_Book_Conjunction_Model_From_Background
begin

section \<open>An explicit carrier for native primitive-conjunction models\<close>

text \<open>
  The target name carrier is 'c+unit, so its canonical values are sets
  of closed minimal terms over ('c+unit) Henkin names. We retain that
  semantic carrier when interpreting the original richer language.
  Source role: the primitive extension of §5.2, p.104, and the model
  construction of Theorem 15.3, pp.320–321.

  This carrier annotation is tied explicitly to the ORIGINAL nonlogical
  name type 'c. It does not require old terms to denote every domain
  element, countability of the signature, or a λ-definition of ∧.
\<close>

type_synonym 'c book_conj_canonical_value =
  "(('c + unit) book_henkin_name) book_named_term set"

section \<open>Native consistency yields a native model\<close>

text \<open>
  From consistency of S in the independent twelve-constructor calculus,
  the proof correspondence gives consistency of enc(S)∪Π∧ in the
  printed minimal calculus. Its canonical model satisfies Π∧ as fixed
  premises. The checked forward model transport then interprets primitive
  ∧ with the actual value of the tag, and J′g(A)=Jg(enc(A)).

  Every original premise holds at every typed assignment. S may be open
  and infinite. No native or minimal model is an input assumption here:
  the intermediate minimal model is obtained from the consistency theorem.
  Scope remains full F, the minimal basis plus primitive ∧, rich stock,
  and witnessed logical closed values; arbitrary admitted sublanguages
  and other primitive extensions are not asserted.
\<close>

theorem book_conj_canonical_model_existence:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G A"
    and consistent: "book_conj_theory_consistent \<Sigma> G S"
  shows "\<exists>(D::otype \<Rightarrow> 'c book_conj_canonical_value set) app J V k.
    book_conjunction_model D app \<Sigma> G J V k \<and>
    (\<forall>A\<in>S. book_formula_valid D G J V A)"
proof -
  let ?T = "book_conj_encoded_premises \<Sigma> G S"
  let ?target = "book_conj_target_signature \<Sigma>"
  have target_consistent: "book_printed_theory_consistent ?target G ?T"
    by (rule iffD1[OF book_conj_consistency_iff_printed_background consistent])
  have target_language: "book_printed_theory_formula ?target G B" if "B \<in> ?T" for B
    by (rule book_conj_encoded_premises_language[OF language that])
  obtain D :: "otype \<Rightarrow> 'c book_conj_canonical_value set" and app J V k where
    target_model: "book_full_minimal_model D app ?target G J V k"
    and target_truth: "\<forall>B\<in>?T. book_formula_valid D G J V B"
    using book_printed_canonical_model_existence[where \<Sigma>="?target" and G=G and S="?T",
      OF rich target_language target_consistent] by blast
  have background: "\<forall>B\<in>book_conj_axioms \<Sigma> G. book_formula_valid D G J V B"
  proof (rule ballI)
    fix B
    assume member: "B \<in> book_conj_axioms \<Sigma> G"
    have in_target: "B \<in> ?T"
      unfolding book_conj_encoded_premises_def by (rule UnI2[OF member])
    show "book_formula_valid D G J V B" by (rule bspec[OF target_truth in_target])
  qed
  obtain k' where native_model: "book_conjunction_model D app \<Sigma> G (book_conj_encoded_denote J) V k'"
    using book_conj_model_from_background[OF target_model rich background] by (elim exE)
  have original_truth: "\<forall>A\<in>S. book_formula_valid D G (book_conj_encoded_denote J) V A"
  proof (rule ballI)
    fix A
    assume member: "A \<in> S"
    have image_member: "book_conj_encode A \<in> image book_conj_encode S"
      by (rule imageI[OF member])
    have in_target: "book_conj_encode A \<in> ?T"
      unfolding book_conj_encoded_premises_def by (rule UnI1[OF image_member])
    have encoded_truth: "book_formula_valid D G J V (book_conj_encode A)"
      by (rule bspec[OF target_truth in_target])
    show "book_formula_valid D G (book_conj_encoded_denote J) V A"
      using encoded_truth by (simp only: book_formula_valid_def book_conj_encoded_denote_def)
  qed
  show ?thesis by (rule exI[where x=D], rule exI[where x=app],
      rule exI[where x="book_conj_encoded_denote J"], rule exI[where x=V], rule exI[where x="k'"],
      rule conjI[OF native_model original_truth])
qed

end
