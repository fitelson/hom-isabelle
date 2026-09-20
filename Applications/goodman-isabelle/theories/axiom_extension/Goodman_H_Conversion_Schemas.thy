theory Goodman_H_Conversion_Schemas
  imports Goodman_Conversion_Derivability
begin

section \<open>A book-H certificate for the actual conjunction operator\<close>

text \<open>
  The old β/η axioms conclude a conjunction of two implications.
  The target book_and is a λ-defined operator, not a primitive Boolean
  constructor. We obtain its introduction certificate from the already
  verified completeness of BOOK H, following the core's modal-certificate
  method. The conclusion is book_H theoremhood, not merely semantic truth.
  We use the independent full-minimal model class, not full HOL functions.
\<close>

theorem gi_H_and_certificate:
  fixes \<Sigma> :: "'c ssignature" and A B :: "'c book_named_term"
  assumes rich: "sg_rich G"
    and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
  shows "book_H \<Sigma> G (book_imp A (book_imp B (book_and G A B)))"
proof -
  have conjunction: "book_theory_formula \<Sigma> G (book_and G A B)"
    by (rule book_and_language[OF rich al bl])
  have tail: "book_theory_formula \<Sigma> G (book_imp B (book_and G A B))"
    by (rule book_imp_language[OF bl conjunction])
  have result_type: "book_theory_formula \<Sigma> G (book_imp A (book_imp B (book_and G A B)))"
    by (rule book_imp_language[OF al tail])
  show ?thesis unfolding book_H_canonical_completeness[OF rich result_type]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k"
      and "\<forall>P\<in>{}. book_formula_valid D G J V P"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp A (book_imp B (book_and G A B)))"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      show "V (J g (book_imp A (book_imp B (book_and G A B))))"
        by (simp only: M.book_imp_truth[OF typed al tail]
          M.book_imp_truth[OF typed bl conjunction] M.book_and_truth[OF rich typed al bl]; simp)
    qed
  qed
qed

theorem gi_H_and_intro:
  assumes rich: "sg_rich G" and first: "book_H \<Sigma> G A" and second: "book_H \<Sigma> G B"
  shows "book_H \<Sigma> G (book_and G A B)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_H_language[OF rich first])
  have bl: "book_theory_formula \<Sigma> G B" by (rule book_H_language[OF rich second])
  have cl: "book_theory_formula \<Sigma> G (book_and G A B)" by (rule book_and_language[OF rich al bl])
  have il: "book_theory_formula \<Sigma> G (book_imp B (book_and G A B))"
    by (rule book_imp_language[OF bl cl])
  have ad: "book_theory_derivable \<Sigma> G {} A" and bd: "book_theory_derivable \<Sigma> G {} B"
    using first second by (simp_all only: book_H_iff_theory[OF rich])
  have certificate: "book_theory_derivable \<Sigma> G {} (book_imp A (book_imp B (book_and G A B)))"
    using gi_H_and_certificate[OF rich al bl] by (simp only: book_H_iff_theory[OF rich])
  have implication: "book_theory_derivable \<Sigma> G {} (book_imp B (book_and G A B))"
    by (rule book_theory_derivable.MP[OF ad certificate il])
  have result: "book_theory_derivable \<Sigma> G {} (book_and G A B)"
    by (rule book_theory_derivable.MP[OF bd implication cl])
  show ?thesis using result by (simp only: book_H_iff_theory[OF rich])
qed

section \<open>The full translated old β and η axiom conclusions\<close>

theorem gi_H_beta_schema:
  assumes rich: "sg_rich G" and step: "compatible_step beta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : Prop" and typed_B: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Conj (Imp A B) (Imp B A)))"
proof -
  have pair: "book_H \<Sigma> G (gi_to_book G ns k (Imp A B)) \<and>
    book_H \<Sigma> G (gi_to_book G ns k (Imp B A))"
    by (rule gi_H_beta_context_implications[OF rich step typed_A typed_B chart distinct constants_A constants_B])
  have combined: "book_H \<Sigma> G (book_and G (gi_to_book G ns k (Imp A B)) (gi_to_book G ns k (Imp B A)))"
    by (rule gi_H_and_intro[OF rich conjunct1[OF pair] conjunct2[OF pair]])
  show ?thesis using combined by (simp only: gi_to_book.simps)
qed

theorem gi_H_eta_schema:
  assumes rich: "sg_rich G" and step: "compatible_step eta_contract A B"
    and typed_A: "\<Gamma> \<turnstile> A : Prop" and typed_B: "\<Gamma> \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants_A: "gi_constants_admitted k \<Sigma> A"
    and constants_B: "gi_constants_admitted k \<Sigma> B"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Conj (Imp A B) (Imp B A)))"
proof -
  have pair: "book_H \<Sigma> G (gi_to_book G ns k (Imp A B)) \<and>
    book_H \<Sigma> G (gi_to_book G ns k (Imp B A))"
    by (rule gi_H_eta_context_implications[OF rich step typed_A typed_B chart distinct constants_A constants_B])
  have combined: "book_H \<Sigma> G (book_and G (gi_to_book G ns k (Imp A B)) (gi_to_book G ns k (Imp B A)))"
    by (rule gi_H_and_intro[OF rich conjunct1[OF pair] conjunct2[OF pair]])
  show ?thesis using combined by (simp only: gi_to_book.simps)
qed

text \<open>
  The exact old Conj(Imp A B)(Imp B A) is translated here; it is not
  replaced definitionally by book_iff. Thus the Beta and Eta constructors'
  entire conclusions are now covered under the displayed language/chart
  guards. The remaining H constructors and whole-proof induction are
  separate obligations, as are the additional CEV+ rules and axioms.
\<close>

end
