theory Bacon_Book_Primitive_Conjunction_Axiom_Theory
  imports Bacon_Book_Primitive_Conjunction_Decoding Bacon_Book_Printed_Theory_Derivation
begin

section \<open>A fixed background theory for the encoded primitive\<close>

text \<open>
  Let k∧ be the distinguished constant of type t→t→t. The background
  Π∧ contains every typed instance of P→(Q→k∧PQ), k∧PQ→P, and
  k∧PQ→Q. Source: the three conjunction schemas in Bacon §5.2, p.104.

  These are FIXED theory premises in the minimal language, not minimal-H
  theorems and not a λ-definition of conjunction. The inductive set below
  specifies precisely those instances; it is not a new proof rule of the
  minimal calculus. In particular, substitution of the tag throughout Π∧
  is not licensed by an empty-premise substitution theorem.
\<close>

definition book_conj_target_apply ::
  "('c + unit) book_named_term \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> ('c + unit) book_named_term" where
  "book_conj_target_apply A B = NApp (NApp (NConst (Inr ()) book_conj_type) A) B"

lemma book_conj_target_apply_language:
  assumes first: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G A"
    and second: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G B"
  shows "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (book_conj_target_apply A B)"
proof -
  have symbol: "book_in_language book_minimal_logical_type UNIV (book_conj_target_signature \<Sigma>) G
    (NConst (Inr ()) book_conj_type) book_conj_type"
    by (simp add: book_language_const_iff book_conj_target_tag_iff)
  show ?thesis unfolding book_conj_target_apply_def
    by (rule book_language_App[OF book_language_App[OF symbol first] second])
qed

inductive_set book_conj_axioms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c + unit) book_named_term set"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Intro: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G P \<Longrightarrow>
    book_printed_theory_formula (book_conj_target_signature \<Sigma>) G Q \<Longrightarrow>
    book_imp P (book_imp Q (book_conj_target_apply P Q)) \<in> book_conj_axioms \<Sigma> G"
| Left: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G P \<Longrightarrow>
    book_printed_theory_formula (book_conj_target_signature \<Sigma>) G Q \<Longrightarrow>
    book_imp (book_conj_target_apply P Q) P \<in> book_conj_axioms \<Sigma> G"
| Right: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G P \<Longrightarrow>
    book_printed_theory_formula (book_conj_target_signature \<Sigma>) G Q \<Longrightarrow>
    book_imp (book_conj_target_apply P Q) Q \<in> book_conj_axioms \<Sigma> G"

theorem book_conj_axioms_language:
  assumes member: "A \<in> book_conj_axioms \<Sigma> G"
  shows "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G A"
  using member
proof (induction rule: book_conj_axioms.induct)
  case Intro
  show ?case by (rule book_imp_language[OF Intro.hyps(1)
    book_imp_language[OF Intro.hyps(2) book_conj_target_apply_language[OF Intro.hyps]]])
next
  case Left
  show ?case by (rule book_imp_language[OF book_conj_target_apply_language[OF Left.hyps] Left.hyps(1)])
next
  case Right
  show ?case by (rule book_imp_language[OF book_conj_target_apply_language[OF Right.hyps] Right.hyps(2)])
qed

lemma book_conj_background_assumption:
  assumes member: "A \<in> book_conj_axioms \<Sigma> G" and inclusion: "book_conj_axioms \<Sigma> G \<subseteq> T"
  shows "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G T A"
  by (rule book_printed_theory_derivable.Assumption[
    OF subsetD[OF inclusion member] book_conj_axioms_language[OF member]])

definition book_conj_encoded_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> ('c + unit) book_named_term set" where
  "book_conj_encoded_premises \<Sigma> G S = image book_conj_encode S \<union> book_conj_axioms \<Sigma> G"

theorem book_conj_encoded_premises_language:
  assumes source: "\<And>A. A \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G A"
    and member: "B \<in> book_conj_encoded_premises \<Sigma> G S"
  shows "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G B"
  using member source unfolding book_conj_encoded_premises_def
  by (blast intro: book_conj_encode_language book_conj_axioms_language)

end
