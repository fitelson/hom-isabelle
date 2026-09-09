theory Bacon_Book_Primitive_Disjunction_Axiom_Theory
  imports Bacon_Book_Primitive_Disjunction_Encoding Bacon_Book_Primitive_Conjunction_Theory_Derivation
begin

section \<open>The fixed disjunction schemas in the conjunction language\<close>

text \<open>
  Let k∨ be the distinguished constant declared only at t→t→t.
  Π∨ consists exactly of the three typed schemas on p.104:
  (A→C)→((B→C)→(k∨AB→C)), A→k∨AB, and B→k∨AB.
  Every previous logical symbol remains a logical symbol in the target.

  These formulas are fixed THEORY PREMISES, not conjunction-H theorems.
  The tagged operator is not a λ-definition. No rule replacing its tag
  is licensed by empty-premise constant substitution. The native richer
  proof calculus is independently defined in a different leaf.
\<close>

definition book_disj_target_apply ::
  "('c + unit) book_conj_term \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> ('c + unit) book_conj_term" where
  "book_disj_target_apply A B = NApp (NApp (NConst (Inr ()) book_disj_type) A) B"

lemma book_disj_target_apply_language:
  assumes first: "book_conj_formula (book_disj_target_signature \<Sigma>) G A"
    and second: "book_conj_formula (book_disj_target_signature \<Sigma>) G B"
  shows "book_conj_formula (book_disj_target_signature \<Sigma>) G (book_disj_target_apply A B)"
proof -
  have symbol: "book_in_language book_conj_logical_type UNIV (book_disj_target_signature \<Sigma>) G
    (NConst (Inr ()) book_disj_type) book_disj_type"
    by (simp add: book_language_const_iff book_disj_target_tag_iff)
  show ?thesis unfolding book_disj_target_apply_def
    by (rule book_language_App[OF book_language_App[OF symbol first] second])
qed

inductive_set book_disj_axioms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c + unit) book_conj_term set"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Elim: "book_conj_formula (book_disj_target_signature \<Sigma>) G A \<Longrightarrow>
    book_conj_formula (book_disj_target_signature \<Sigma>) G B \<Longrightarrow>
    book_conj_formula (book_disj_target_signature \<Sigma>) G C \<Longrightarrow>
    book_conj_imp (book_conj_imp A C)
      (book_conj_imp (book_conj_imp B C) (book_conj_imp (book_disj_target_apply A B) C))
      \<in> book_disj_axioms \<Sigma> G"
| Intro1: "book_conj_formula (book_disj_target_signature \<Sigma>) G A \<Longrightarrow>
    book_conj_formula (book_disj_target_signature \<Sigma>) G B \<Longrightarrow>
    book_conj_imp A (book_disj_target_apply A B) \<in> book_disj_axioms \<Sigma> G"
| Intro2: "book_conj_formula (book_disj_target_signature \<Sigma>) G A \<Longrightarrow>
    book_conj_formula (book_disj_target_signature \<Sigma>) G B \<Longrightarrow>
    book_conj_imp B (book_disj_target_apply A B) \<in> book_disj_axioms \<Sigma> G"

theorem book_disj_axioms_language:
  assumes member: "A \<in> book_disj_axioms \<Sigma> G"
  shows "book_conj_formula (book_disj_target_signature \<Sigma>) G A"
  using member
proof (induction rule: book_disj_axioms.induct)
  case Elim
  have target: "book_conj_formula (book_disj_target_signature \<Sigma>) G (book_disj_target_apply A B)"
    if "book_conj_formula (book_disj_target_signature \<Sigma>) G A"
      "book_conj_formula (book_disj_target_signature \<Sigma>) G B" for A B
    by (rule book_disj_target_apply_language[OF that])
  show ?case by (intro book_conj_imp_language) (rule Elim.hyps | rule target)+
next
  case Intro1
  show ?case by (rule book_conj_imp_language[OF Intro1.hyps(1) book_disj_target_apply_language[OF Intro1.hyps]])
next
  case Intro2
  show ?case by (rule book_conj_imp_language[OF Intro2.hyps(2) book_disj_target_apply_language[OF Intro2.hyps]])
qed

lemma book_disj_background_assumption:
  assumes member: "A \<in> book_disj_axioms \<Sigma> G" and inclusion: "book_disj_axioms \<Sigma> G \<subseteq> T"
  shows "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G T A"
  by (rule book_conj_theory_derivable.Assumption[
    OF subsetD[OF inclusion member] book_disj_axioms_language[OF member]])

definition book_disj_encoded_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_disj_term set \<Rightarrow> ('c + unit) book_conj_term set" where
  "book_disj_encoded_premises \<Sigma> G S = image book_disj_encode S \<union> book_disj_axioms \<Sigma> G"

theorem book_disj_encoded_premises_language:
  assumes source: "\<And>A. A \<in> S \<Longrightarrow> book_disj_formula \<Sigma> G A"
    and member: "B \<in> book_disj_encoded_premises \<Sigma> G S"
  shows "book_conj_formula (book_disj_target_signature \<Sigma>) G B"
  using member source unfolding book_disj_encoded_premises_def
  by (blast intro: book_disj_encode_language book_disj_axioms_language)

end
