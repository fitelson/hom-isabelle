theory Bacon_Book_Lambda_I_Propositional_Certificates
  imports Bacon_Book_Lambda_I_Conversion
begin

section \<open>MP-only certificates with local assumptions\<close>

text \<open>
  S ⊢ₚ A records a propositional certificate: a typed assumption from S,
  an already proved theorem ∅ ⊢ A, or MP. Every certificate yields
  S ⊢ A in Bacon's theory calculus (Definition 5.1, pp.97–98); the λI
  rules used here are those of Definition 9.8, p.197, restricted to λI
  formulas, i.e. the same schemas as Definition 5.1 (see
  Bacon_Book_Lambda_I_Calculus).
  The certificate relation is auxiliary proof tooling, not another rule
  of that calculus. Its theorem leaves may cite the existing theory
  calculus, but they must have EMPTY premises.

  Representation: book_lambda_I_certificate has exactly Assumption, Theorem,
  and MP constructors, with explicit formula-language guards.
  Status: no Gen occurs in a certificate. Consequently its local
  deduction theorem permits an open discharged formula C. This does NOT
  give unrestricted open discharge for book_lambda_I_derivable, whose
  actual Gen rule remains unchanged.
\<close>

inductive book_lambda_I_certificate ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<Longrightarrow>
    book_lambda_I_certificate \<Sigma> G S A"
| Theorem: "book_lambda_I_derivable \<Sigma> G {} A \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<Longrightarrow>
    book_lambda_I_certificate \<Sigma> G S A"
| MP: "book_lambda_I_certificate \<Sigma> G S A \<Longrightarrow>
    book_lambda_I_certificate \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G B \<Longrightarrow> book_lambda_I_certificate \<Sigma> G S B"

lemma book_lambda_I_certificate_language:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G S A"
  shows "book_lambda_I_formula \<Sigma> G A"
  using certificate
proof (induction rule: book_lambda_I_certificate.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case Theorem
  show ?case by (rule Theorem.hyps(2))
next
  case MP
  show ?case by (rule MP.hyps(3))
qed

theorem book_lambda_I_certificate_embeds:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G S A"
  shows "book_lambda_I_derivable \<Sigma> G S A"
  using certificate
proof (induction rule: book_lambda_I_certificate.induct)
  case Assumption
  show ?case by (rule book_lambda_I_derivable.Assumption[OF Assumption.hyps])
next
  case Theorem
  show ?case by (rule book_lambda_I_derivable_mono[OF Theorem.hyps(1) empty_subsetI])
next
  case MP
  show ?case by (rule book_lambda_I_derivable.MP[OF MP.IH MP.hyps(3)])
qed

lemma book_lambda_I_certificate_weaken:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G S A"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_certificate \<Sigma> G S (book_imp C A)"
proof -
  have al: "book_lambda_I_formula \<Sigma> G A"
    by (rule book_lambda_I_certificate_language[OF certificate])
  have cal: "book_lambda_I_formula \<Sigma> G (book_imp C A)"
    by (rule book_lambda_I_imp_language[OF cl al])
  have schema: "book_lambda_I_derivable \<Sigma> G {} (book_imp A (book_imp C A))"
    by (rule book_lambda_I_derivable.PC1[OF al cl])
  have lifted: "book_lambda_I_certificate \<Sigma> G S (book_imp A (book_imp C A))"
    by (rule book_lambda_I_certificate.Theorem[OF schema book_lambda_I_imp_language[OF al cal]])
  show ?thesis by (rule book_lambda_I_certificate.MP[OF certificate lifted cal])
qed

section \<open>Discharge inside an MP-only certificate\<close>

text \<open>
  S∪{C} ⊢ₚ A implies S ⊢ₚ C→A, for every typed C, including open C.
  The induction uses C→C for the discharged assumption, PC1 for other
  leaves, and PC2 for MP. There is no generalization case to discharge.
  Neither richness of G nor a semantic interpretation is needed.
\<close>

lemma book_lambda_I_certificate_deduction_aux:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G T A"
    and insertion: "T = insert C S"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_certificate \<Sigma> G S (book_imp C A)"
  using certificate insertion
proof (induction arbitrary: S rule: book_lambda_I_certificate.induct)
  case (Assumption A T)
  show ?case
  proof (cases "A = C")
    case True
    have reflexive: "book_lambda_I_derivable \<Sigma> G {} (book_imp C C)"
      by (rule book_lambda_I_imp_refl[OF cl])
    have result: "book_lambda_I_certificate \<Sigma> G S (book_imp C C)"
      by (rule book_lambda_I_certificate.Theorem[OF reflexive book_lambda_I_imp_language[OF cl cl]])
    show ?thesis using result by (simp only: True)
  next
    case False
    have member: "A \<in> S" using Assumption.hyps(1) Assumption.prems False by auto
    have local_fact: "book_lambda_I_certificate \<Sigma> G S A"
      by (rule book_lambda_I_certificate.Assumption[OF member Assumption.hyps(2)])
    show ?thesis by (rule book_lambda_I_certificate_weaken[OF local_fact cl])
  qed
next
  case (Theorem A T)
  have local_fact: "book_lambda_I_certificate \<Sigma> G S A"
    by (rule book_lambda_I_certificate.Theorem[OF Theorem.hyps])
  show ?case by (rule book_lambda_I_certificate_weaken[OF local_fact cl])
next
  case (MP T A B)
  have ca: "book_lambda_I_certificate \<Sigma> G S (book_imp C A)"
    by (rule MP.IH(1)[OF MP.prems])
  have cab: "book_lambda_I_certificate \<Sigma> G S (book_imp C (book_imp A B))"
    by (rule MP.IH(2)[OF MP.prems])
  have al: "book_lambda_I_formula \<Sigma> G A"
    by (rule book_lambda_I_certificate_language[OF MP.hyps(1)])
  have bl: "book_lambda_I_formula \<Sigma> G B" by (rule MP.hyps(3))
  have cal: "book_lambda_I_formula \<Sigma> G (book_imp C A)"
    by (rule book_lambda_I_imp_language[OF cl al])
  have cbl: "book_lambda_I_formula \<Sigma> G (book_imp C B)"
    by (rule book_lambda_I_imp_language[OF cl bl])
  have cabl: "book_lambda_I_formula \<Sigma> G (book_imp C (book_imp A B))"
    by (rule book_lambda_I_imp_language[OF cl book_lambda_I_imp_language[OF al bl]])
  have tail: "book_lambda_I_formula \<Sigma> G (book_imp (book_imp C A) (book_imp C B))"
    by (rule book_lambda_I_imp_language[OF cal cbl])
  have pc2: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp C (book_imp A B)) (book_imp (book_imp C A) (book_imp C B)))"
    by (rule book_lambda_I_derivable.PC2[OF cl al bl])
  have schema: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_imp C (book_imp A B)) (book_imp (book_imp C A) (book_imp C B)))"
    by (rule book_lambda_I_certificate.Theorem[OF pc2 book_lambda_I_imp_language[OF cabl tail]])
  have implication: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_imp C A) (book_imp C B))"
    by (rule book_lambda_I_certificate.MP[OF cab schema tail])
  show ?case by (rule book_lambda_I_certificate.MP[OF ca implication cbl])
qed

theorem book_lambda_I_certificate_deduction:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G (insert C S) A"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_certificate \<Sigma> G S (book_imp C A)"
  by (rule book_lambda_I_certificate_deduction_aux[OF certificate refl cl])

corollary book_lambda_I_certificate_deduction_embeds:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G (insert C S) A"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp C A)"
  by (rule book_lambda_I_certificate_embeds[OF book_lambda_I_certificate_deduction[OF certificate cl]])

end
