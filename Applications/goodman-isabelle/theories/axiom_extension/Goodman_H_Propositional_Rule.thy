theory Goodman_H_Propositional_Rule
  imports Goodman_H_Certificate_Interface
begin

section \<open>Truth-functional evaluation of the translated constructors\<close>

context book_full_minimal_model
begin

lemma gi_prop_eval_interpretation:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and chart: "map stock ns = \<Gamma>"
    and formula: "\<Gamma> \<turnstile> A : Prop" and constants: "gi_constants_admitted k signature A"
  shows "prop_eval (\<lambda>B. V (denote g (gi_to_book stock ns k B))) A =
    V (denote g (gi_to_book stock ns k A))"
  using formula constants
proof (induction A)
  case Var
  show ?case by (simp only: prop_eval.simps)
next
  case Const
  show ?case by (simp only: prop_eval.simps)
next
  case App
  show ?case by (simp only: prop_eval.simps)
next
  case Lam
  show ?case by (simp only: prop_eval.simps)
next
  case Eq
  show ?case by (simp only: prop_eval.simps)
next
  case (Neg A)
  have at: "\<Gamma> \<turnstile> A : Prop" using Neg.prems(1) by (auto elim: has_type.cases)
  have ac: "gi_constants_admitted k signature A" using Neg.prems(2) by simp
  have al: "book_theory_formula signature stock (gi_to_book stock ns k A)"
    by (rule gi_to_book_language[OF rich at chart ac])
  show ?case by (simp only: prop_eval.simps gi_to_book.simps
    book_not_truth[OF rich typed al] Neg.IH[OF at ac])
next
  case (Conj A B)
  have at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    using Conj.prems(1) by (auto elim: has_type.cases)
  have ac: "gi_constants_admitted k signature A" and bc: "gi_constants_admitted k signature B"
    using Conj.prems(2) by simp_all
  have al: "book_theory_formula signature stock (gi_to_book stock ns k A)"
    by (rule gi_to_book_language[OF rich at chart ac])
  have bl: "book_theory_formula signature stock (gi_to_book stock ns k B)"
    by (rule gi_to_book_language[OF rich bt chart bc])
  show ?case by (simp only: prop_eval.simps gi_to_book.simps
    book_and_truth[OF rich typed al bl] Conj.IH(1)[OF at ac] Conj.IH(2)[OF bt bc])
next
  case (Disj A B)
  have at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    using Disj.prems(1) by (auto elim: has_type.cases)
  have ac: "gi_constants_admitted k signature A" and bc: "gi_constants_admitted k signature B"
    using Disj.prems(2) by simp_all
  have al: "book_theory_formula signature stock (gi_to_book stock ns k A)"
    by (rule gi_to_book_language[OF rich at chart ac])
  have bl: "book_theory_formula signature stock (gi_to_book stock ns k B)"
    by (rule gi_to_book_language[OF rich bt chart bc])
  show ?case by (simp only: prop_eval.simps gi_to_book.simps
    book_or_truth[OF rich typed al bl] Disj.IH(1)[OF at ac] Disj.IH(2)[OF bt bc])
next
  case (Imp A B)
  have at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    using Imp.prems(1) by (auto elim: has_type.cases)
  have ac: "gi_constants_admitted k signature A" and bc: "gi_constants_admitted k signature B"
    using Imp.prems(2) by simp_all
  have al: "book_theory_formula signature stock (gi_to_book stock ns k A)"
    by (rule gi_to_book_language[OF rich at chart ac])
  have bl: "book_theory_formula signature stock (gi_to_book stock ns k B)"
    by (rule gi_to_book_language[OF rich bt chart bc])
  show ?case by (simp only: prop_eval.simps gi_to_book.simps
    book_imp_truth[OF typed al bl] Imp.IH(1)[OF at ac] Imp.IH(2)[OF bt bc])
next
  case Forall
  show ?case by (simp only: prop_eval.simps)
next
  case Exists
  show ?case by (simp only: prop_eval.simps)
qed

end

theorem gi_H_PC:
  assumes rich: "sg_rich G" and tautology: "prop_tautology \<Gamma> A"
    and chart: "map G ns = \<Gamma>" and constants: "gi_constants_admitted k \<Sigma> A"
  shows "book_H \<Sigma> G (gi_to_book G ns k A)"
proof -
  have formula: "\<Gamma> \<turnstile> A : Prop" and taut: "\<forall>v. prop_eval v A"
    using tautology unfolding prop_tautology_def by blast+
  have language: "book_theory_formula \<Sigma> G (gi_to_book G ns k A)"
    by (rule gi_to_book_language[OF rich formula chart constants])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich language])
    fix D app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have equality: "prop_eval (\<lambda>B. V (J g (gi_to_book G ns k B))) A =
      V (J g (gi_to_book G ns k A))"
      by (rule M.gi_prop_eval_interpretation[OF rich typed chart formula constants])
    show "V (J g (gi_to_book G ns k A))" using taut equality by blast
  qed
qed

text \<open>
  Only the truth-functional constructors are unfolded by prop_eval.
  Equations, quantified terms and applications remain atoms; no extra
  tautologies are introduced by treating object identity extensionally.
\<close>

end
