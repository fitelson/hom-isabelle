theory Bacon_Source_Relational_Universal_Closure_Syntax
  imports Bacon_Source_Relational_Universal_Proof_Basics
begin

section \<open>Finite literal universal prefixes\<close>

fun paper_R_all_vec :: "sgcontext \<Rightarrow> nat list \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "paper_R_all_vec G [] P = P"
| "paper_R_all_vec G (n#ns) P = named_paper_all (G n) (NLam n (paper_R_all_vec G ns P))"

lemma paper_R_all_vec_language:
  assumes language: "paper_R_in_language \<Sigma> G P Prop" and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: paper_R_all_vec.simps; rule language)
next
  case (Cons n ns)
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  show ?case by (simp only: paper_R_all_vec.simps;
    rule paper_R_named_all_binder_language[OF Cons.IH[OF tail] refl nr])
qed

lemma paper_R_all_vec_fv:
  "named_fv (paper_R_all_vec G ns P) = named_fv P - set ns"
  by (induction ns) (auto simp: named_paper_primitive_fv)

lemma paper_R_all_vec_closed:
  assumes covers: "named_fv P \<subseteq> set ns"
  shows "named_fv (paper_R_all_vec G ns P) = {}"
  using covers by (simp only: paper_R_all_vec_fv; blast)

text \<open>
  H proves (∀n⃗.P)→P by successive literal UI/β instances and
  implication transitivity. The prefix may be empty or repeat names.
  Source: Figure 2, p.8; the closed-sentence reduction supporting
  Theorem 3.2 and the H-theories in n.73.
  This is a theorem implication, not local generalization under
  arbitrary open assumptions.
\<close>

theorem paper_R_named_H_all_vec_instance:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G P Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G (paper_R_all_vec G ns P) P)"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: paper_R_all_vec.simps; rule paper_R_named_H_imp_refl[OF rich language])
next
  case (Cons n ns)
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  have inner: "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    by (rule paper_R_all_vec_language[OF language tail])
  have outer: "paper_R_in_language \<Sigma> G (paper_R_all_vec G (n#ns) P) Prop"
    by (rule paper_R_all_vec_language[OF language Cons.prems])
  have first: "paper_R_named_H \<Sigma> G
    (named_paper_imp G (paper_R_all_vec G (n#ns) P) (paper_R_all_vec G ns P))"
    by (simp only: paper_R_all_vec.simps; rule paper_R_named_H_all_binder_instance[OF rich inner refl nr])
  show ?case by (rule paper_R_named_H_imp_trans[OF rich outer inner language first Cons.IH[OF tail]])
qed

end
