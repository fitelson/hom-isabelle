theory Bacon_Source_Relational_Universal_Consequent
  imports Bacon_Source_Relational_Universal_Closure_Syntax
begin

section \<open>A fresh finite universal prefix on an implication's consequent\<close>

theorem paper_R_named_H_imp_all_vec:
  assumes rich: "paper_R_rich G"
    and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and fresh: "set ns \<inter> named_fv A = {}"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_imp G A B)"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G A (paper_R_all_vec G ns B))"
  using binders fresh
proof (induction ns)
  case Nil
  show ?case by (simp only: paper_R_all_vec.simps; rule premise)
next
  case (Cons n ns)
  have tail_types: "list_all paper_R_type (map G ns)" using Cons.prems(1) by simp
  have tail_fresh: "set ns \<inter> named_fv A = {}" and nf: "n \<notin> named_fv A"
    using Cons.prems(2) by auto
  have inner: "paper_R_named_H \<Sigma> G (named_paper_imp G A (paper_R_all_vec G ns B))"
    by (rule Cons.IH[OF tail_types tail_fresh])
  have whole_language: "paper_R_in_language \<Sigma> G
      (named_paper_imp G A (paper_R_all_vec G (n#ns) B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al paper_R_all_vec_language[OF bl Cons.prems(1)]])
  show ?case using paper_R_named_H.Gen[OF inner refl nf
    whole_language[unfolded paper_R_all_vec.simps]]
    by (simp only: paper_R_all_vec.simps)
qed

text \<open>
  Only the native Gen rule is iterated. Each quantified variable is
  free in neither the fixed antecedent nor a new side assumption.
  This is an H theorem calculation, not unrestricted generalization
  of a local consequence. Source: Figure 2 and p.18 n.22.
\<close>

end
