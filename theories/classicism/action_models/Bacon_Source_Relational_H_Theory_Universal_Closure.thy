theory Bacon_Source_Relational_H_Theory_Universal_Closure
  imports Bacon_Source_Relational_H_Theory Bacon_Source_Relational_Universal_Closure_Syntax
    Bacon_Source_Relational_Assignment_Extension
begin

section \<open>Global H-theory closure under universal generalization\<close>

theorem paper_R_H_theory_generalize:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and member: "P \<in> T" and variable: "G n = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "named_paper_all \<sigma> (NLam n P) \<in> T"
proof -
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule paper_R_H_theory_language[OF theory_h member])
  have top: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have all_language: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam n P)) Prop"
    by (rule paper_R_named_all_binder_language[OF pl variable rt])
  have schema: "named_paper_imp G P (named_paper_imp G (paper_R_named_top G) P) \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h paper_R_named_H_imp_weaken[OF rich top pl]])
  have conditional: "named_paper_imp G (paper_R_named_top G) P \<in> T"
    by (rule paper_R_H_theory_MP[OF theory_h member schema paper_R_named_paper_imp_language[OF rich top pl]])
  have fresh: "n \<notin> named_fv (paper_R_named_top G)" by (simp only: paper_R_named_top_closed; simp)
  have generalized: "named_paper_imp G (paper_R_named_top G) (named_paper_all \<sigma> (NLam n P)) \<in> T"
    by (rule paper_R_H_theory_Gen[OF theory_h conditional variable fresh
      paper_R_named_paper_imp_language[OF rich top all_language]])
  have truth_member: "paper_R_named_top G \<in> T" by (rule paper_R_H_theory_H[OF theory_h paper_R_named_H_top[OF rich]])
  show ?thesis by (rule paper_R_H_theory_MP[OF theory_h truth_member generalized all_language])
qed

theorem paper_R_H_theory_universal_closure:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and member: "P \<in> T" and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_all_vec G ns P \<in> T"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: paper_R_all_vec.simps; rule member)
next
  case (Cons n ns)
  have nr: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)" using Cons.prems by simp_all
  show ?case by (simp only: paper_R_all_vec.simps;
    rule paper_R_H_theory_generalize[OF rich theory_h Cons.IH[OF tail] refl nr])
qed

text \<open>
  Each P∈T has an actual closed universal closure in T: enumerate
  its finite free-variable set distinctly. Their types are in R by the
  independent typing derivation of P. This uses global H-theory Gen
  with the closed antecedent ⊤, never unrestricted local Gen.
  Source: Theorem 3.2's sentence formulation and n.73's H-theories.
\<close>

theorem paper_R_H_theory_closed_universal_instance:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T" and member: "P \<in> T"
  obtains ns where "distinct ns" "set ns = named_fv P" "list_all paper_R_type (map G ns)"
    "paper_R_all_vec G ns P \<in> T" "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    "named_fv (paper_R_all_vec G ns P) = {}"
proof -
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule paper_R_H_theory_language[OF theory_h member])
  obtain ns where cover: "set ns = named_fv P" and distinct: "distinct ns"
    using finite_distinct_list[OF named_fv_finite[of P]] by blast
  have types: "paper_R_type (G n)" if "n \<in> set ns" for n
    by (rule paper_R_language_fv_type[OF pl]; use that in \<open>simp only: cover\<close>)
  have binders: "list_all paper_R_type (map G ns)" using types by (simp add: list_all_iff)
  have included: "paper_R_all_vec G ns P \<in> T" by (rule paper_R_H_theory_universal_closure[OF rich theory_h member binders])
  have language: "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop" by (rule paper_R_all_vec_language[OF pl binders])
  have closed: "named_fv (paper_R_all_vec G ns P) = {}" by (simp only: paper_R_all_vec_fv cover; simp)
  show thesis by (rule that[OF distinct cover binders included language closed])
qed

end
