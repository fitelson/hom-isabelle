theory Bacon_Source_Relational_Identity_Fresh_Application
  imports Bacon_Source_Relational_Identity_Interpretation
begin

section \<open>Every class value can be tested by a fresh predicate variable\<close>

text \<open>
  For X∈Dσ, update the partial class assignment at n:σ. Since
  n∉FV(F), raw locality fixes JgF. The variable equation gives X,
  and the application equation gives J(g[n↦X])(Fn)=app(JgF,X).
  Source role: Definition 3.1(iii.d–e), p.44, for the canonical
  interpretation of Theorem 3.2, p.45 n.64.

  No consistency, Henkin theory, semantic BBK model or closed
  denotability premise is used. The arbitrary X is an actual input
  class; the assignment remains partial and covers the new Fn term.
\<close>

theorem paper_R_identity_denote_fresh_application:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    and member: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_identity_denote \<Sigma> G S (g(n := Some X)) (NApp F (NVar n)) =
    paper_R_identity_application \<Sigma> G S \<sigma> Prop (paper_R_identity_denote \<Sigma> G S g F) X"
proof -
  let ?k = "g(n := Some X)"
  have at_name: "X \<in> paper_R_identity_domain \<Sigma> G S (G n)" by (simp only: nt; rule member)
  have kt: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G ?k"
    by (rule named_assignment_update_typed[where D="paper_R_identity_domain \<Sigma> G S" and G=G and n=n,
      OF typed at_name])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF nt rt])
  have whole: "named_adequate ?k (NApp F (NVar n))"
    using adequate by (auto simp: named_adequate_def named_assignment_update_domain)
  have unchanged: "paper_R_identity_denote \<Sigma> G S ?k F = paper_R_identity_denote \<Sigma> G S g F"
  proof (rule paper_R_identity_denote_locality)
    fix m
    assume free: "m \<in> named_fv F"
    have different: "m \<noteq> n" using free fresh by blast
    show "?k m = g m" by (simp add: different)
  qed
  have assigned: "?k n = Some X" by simp
  have variable_value: "paper_R_identity_denote \<Sigma> G S ?k (NVar n) = X"
    by (rule paper_R_identity_denote_var[where g="?k" and n=n, OF rich kt assigned])
  show ?thesis by (simp only: paper_R_identity_denote_App[OF rich predicate variable kt whole] unchanged variable_value)
qed

end
