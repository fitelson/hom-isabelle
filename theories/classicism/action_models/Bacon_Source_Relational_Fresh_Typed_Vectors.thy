theory Bacon_Source_Relational_Fresh_Typed_Vectors
  imports Bacon_Source_Relational_Application_Graph
begin

section \<open>Distinct R-typed test variables outside a finite forbidden set\<close>

text \<open>
  For each finite R type list σ⃗, choose distinct variables u⃗
  of those types avoiding a prescribed finite set. At the successor
  step put the newly chosen name into the forbidden set for the tail.
  Source: the fresh relational-tail variables in p.15, footnote 17.
  This is a syntactic stock result, not a model or choice of argument
  values. Distinctness prevents replacing a full application test by
  a diagonal one.
\<close>

theorem paper_R_fresh_typed_vector:
  assumes rich: "paper_R_rich G" and types: "list_all paper_R_type \<sigma>s" and finite: "finite Avoid"
  obtains us where "distinct us" "map G us = \<sigma>s" "set us \<inter> Avoid = {}"
proof -
  have existence: "\<exists>us. distinct us \<and> map G us = \<sigma>s \<and> set us \<inter> Avoid = {}"
    using types finite
  proof (induction \<sigma>s arbitrary: Avoid)
    case Nil
    show ?case by (rule exI[where x="[]"]; simp)
  next
    case (Cons \<sigma> \<sigma>s)
    have rt: "paper_R_type \<sigma>" and tail: "list_all paper_R_type \<sigma>s" using Cons.prems(1) by simp_all
    obtain u where ut: "G u = \<sigma>" and fresh: "u \<notin> Avoid"
      by (rule paper_R_rich_fresh[OF rich rt Cons.prems(2)])
    have finite_next: "finite (insert u Avoid)" using Cons.prems(2) by simp
    obtain us where distinct: "distinct us" and typed: "map G us = \<sigma>s"
      and avoids: "set us \<inter> insert u Avoid = {}"
      using Cons.IH[OF tail finite_next] by blast
    have head_fresh: "u \<notin> set us" using avoids by blast
    have tail_fresh: "set us \<inter> Avoid = {}" using avoids by blast
    show ?case by (rule exI[where x="u#us"]; use distinct typed ut head_fresh fresh tail_fresh in auto)
  qed
  obtain us where distinct: "distinct us" and typed: "map G us = \<sigma>s" and fresh: "set us \<inter> Avoid = {}"
    using existence by blast
  show thesis by (rule that[OF distinct typed fresh])
qed

end
