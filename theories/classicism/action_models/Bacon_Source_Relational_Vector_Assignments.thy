theory Bacon_Source_Relational_Vector_Assignments
  imports Bacon_Source_Relational_Binder_Vectors
begin

section \<open>Sequential updates follow the outer-to-inner binder order\<close>

text \<open>
  Evaluating (λn₁…nₖ.A)a₁…aₖ updates n₁ first, then n₂,
  and so on. Source: the iterated λ convention, pp.5–9.
  Repeated names are permitted: the later, inner binder update wins.
  This is sequential assignment update, not simultaneous substitution.

  The operation remains partial-assignment-valued. Arity mismatches
  receive the unconstrained undefined function; every domain, typing
  and adequacy theorem carries a matching-length or typed-vector guard.
  The elementary assignment facts need no model or R-type assumption;
  the subsequent R semantic use supplies the required binder types.
\<close>

fun paper_R_update_vector :: "'v named_assignment \<Rightarrow> nat list \<Rightarrow> 'v list \<Rightarrow> 'v named_assignment" where
  "paper_R_update_vector g [] [] = g"
| "paper_R_update_vector g [] (a#xs) = undefined"
| "paper_R_update_vector g (n#ns) [] = undefined"
| "paper_R_update_vector g (n#ns) (a#xs) = paper_R_update_vector (g(n := Some a)) ns xs"

lemma paper_R_update_vector_repeated:
  "paper_R_update_vector g [n,n] [a,b] = g(n := Some b)"
  by simp

lemma paper_R_update_vector_domain:
  assumes lengths: "length ns = length xs"
  shows "dom (paper_R_update_vector g ns xs) = dom g \<union> set ns"
  using lengths
proof (induction ns arbitrary: g xs)
  case Nil
  have empty: "xs = []" using Nil.prems by simp
  show ?case by (simp add: empty)
next
  case (Cons n ns)
  obtain a ys where shape: "xs = a#ys" and tail: "length ns = length ys"
    using Cons.prems by (cases xs) auto
  have domain: "dom (paper_R_update_vector (g(n := Some a)) ns ys) =
    dom (g(n := Some a)) \<union> set ns" by (rule Cons.IH[OF tail])
  show ?case by (simp only: shape paper_R_update_vector.simps domain named_assignment_update_domain list.set; blast)
qed

lemma paper_R_update_vector_typed:
  assumes typed: "named_env_typed D G g" and args: "paper_R_vector_args D (map G ns) xs"
  shows "named_env_typed D G (paper_R_update_vector g ns xs)"
  using typed args
proof (induction ns arbitrary: g xs)
  case Nil
  have empty: "xs = []" using Nil.prems(2) by simp
  show ?case by (simp only: empty paper_R_update_vector.simps; rule Nil.prems(1))
next
  case (Cons n ns)
  obtain a ys where shape: "xs = a#ys" and member: "a \<in> D (G n)"
    and tail: "paper_R_vector_args D (map G ns) ys"
    using Cons.prems(2) by (cases xs) auto
  have updated: "named_env_typed D G (g(n := Some a))"
    by (rule named_assignment_update_typed[where D=D and G=G, OF Cons.prems(1) member])
  have result: "named_env_typed D G (paper_R_update_vector (g(n := Some a)) ns ys)"
    by (rule Cons.IH[OF updated tail])
  show ?case by (simp only: shape paper_R_update_vector.simps; rule result)
qed

lemma paper_R_update_vector_adequate_iff:
  assumes lengths: "length ns = length xs"
  shows "named_adequate (paper_R_update_vector g ns xs) A \<longleftrightarrow>
    named_adequate g (named_lam_vec ns A)"
  by (auto simp only: named_adequate_def paper_R_update_vector_domain[OF lengths] named_lam_vec_fv)

lemma paper_R_update_vector_outside:
  assumes lengths: "length ns = length xs" and outside: "n \<notin> set ns"
  shows "paper_R_update_vector g ns xs n = g n"
  using lengths outside
proof (induction ns arbitrary: g xs)
  case Nil
  have empty: "xs = []" using Nil.prems(1) by simp
  show ?case by (simp add: empty)
next
  case (Cons m ms)
  obtain a ys where shape: "xs = a#ys" and tail: "length ms = length ys"
    using Cons.prems(1) by (cases xs) auto
  have nm: "n \<noteq> m" and fresh: "n \<notin> set ms" using Cons.prems(2) by auto
  have unchanged: "paper_R_update_vector (g(m := Some a)) ms ys n = (g(m := Some a)) n"
    by (rule Cons.IH[OF tail fresh])
  show ?case by (simp add: shape unchanged nm)
qed

lemma paper_R_update_vector_append:
  assumes lengths: "length ns = length xs"
  shows "paper_R_update_vector g (ns@ms) (xs@ys) =
    paper_R_update_vector (paper_R_update_vector g ns xs) ms ys"
  using lengths
proof (induction ns arbitrary: g xs)
  case Nil
  have empty: "xs = []" using Nil.prems by simp
  show ?case by (simp add: empty)
next
  case (Cons n ns)
  obtain a zs where shape: "xs = a#zs" and tail: "length ns = length zs"
    using Cons.prems by (cases xs) auto
  show ?case by (simp only: shape append_Cons paper_R_update_vector.simps; rule Cons.IH[OF tail])
qed

end
