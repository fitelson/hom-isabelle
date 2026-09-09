theory Bacon_Source_Relational_Implication_Lists
  imports Bacon_Source_Relational_Deduction
begin

section \<open>Finite premise discharge in native local H\<close>

fun paper_R_imp_list :: "sgcontext \<Rightarrow> 'c paper_named_term list \<Rightarrow>
    'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "paper_R_imp_list G [] P = P"
| "paper_R_imp_list G (A#As) P = named_paper_imp G A (paper_R_imp_list G As P)"

lemma paper_R_imp_list_language:
  assumes rich: "paper_R_rich G" and formulas: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As"
    and conclusion: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_in_language \<Sigma> G (paper_R_imp_list G As P) Prop"
  using formulas
proof (induction As)
  case Nil
  show ?case by (simp only: paper_R_imp_list.simps; rule conclusion)
next
  case (Cons A As)
  have al: "paper_R_in_language \<Sigma> G A Prop"
    and tail: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As" using Cons.prems by simp_all
  show ?case by (simp only: paper_R_imp_list.simps;
    rule paper_R_named_paper_imp_language[OF rich al Cons.IH[OF tail]])
qed

theorem paper_R_named_derivable_list_deduction:
  assumes rich: "paper_R_rich G" and formulas: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As"
    and derivation: "paper_R_named_derivable \<Sigma> G (set As \<union> T) P"
  shows "paper_R_named_derivable \<Sigma> G T (paper_R_imp_list G As P)"
  using formulas derivation
proof (induction As arbitrary: T)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons A As)
  have al: "paper_R_in_language \<Sigma> G A Prop"
    and tail: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As" using Cons.prems(1) by simp_all
  have sets: "set (A#As) \<union> T = set As \<union> insert A T" by auto
  have reordered: "paper_R_named_derivable \<Sigma> G (set As \<union> insert A T) P"
    using Cons.prems(2) by (simp only: sets)
  have inner: "paper_R_named_derivable \<Sigma> G (insert A T) (paper_R_imp_list G As P)"
    by (rule Cons.IH[OF tail reordered])
  show ?case by (simp only: paper_R_imp_list.simps; rule paper_R_named_derivable_deduction[OF rich al inner])
qed

text \<open>
  The nested implication A₁→⋯→Aₙ→P is the finite-premise
  form of the conjunction implication in p.52 n.73. Each discharge is
  the proved LOCAL H deduction theorem. No Gen, Inst or Necessitation
  is applied to an assumed formula. The background T may be infinite.
\<close>

end
