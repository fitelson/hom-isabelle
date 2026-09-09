theory Bacon_Source_Relational_H_Theory_Boxed_Lists
  imports Bacon_Source_Relational_Implication_Lists Bacon_Source_Relational_H_Theory_Normal_K
begin

section \<open>Iterated K transports a finite list of boxed premises\<close>

text \<open>
  From □(A₁→⋯→Aₙ→P) and □A₁,…,□Aₙ, local H
  derives □P using instances of K already in T. The containing
  premise set S need only contain T; no closure condition is imposed
  on S and no Necessitation is performed in S.
  Source: the finite modal step in p.52 n.73.
\<close>

theorem paper_R_H_theory_boxed_list_MP:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and subset: "T \<subseteq> S"
    and formulas: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As"
    and conclusion: "paper_R_in_language \<Sigma> G P Prop"
    and implication: "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G (paper_R_imp_list G As P))"
    and premises_boxed: "\<And>A. A \<in> set As \<Longrightarrow> paper_R_named_derivable \<Sigma> G S (paper_R_named_box G A)"
  shows "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G P)"
  using formulas implication premises_boxed
proof (induction As)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons A As)
  let ?R = "paper_R_imp_list G As P"
  have al: "paper_R_in_language \<Sigma> G A Prop"
    and tail: "list_all (\<lambda>A. paper_R_in_language \<Sigma> G A Prop) As" using Cons.prems(1) by simp_all
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_imp_list_language[OF rich tail conclusion])
  have ba: "paper_R_in_language \<Sigma> G (paper_R_named_box G A) Prop" by (rule paper_R_named_box_language[OF rich al])
  have br: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?R) Prop" by (rule paper_R_named_box_language[OF rich rl])
  let ?K = "named_paper_imp G (paper_R_named_box G (named_paper_imp G A ?R))
    (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G ?R))"
  have k_member: "?K \<in> T" by (rule paper_R_H_theory_normal_K[OF rich theory_h pe al rl])
  have k_language: "paper_R_in_language \<Sigma> G ?K Prop" by (rule paper_R_H_theory_language[OF theory_h k_member])
  have k_local: "paper_R_named_derivable \<Sigma> G S ?K"
    by (rule paper_R_named_derivable.Assumption[OF subsetD[OF subset k_member] k_language])
  have old: "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G (named_paper_imp G A ?R))"
    using Cons.prems(2) by simp
  have conditional: "paper_R_named_derivable \<Sigma> G S
      (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G ?R))"
    by (rule paper_R_named_derivable.MP[OF old k_local paper_R_named_paper_imp_language[OF rich ba br]])
  have head_box: "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G A)"
    by (rule Cons.prems(3); simp)
  have rest_box: "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G ?R)"
    by (rule paper_R_named_derivable.MP[OF head_box conditional br])
  show ?case by (rule Cons.IH[OF tail rest_box]; rule Cons.prems(3); simp)
qed

end
