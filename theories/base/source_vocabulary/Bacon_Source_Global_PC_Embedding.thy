theory Bacon_Source_Global_PC_Embedding
  imports Bacon_Source_Global_H Bacon_Source_Variable_Embedding Bacon_Source_Reverse_PC
begin

section \<open>Renaming a literal propositional instance\<close>

text \<open>
  A propositional template remains the same template when its substituted
  formulas are renamed (Bacon–Dorr Figure 2, PC). Figure 1's → and ↔
  are closed λ-definitions and are unchanged by free-variable renaming.

  Isabelle representation: srename commutes with paper_prop_instance.
  The implication and biconditional heads remain literal source terms;
  no target primitive connective is substituted for them.

  Status: a syntax equation. Injectivity and stock richness are not needed.
\<close>

lemma srename_paper_iff:
  "srename r (paper_iff A B) = paper_iff (srename r A) (srename r B)"
  by (simp add: paper_iff_def paper_iff_const_def paper_and_def paper_or_def paper_not_def)

lemma paper_prop_instance_rename:
  "srename r (paper_prop_instance v P) =
    paper_prop_instance (\<lambda>a. srename r (v a)) P"
  by (induction P)
    (simp_all add: paper_not_def paper_and_def paper_or_def srename_paper_imp srename_paper_iff)

section \<open>Embedding the finite-frame PC instance into the global stock\<close>

text \<open>
  A PC instance remains a PC instance when each declared finite-frame
  variable is sent to a global variable of its type.
  Source: the typed stock of §1.1 and PC in Figure 2.

  Isabelle representation: the proved variable-embedding lemma supplies
  global language membership. The same natural-number template witnesses
  paper_global_PC, with the renamed substitution for its atoms.

  Status: the PC case of reverse proof translation only. No whole-proof
  reflection, model, or stronger source calculus is assumed.
\<close>

theorem paper_PC_global_embedding:
  assumes pc: "paper_PC \<Sigma> \<Gamma> A"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_PC \<Sigma> G (srename r A)"
proof -
  have language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    by (rule paper_PC_language[OF pc])
  have global_language: "sgterm_in_language paper_logical_type \<Sigma> G (srename r A) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF language map])
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and eq: "A = paper_prop_instance v P"
    using conjunct2[OF pc[unfolded paper_PC_def]] by (elim exE conjE)
  have renamed: "srename r A = paper_prop_instance (\<lambda>a. srename r (v a)) P"
    by (simp only: eq paper_prop_instance_rename)
  show ?thesis unfolding paper_global_PC_def
  proof (rule conjI[OF global_language])
    show "\<exists>Q :: nat sprop_template. \<exists>w. sprop_tautology Q \<and> srename r A = paper_prop_instance w Q"
      by (rule exI[where x=P], rule exI[where x="\<lambda>a. srename r (v a)"],
        rule conjI[OF taut renamed])
  qed
qed

corollary pterm_to_paper_global_PC:
  assumes taut: "pprop_tautology \<Gamma> A" and names: "pterm_in_signature \<Sigma> A"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_PC \<Sigma> G (srename r (pterm_to_paper A))"
  by (rule paper_PC_global_embedding[where G=G and r=r,
    OF pterm_to_paper_PC[OF taut names] map])

corollary pterm_to_paper_global_H_PC:
  assumes taut: "pprop_tautology \<Gamma> A" and names: "pterm_in_signature \<Sigma> A"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper A))"
  by (rule paper_global_H.PC[OF pterm_to_paper_global_PC[where G=G and r=r,
    OF taut names map]])

end
