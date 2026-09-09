theory Bacon_Source_Global_Proof_Basics
  imports Bacon_Source_Global_Connective_Language
begin

section \<open>Two-formula PC instances in the global source calculus\<close>

text \<open>
  PC includes each tautological template with formulas substituted for its
  propositional letters (Bacon–Dorr Figure 2, p.8).

  Isabelle representation: label 0 receives A; every other label receives B.
  A common finite prefix proves only the required language guard. The
  logical inference is paper_global_H.PC, not target pH theoremhood.

  Status: source proof infrastructure; no semantic or proof-reflection premise.
\<close>

lemma paper_global_PC_two:
  fixes T :: "nat sprop_template"
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and taut: "sprop_tautology T"
  shows "paper_global_H \<Sigma> G (paper_prop_instance (\<lambda>k. if k = 0 then A else B) T)"
proof -
  let ?m = "max (source_free_bound A) (source_free_bound B)"
  let ?v = "\<lambda>k :: nat. if k = 0 then A else B"
  have al: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) A Prop"
    by (rule source_language_in_prefix[OF A]) simp
  have bl: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) B Prop"
    by (rule source_language_in_prefix[OF B]) simp
  have finite_language: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m)
    (paper_prop_instance ?v T) Prop"
  proof (rule paper_prop_instance_language)
    fix a
    assume "a \<in> sprop_atoms T"
    show "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) (?v a) Prop"
      using al bl by (cases "a = 0") simp_all
  qed
  have language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_prop_instance ?v T) Prop"
    by (rule source_prefix_language_to_global[OF finite_language])
  have pc: "paper_global_PC \<Sigma> G (paper_prop_instance ?v T)"
    unfolding paper_global_PC_def
  proof (rule conjI[OF language])
    show "\<exists>P :: nat sprop_template. \<exists>w. sprop_tautology P \<and>
      paper_prop_instance ?v T = paper_prop_instance w P"
      by (rule exI[where x=T], rule exI[where x="?v"], rule conjI[OF taut refl])
  qed
  show ?thesis by (rule paper_global_H.PC[OF pc])
qed

section \<open>Material biconditionals transport source proofs\<close>

text \<open>
  From A ↔ B and A, infer B; from A ↔ B and B, infer A.
  These are PC/MP consequences in the source calculus.

  Isabelle representation: the biconditional and both implications are
  literal Figure 1 source operations. Each MP conclusion is language-guarded.
  Status: theorem-level inference only, not arbitrary intensional replacement.
\<close>

lemma paper_global_iff_forward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and proved: "paper_global_H \<Sigma> G A"
    and equivalent: "paper_global_H \<Sigma> G (paper_iff A B)"
  shows "paper_global_H \<Sigma> G B"
proof -
  let ?T = "SPImp (SPAtom 0) (SPImp (SPIff (SPAtom 0) (SPAtom 1)) (SPAtom 1)) :: nat sprop_template"
  have taut: "sprop_tautology ?T" by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have bridge: "paper_global_H \<Sigma> G (paper_imp A (paper_imp (paper_iff A B) B))"
    using paper_global_PC_two[OF A B taut] by simp
  have language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp (paper_iff A B) B) Prop"
    by (rule paper_global_imp_language[OF paper_global_iff_language[OF A B] B])
  have implication: "paper_global_H \<Sigma> G (paper_imp (paper_iff A B) B)"
    by (rule paper_global_H.MP[OF proved bridge language])
  show ?thesis by (rule paper_global_H.MP[OF equivalent implication B])
qed

lemma paper_global_iff_backward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and proved: "paper_global_H \<Sigma> G B"
    and equivalent: "paper_global_H \<Sigma> G (paper_iff A B)"
  shows "paper_global_H \<Sigma> G A"
proof -
  let ?T = "SPImp (SPAtom 1) (SPImp (SPIff (SPAtom 0) (SPAtom 1)) (SPAtom 0)) :: nat sprop_template"
  have taut: "sprop_tautology ?T" by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have bridge: "paper_global_H \<Sigma> G (paper_imp B (paper_imp (paper_iff A B) A))"
    using paper_global_PC_two[OF A B taut] by simp
  have language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp (paper_iff A B) A) Prop"
    by (rule paper_global_imp_language[OF paper_global_iff_language[OF A B] A])
  have implication: "paper_global_H \<Sigma> G (paper_imp (paper_iff A B) A)"
    by (rule paper_global_H.MP[OF proved bridge language])
  show ?thesis by (rule paper_global_H.MP[OF equivalent implication A])
qed

lemma paper_global_H_iff_expanded:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and equivalent: "paper_global_H \<Sigma> G (paper_iff A B)"
  shows "paper_global_H \<Sigma> G (paper_and (paper_imp A B) (paper_imp B A))"
proof -
  let ?E = "paper_and (paper_imp A B) (paper_imp B A)"
  let ?T = "SPImp (SPIff (SPAtom 0) (SPAtom 1))
    (SPAnd (SPImp (SPAtom 0) (SPAtom 1)) (SPImp (SPAtom 1) (SPAtom 0))) :: nat sprop_template"
  have taut: "sprop_tautology ?T" by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have bridge: "paper_global_H \<Sigma> G (paper_imp (paper_iff A B) ?E)"
    using paper_global_PC_two[OF A B taut] by simp
  have language: "sgterm_in_language paper_logical_type \<Sigma> G ?E Prop"
    by (rule conjunct2[OF iffD1[OF paper_global_imp_language_iff paper_global_H_language[OF bridge]]])
  show ?thesis by (rule paper_global_H.MP[OF equivalent bridge language])
qed

text \<open>
  The last lemma changes theoremhood from the literal source biconditional
  to the conjunction of its two literal source implications. It is a PC/MP
  consequence, not an identity between connective operations.
\<close>

section \<open>Source proof transport along contextual β and η steps\<close>

text \<open>
  Figure 2's β/η axioms yield the literal biconditional between the
  endpoints; the preceding PC/MP argument transports their theoremhood.
  Status: one compatible syntactic step, possibly under binders. This is
  not a semantic argument or a presupposed complete reflection theorem.
\<close>

lemma paper_global_beta_biconditional:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step sbeta_contract A B"
  shows "paper_global_H \<Sigma> G (paper_iff A B)"
  by (rule paper_global_H.Beta[OF A B step paper_global_iff_language[OF A B]])

lemma paper_global_eta_biconditional:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step seta_contract A B"
  shows "paper_global_H \<Sigma> G (paper_iff A B)"
  by (rule paper_global_H.Eta[OF A B step paper_global_iff_language[OF A B]])

lemma paper_global_beta_forward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step sbeta_contract A B" and proved: "paper_global_H \<Sigma> G A"
  shows "paper_global_H \<Sigma> G B"
  by (rule paper_global_iff_forward[OF A B proved paper_global_beta_biconditional[OF A B step]])

lemma paper_global_beta_backward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step sbeta_contract A B" and proved: "paper_global_H \<Sigma> G B"
  shows "paper_global_H \<Sigma> G A"
  by (rule paper_global_iff_backward[OF A B proved paper_global_beta_biconditional[OF A B step]])

lemma paper_global_eta_forward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step seta_contract A B" and proved: "paper_global_H \<Sigma> G A"
  shows "paper_global_H \<Sigma> G B"
  by (rule paper_global_iff_forward[OF A B proved paper_global_eta_biconditional[OF A B step]])

lemma paper_global_eta_backward:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    and step: "scompatible_step seta_contract A B" and proved: "paper_global_H \<Sigma> G B"
  shows "paper_global_H \<Sigma> G A"
  by (rule paper_global_iff_backward[OF A B proved paper_global_eta_biconditional[OF A B step]])

lemmas paper_global_H_beta_forward = paper_global_beta_forward
lemmas paper_global_H_beta_backward = paper_global_beta_backward
lemmas paper_global_H_eta_forward = paper_global_eta_forward
lemmas paper_global_H_eta_backward = paper_global_eta_backward

end
