theory Bacon_Source_Reverse_PC
  imports Bacon_Source_Reverse_Syntax Bacon_Source_Propositional_Reindexing
begin

section \<open>The target propositional skeleton is a source PC template\<close>

text \<open>
  A target PC tautology becomes a paper PC instance after its connectives
  are re-expressed in the source vocabulary (Bacon–Dorr Figures 1–2).
  Target implication becomes the literal source λpq.¬p ∨ q.

  Isabelle representation: pterm_prop_template decomposes PNeg, PConj,
  PDisj, and PImp. Every other constructor is a single schematic atom
  labelled by its whole pterm. Only the finite set of occurring labels is
  reindexed to nat; the arbitrary carrier of nonlogical names is unchanged.

  Status: finite-frame PC preservation in the reverse syntax direction,
  not yet induction over target H proofs or general proof reflection.
\<close>

fun pterm_prop_template :: "'c pterm \<Rightarrow> 'c pterm sprop_template" where
  "pterm_prop_template (PVar n) = SPAtom (PVar n)"
| "pterm_prop_template (PConst c \<sigma>) = SPAtom (PConst c \<sigma>)"
| "pterm_prop_template (PApp F A) = SPAtom (PApp F A)"
| "pterm_prop_template (PLam \<sigma> A) = SPAtom (PLam \<sigma> A)"
| "pterm_prop_template (PEq \<sigma> A B) = SPAtom (PEq \<sigma> A B)"
| "pterm_prop_template (PNeg A) = SPNot (pterm_prop_template A)"
| "pterm_prop_template (PConj A B) = SPAnd (pterm_prop_template A) (pterm_prop_template B)"
| "pterm_prop_template (PDisj A B) = SPOr (pterm_prop_template A) (pterm_prop_template B)"
| "pterm_prop_template (PImp A B) = SPImp (pterm_prop_template A) (pterm_prop_template B)"
| "pterm_prop_template (PForall \<sigma> A) = SPAtom (PForall \<sigma> A)"
| "pterm_prop_template (PExists \<sigma> A) = SPAtom (PExists \<sigma> A)"

lemma pterm_prop_template_eval:
  "sprop_eval v (pterm_prop_template A) = pprop_eval v A"
  by (induction A) simp_all

lemma pterm_prop_template_instance:
  "paper_prop_instance pterm_to_paper (pterm_prop_template A) = pterm_to_paper A"
  by (induction A) simp_all

lemma pterm_prop_template_tautology:
  assumes taut: "pprop_tautology \<Gamma> A"
  shows "sprop_tautology (pterm_prop_template A)"
proof (unfold sprop_tautology_def, rule allI)
  fix v
  have all: "\<forall>v. pprop_eval v A"
    by (rule conjunct2[OF taut[unfolded pprop_tautology_def]])
  have "pprop_eval v A" by (rule spec[where x=v, OF all])
  then show "sprop_eval v (pterm_prop_template A)" by (simp only: pterm_prop_template_eval)
qed

theorem pterm_to_paper_PC:
  assumes taut: "pprop_tautology \<Gamma> A" and names: "pterm_in_signature \<Sigma> A"
  shows "paper_PC \<Sigma> \<Gamma> (pterm_to_paper A)"
proof -
  have typed: "has_ptype \<Gamma> A Prop"
    by (rule conjunct1[OF taut[unfolded pprop_tautology_def]])
  have language: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF typed names])
  have source_language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (pterm_to_paper A) Prop"
    by (rule pterm_to_paper_language[OF language])
  have template_taut: "sprop_tautology (pterm_prop_template A)"
    by (rule pterm_prop_template_tautology[OF taut])
  obtain Q :: "nat sprop_template" and w where qt: "sprop_tautology Q"
    and reconstruction: "paper_prop_instance w Q =
      paper_prop_instance pterm_to_paper (pterm_prop_template A)"
    by (rule paper_prop_instance_nat_template[OF template_taut]; rule that; assumption)
  have reverse_eq: "paper_prop_instance w Q = pterm_to_paper A"
    using reconstruction by (simp only: pterm_prop_template_instance)
  have eq: "pterm_to_paper A = paper_prop_instance w Q" by (rule sym[OF reverse_eq])
  show ?thesis unfolding paper_PC_def
  proof (rule conjI[OF source_language])
    show "\<exists>P :: nat sprop_template. \<exists>v. sprop_tautology P \<and> pterm_to_paper A = paper_prop_instance v P"
      by (rule exI[where x=Q], rule exI[where x=w], rule conjI[OF qt eq])
  qed
qed

end
