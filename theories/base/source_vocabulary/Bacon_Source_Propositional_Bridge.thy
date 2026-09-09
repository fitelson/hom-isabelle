theory Bacon_Source_Propositional_Bridge
  imports Bacon_Source_Propositional_Typing
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Deduction
begin

section \<open>Propositional templates in the expanded target syntax\<close>

text \<open>
  PC: each substitution instance of a propositional tautology is a theorem
  (Bacon–Dorr Figure 2, p. 8).  The paper defines A → B by ¬A ∨ B
  and A ↔ B by (¬A ∨ B) ∧ (¬B ∨ A) (Figure 1, p. 6).

  Isabelle representation: paper_expanded_prop uses only PNeg, PConj, and
  PDisj around its supplied atom terms.  It never replaces paper implication
  with primitive PImp.  The atom terms may themselves be arbitrary typed
  target formulas.

  Status: expanded-template evaluation and target PC theoremhood.
  Conversion from the literal translated source instance to this expansion
  is a separate, still-required congruence/β computation.
\<close>

fun paper_expanded_prop :: "('a \<Rightarrow> 'c pterm) \<Rightarrow> 'a sprop_template \<Rightarrow> 'c pterm" where
  "paper_expanded_prop v (SPAtom a) = v a"
| "paper_expanded_prop v (SPNot P) = PNeg (paper_expanded_prop v P)"
| "paper_expanded_prop v (SPAnd P Q) = PConj (paper_expanded_prop v P) (paper_expanded_prop v Q)"
| "paper_expanded_prop v (SPOr P Q) = PDisj (paper_expanded_prop v P) (paper_expanded_prop v Q)"
| "paper_expanded_prop v (SPImp P Q) =
    PDisj (PNeg (paper_expanded_prop v P)) (paper_expanded_prop v Q)"
| "paper_expanded_prop v (SPIff P Q) =
    PConj (PDisj (PNeg (paper_expanded_prop v P)) (paper_expanded_prop v Q))
      (PDisj (PNeg (paper_expanded_prop v Q)) (paper_expanded_prop v P))"

lemma paper_expanded_prop_eval:
  "pprop_eval w (paper_expanded_prop v P) = sprop_eval (\<lambda>a. pprop_eval w (v a)) P"
  by (induction P) auto

lemma paper_expanded_prop_type:
  assumes atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> has_ptype \<Gamma> (v a) Prop"
  shows "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
  using atoms
proof (induction P)
  case (SPAtom a)
  show ?case using SPAtom.prems[of a] by simp
next
  case (SPNot P)
  have p: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule SPNot.IH; rule SPNot.prems; simp_all)
  show ?case unfolding paper_expanded_prop.simps by (rule has_ptype.PNeg[OF p])
next
  case (SPAnd P Q)
  have p: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule SPAnd.IH(1); rule SPAnd.prems; simp_all)
  have q: "has_ptype \<Gamma> (paper_expanded_prop v Q) Prop"
    by (rule SPAnd.IH(2); rule SPAnd.prems; simp_all)
  show ?case unfolding paper_expanded_prop.simps by (rule has_ptype.PConj[OF p q])
next
  case (SPOr P Q)
  have p: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule SPOr.IH(1); rule SPOr.prems; simp_all)
  have q: "has_ptype \<Gamma> (paper_expanded_prop v Q) Prop"
    by (rule SPOr.IH(2); rule SPOr.prems; simp_all)
  show ?case unfolding paper_expanded_prop.simps by (rule has_ptype.PDisj[OF p q])
next
  case (SPImp P Q)
  have p: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule SPImp.IH(1); rule SPImp.prems; simp_all)
  have q: "has_ptype \<Gamma> (paper_expanded_prop v Q) Prop"
    by (rule SPImp.IH(2); rule SPImp.prems; simp_all)
  show ?case unfolding paper_expanded_prop.simps
    by (rule has_ptype.PDisj[OF has_ptype.PNeg[OF p] q])
next
  case (SPIff P Q)
  have p: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule SPIff.IH(1); rule SPIff.prems; simp_all)
  have q: "has_ptype \<Gamma> (paper_expanded_prop v Q) Prop"
    by (rule SPIff.IH(2); rule SPIff.prems; simp_all)
  show ?case unfolding paper_expanded_prop.simps
    by (rule has_ptype.PConj[OF has_ptype.PDisj[OF has_ptype.PNeg[OF p] q]
      has_ptype.PDisj[OF has_ptype.PNeg[OF q] p]])
qed

lemma paper_expanded_prop_signature_iff:
  "pterm_in_signature \<Sigma> (paper_expanded_prop v P) \<longleftrightarrow>
    (\<forall>a\<in>sprop_atoms P. pterm_in_signature \<Sigma> (v a))"
  by (induction P) auto

lemma paper_expanded_prop_tautology:
  assumes taut: "sprop_tautology P"
    and atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> has_ptype \<Gamma> (v a) Prop"
  shows "pprop_tautology \<Gamma> (paper_expanded_prop v P)"
proof -
  have typed: "has_ptype \<Gamma> (paper_expanded_prop v P) Prop"
    by (rule paper_expanded_prop_type[OF atoms])
  have every: "\<forall>w. pprop_eval w (paper_expanded_prop v P)"
  proof (rule allI)
    fix w
    have "sprop_eval (\<lambda>a. pprop_eval w (v a)) P"
      by (rule spec[where x="\<lambda>a. pprop_eval w (v a)", OF taut[unfolded sprop_tautology_def]])
    then show "pprop_eval w (paper_expanded_prop v P)" by (simp only: paper_expanded_prop_eval)
  qed
  show ?thesis unfolding pprop_tautology_def by (rule conjI[OF typed every])
qed

theorem paper_expanded_prop_PC:
  assumes taut: "sprop_tautology P"
    and atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> pterm_in_language \<Sigma> \<Gamma> (v a) Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_expanded_prop v P)"
proof -
  have typed: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> has_ptype \<Gamma> (v a) Prop"
  proof -
    fix a
    assume member: "a \<in> sprop_atoms P"
    show "has_ptype \<Gamma> (v a) Prop"
      using atoms[OF member] unfolding pterm_in_language_def by (rule conjunct1)
  qed
  have names: "pterm_in_signature \<Sigma> (paper_expanded_prop v P)"
  proof (rule iffD2[OF paper_expanded_prop_signature_iff], rule ballI)
    fix a
    assume member: "a \<in> sprop_atoms P"
    show "pterm_in_signature \<Sigma> (v a)"
      using atoms[OF member] unfolding pterm_in_language_def by (rule conjunct2)
  qed
  show ?thesis by (rule pH_proves.PC[OF paper_expanded_prop_tautology[OF taut typed] names])
qed

text \<open>
  From a paper PC instance A we obtain its template P and substitution v,
  together with a target proof of the materially expanded template.
  Status: this is not yet a proof of ⟦A⟧ itself.  The missing conversion
  bridge is not assumed, and paper_PC retains its original definition.
\<close>

theorem paper_PC_expanded_witness:
  assumes pc: "paper_PC \<Sigma> \<Gamma> A"
  obtains P :: "nat sprop_template" and v where "sprop_tautology P"
    and "A = paper_prop_instance v P"
    and "pH_proves \<Sigma> \<Gamma> (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
proof -
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and eq: "A = paper_prop_instance v P"
    and atoms: "\<forall>a\<in>sprop_atoms P. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
    by (rule paper_PC_atoms[OF pc]; rule that; assumption)
  have target_proof: "pH_proves \<Sigma> \<Gamma> (paper_expanded_prop (\<lambda>a. paper_to_pterm (v a)) P)"
  proof (rule paper_expanded_prop_PC[OF taut])
    fix a
    assume member: "a \<in> sprop_atoms P"
    have source: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
      by (rule bspec[OF atoms member])
    show "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm (v a)) Prop"
      by (rule iffD2[OF paper_to_pterm_language_iff source])
  qed
  show thesis by (rule that[OF taut eq target_proof])
qed

end
