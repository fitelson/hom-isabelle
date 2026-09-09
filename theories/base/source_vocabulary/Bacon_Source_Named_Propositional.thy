theory Bacon_Source_Named_Propositional
  imports Bacon_Source_Named_Logical_Encoding Bacon_Source_Global_H
begin

section \<open>Native named instances of independent Boolean templates\<close>

text \<open>
  PC includes each well-formed substitution instance of a classical
  propositional tautology (Bacon–Dorr Figure 2, p.8). The paper's →
  and ↔ abbreviations remain the named λ definitions of Figure 1, p.6.

  Isabelle representation. sprop_template and sprop_tautology describe
  finite Boolean templates independently of either object language.
  named_paper_prop_instance replaces their atoms by named formulas and
  builds their connectives using native named syntax. Logical encoding
  commutes exactly with instantiation, even under a surrounding binder
  stack. A rich G supplies the two distinct Prop names in the closed
  implication and biconditional definitions.

  Status. This is a propositional instance predicate and its forward
  representation theorem, not an H judgment or a semantic assertion.
  No primitive target implication is identified with a material replacement.
\<close>

fun named_paper_prop_instance ::
  "sgcontext \<Rightarrow> ('a \<Rightarrow> 'c paper_named_term) \<Rightarrow> 'a sprop_template \<Rightarrow> 'c paper_named_term" where
  "named_paper_prop_instance G v (SPAtom a) = v a"
| "named_paper_prop_instance G v (SPNot P) = named_paper_not (named_paper_prop_instance G v P)"
| "named_paper_prop_instance G v (SPAnd P Q) =
    named_paper_and (named_paper_prop_instance G v P) (named_paper_prop_instance G v Q)"
| "named_paper_prop_instance G v (SPOr P Q) =
    named_paper_or (named_paper_prop_instance G v P) (named_paper_prop_instance G v Q)"
| "named_paper_prop_instance G v (SPImp P Q) =
    named_paper_imp G (named_paper_prop_instance G v P) (named_paper_prop_instance G v Q)"
| "named_paper_prop_instance G v (SPIff P Q) =
    named_paper_iff G (named_paper_prop_instance G v P) (named_paper_prop_instance G v Q)"

theorem named_paper_prop_instance_encoding:
  assumes rich: "sg_rich G"
  shows "named_to_source G ns (named_paper_prop_instance G v P) =
    paper_prop_instance (\<lambda>a. named_to_source G ns (v a)) P"
proof (induction P)
  case (SPAtom a)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps)
next
  case (SPNot P)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps
    named_paper_not_encoding SPNot.IH)
next
  case (SPAnd P Q)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps
    named_paper_and_encoding SPAnd.IH)
next
  case (SPOr P Q)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps
    named_paper_or_encoding SPOr.IH)
next
  case (SPImp P Q)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps
    named_paper_imp_encoding[OF rich] SPImp.IH)
next
  case (SPIff P Q)
  show ?case by (simp only: named_paper_prop_instance.simps paper_prop_instance.simps
    named_paper_iff_encoding[OF rich] SPIff.IH)
qed

section \<open>PC is defined directly on named formulas\<close>

text \<open>
  The instantiated formula itself must belong to ℒ(Σ) and have type t.
  Only the finitely many schematic template positions use nat labels;
  the carrier of nonlogical constant names is unrestricted. The definition
  contains neither paper_global_PC nor an H theoremhood predicate.
\<close>

definition named_PC :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "named_PC \<Sigma> G A \<longleftrightarrow>
    named_in_language paper_logical_type \<Sigma> G A Prop \<and>
    (\<exists>P :: nat sprop_template. \<exists>v. sprop_tautology P \<and> A = named_paper_prop_instance G v P)"

lemma named_PC_language:
  "named_PC \<Sigma> G A \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G A Prop"
  unfolding named_PC_def by (rule conjunct1)

lemma named_PC_instance:
  fixes P :: "nat sprop_template"
  assumes taut: "sprop_tautology P"
    and language: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
  shows "named_PC \<Sigma> G (named_paper_prop_instance G v P)"
  unfolding named_PC_def
proof (rule conjI[OF language])
  show "\<exists>Q :: nat sprop_template. \<exists>w. sprop_tautology Q \<and>
    named_paper_prop_instance G v P = named_paper_prop_instance G w Q"
    by (rule exI[where x=P], rule exI[where x=v], rule conjI[OF taut refl])
qed

theorem named_PC_encoding:
  assumes rich: "sg_rich G" and pc: "named_PC \<Sigma> G A"
  shows "paper_global_PC \<Sigma> G (named_to_source G [] A)"
proof -
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule named_PC_language[OF pc])
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) Prop"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and instance_eq: "A = named_paper_prop_instance G v P"
    using conjunct2[OF pc[unfolded named_PC_def]] by (elim exE conjE)
  have encoded: "named_to_source G [] A = paper_prop_instance (\<lambda>a. named_to_source G [] (v a)) P"
    by (simp only: instance_eq named_paper_prop_instance_encoding[OF rich])
  show ?thesis unfolding paper_global_PC_def
  proof (rule conjI[OF encoded_language])
    show "\<exists>Q :: nat sprop_template. \<exists>w. sprop_tautology Q \<and>
      named_to_source G [] A = paper_prop_instance w Q"
      by (rule exI[where x=P], rule exI[where x="\<lambda>a. named_to_source G [] (v a)"],
        rule conjI[OF taut encoded])
  qed
qed

end
