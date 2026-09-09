theory Bacon_Source_Relational_H
  imports Bacon_Source_Relational_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Propositional
begin

section \<open>Independent Figure 2 theoremhood in the default R language\<close>

text \<open>
  The paper's H is the least theory with PC, UI, EG, Ref, LL,
  β, η, MP, Gen and Inst (Figure 2, p.8). Here every formula in
  a derivation belongs to the independently typed R language of
  §1.1, p.5. In particular, returning type t does not allow a
  formula containing quantification over a non-R type.

  PC uses Boolean templates and their literal named instances,
  with an R-language guard on the entire instance. The definition
  contains no F theoremhood or semantic-validity predicate. Only
  occurring atoms matter; no condition is imposed on unused entries
  of the template assignment.

  The closed → and ↔ operators are Figure 1's λ definitions,
  not primitive replacements. Their chosen binder names use only
  the Prop fiber of G. The source stock is R-rich; no F-richness
  premise is built into the judgment. Typing their abbreviations
  from R-richness is a separate syntactic obligation.

  β and η use ONE literal contextual contraction, with R-typed
  formula endpoints; the context may bind variables. No α, whole
  conversion, individual Existence or semantic rule is added.
  This leaf gives the declaration and formula-language invariant,
  not R soundness, completeness, or F-to-R conservativity.
\<close>

definition paper_R_named_PC ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_R_named_PC \<Sigma> G A \<longleftrightarrow>
    paper_R_in_language \<Sigma> G A Prop \<and>
    (\<exists>P :: nat sprop_template. \<exists>v.
      sprop_tautology P \<and> A = named_paper_prop_instance G v P)"

lemma paper_R_named_PC_language:
  "paper_R_named_PC \<Sigma> G A \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  unfolding paper_R_named_PC_def by (rule conjunct1)

inductive paper_R_named_H :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  PC: "paper_R_named_PC \<Sigma> G A \<Longrightarrow> paper_R_named_H \<Sigma> G A"
| UI: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A)) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A))"
| EG: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F)) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F))"
| Ref: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A A) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A A)"
| LL: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B))) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_eq \<sigma> A B)
      (named_paper_imp G (NApp F A) (NApp F B)))"
| Beta: "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
    named_compatible_step named_beta_contract A B \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
| Eta: "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
    named_compatible_step named_eta_contract A B \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
| MP: "paper_R_named_H \<Sigma> G A \<Longrightarrow> paper_R_named_H \<Sigma> G (named_paper_imp G A B) \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> paper_R_named_H \<Sigma> G B"
| Gen: "paper_R_named_H \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow> G n = \<sigma> \<Longrightarrow>
    n \<notin> named_fv P \<Longrightarrow> paper_R_in_language \<Sigma> G
      (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
| Inst: "paper_R_named_H \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow> G n = \<sigma> \<Longrightarrow>
    n \<notin> named_fv Q \<Longrightarrow> paper_R_in_language \<Sigma> G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
    paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"

lemma paper_R_named_H_language:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
  shows "paper_R_in_language \<Sigma> G A Prop"
  using derivation by (induction rule: paper_R_named_H.induct) (auto simp: paper_R_named_PC_def)


end

