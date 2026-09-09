theory Bacon_Source_Reverse_Syntax
  imports Bacon_Source_Propositional
begin

section \<open>Re-expressing target syntax in the paper's first-class language\<close>

text \<open>
  Target variables, nonlogical constants, application, and abstraction
  retain their structure.  Identity becomes =σ A B; Boolean connectives
  become the paper's connectives, including its literal defined →.
  Target ∀x:σ.A and ∃x:σ.A become ∀σ(λx:σ.A) and ∃σ(λx:σ.A).
  Source: Bacon--Dorr §1.1 and Figure 1, pp.5–6.

  Isabelle representation.  pterm_to_paper maps arbitrary-name 'c pterm
  into 'c paper_term without changing nonlogical names or their type tags.
  PImp maps to paper_imp, not a new source primitive.  PForall/PExists
  insert the first-class logical constant and a source SLam.
  Status.  This leaf proves finite-context typing preservation and exact
  signature membership.  It asserts no proof reflection, semantic
  preservation, or literal inverse equation with paper_to_pterm.
\<close>

fun pterm_to_paper :: "'c pterm \<Rightarrow> 'c paper_term" where
  "pterm_to_paper (PVar n) = SVar n"
| "pterm_to_paper (PConst c \<sigma>) = SConst c \<sigma>"
| "pterm_to_paper (PApp F A) = SApp (pterm_to_paper F) (pterm_to_paper A)"
| "pterm_to_paper (PLam \<sigma> A) = SLam \<sigma> (pterm_to_paper A)"
| "pterm_to_paper (PEq \<sigma> A B) =
    SApp (SApp (SLogical (SEq \<sigma>)) (pterm_to_paper A)) (pterm_to_paper B)"
| "pterm_to_paper (PNeg A) = paper_not (pterm_to_paper A)"
| "pterm_to_paper (PConj A B) = paper_and (pterm_to_paper A) (pterm_to_paper B)"
| "pterm_to_paper (PDisj A B) = paper_or (pterm_to_paper A) (pterm_to_paper B)"
| "pterm_to_paper (PImp A B) = paper_imp (pterm_to_paper A) (pterm_to_paper B)"
| "pterm_to_paper (PForall \<sigma> A) = SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (pterm_to_paper A))"
| "pterm_to_paper (PExists \<sigma> A) = SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (pterm_to_paper A))"

theorem pterm_to_paper_type:
  assumes typed: "has_ptype \<Gamma> A \<tau>"
  shows "has_stype paper_logical_type \<Gamma> (pterm_to_paper A) \<tau>"
  using typed
proof (induction rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  show ?case using has_stype.Var[OF PVar.hyps] by simp
next
  case PConst
  show ?case by (simp only: pterm_to_paper.simps) (rule has_stype.Const)
next
  case PApp
  show ?case using has_stype.App[OF PApp.IH(1) PApp.IH(2)] by simp
next
  case PLam
  show ?case using has_stype.Lam[OF PLam.IH] by simp
next
  case (PEq \<Gamma> A \<sigma> B)
  have head: "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)" by simp
  show ?case using paper_binary_logical_type[OF head PEq.IH(1) PEq.IH(2)] by simp
next
  case PNeg
  show ?case using paper_not_type[OF PNeg.IH] by simp
next
  case PConj
  show ?case using paper_and_type[OF PConj.IH(1) PConj.IH(2)] by simp
next
  case PDisj
  show ?case using paper_or_type[OF PDisj.IH(1) PDisj.IH(2)] by simp
next
  case PImp
  show ?case using paper_imp_type[OF PImp.IH(1) PImp.IH(2)] by simp
next
  case (PForall \<sigma> \<Gamma> A)
  have predicate_type: "has_stype paper_logical_type \<Gamma> (SLam \<sigma> (pterm_to_paper A)) (Arr \<sigma> Prop)"
    by (rule has_stype.Lam[OF PForall.IH])
  have head: "paper_logical_type (SAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  show ?case using paper_unary_logical_type[OF head predicate_type] by simp
next
  case (PExists \<sigma> \<Gamma> A)
  have predicate_type: "has_stype paper_logical_type \<Gamma> (SLam \<sigma> (pterm_to_paper A)) (Arr \<sigma> Prop)"
    by (rule has_stype.Lam[OF PExists.IH])
  have head: "paper_logical_type (SEx \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  show ?case using paper_unary_logical_type[OF head predicate_type] by simp
qed

theorem pterm_to_paper_signature_iff:
  "sterm_in_signature \<Sigma> (pterm_to_paper A) \<longleftrightarrow> pterm_in_signature \<Sigma> A"
  by (induction A) simp_all

corollary pterm_to_paper_language:
  assumes language: "pterm_in_language \<Sigma> \<Gamma> A \<tau>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (pterm_to_paper A) \<tau>"
proof -
  have typed: "has_ptype \<Gamma> A \<tau>" using language unfolding pterm_in_language_def by (rule conjunct1)
  have names: "pterm_in_signature \<Sigma> A" using language unfolding pterm_in_language_def by (rule conjunct2)
  have source_names: "sterm_in_signature \<Sigma> (pterm_to_paper A)"
    using names by (simp only: pterm_to_paper_signature_iff)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF pterm_to_paper_type[OF typed] source_names])
qed

end
