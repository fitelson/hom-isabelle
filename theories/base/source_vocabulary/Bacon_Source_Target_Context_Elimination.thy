theory Bacon_Source_Target_Context_Elimination
  imports
    "Bacon_Parametric_Signature_Development.Bacon_Parametric_Signature_Conservativity"
    "Bacon_Parametric_Signature_Development.Bacon_Parametric_Local_Quantifiers"
begin

section \<open>Removing unused target contexts from closed-sentence proofs\<close>

text \<open>
  If A is a closed sentence of ℒ(Σ) and Σ;Γ ⊢H A, then Σ;[] ⊢H A.
  Each unused variable slot is removed by the existing syntactic Inst
  argument, not by substituting a closed inhabitant of its type.

  Isabelle representation.  source_target_remove_unused_slot specializes
  pH_remove_unused_slot to the empty assumption set.  Closed typing
  implies that every free-variable renaming fixes A, so pshift A = A;
  the context induction can therefore remove one slot at a time.
  Status.  This is theorem transport in the represented target pH_proves.
  The underlying pH_all_type_existence theorem ultimately uses the target
  IndividualExistence presentation.  No source Existence axiom is added,
  no signature is enlarged, and no semantic model or Σ-inhabitant is assumed.
\<close>

lemma source_target_empty_set_to_theorem:
  assumes derivation: "pH_set_derivable \<Sigma> \<Gamma> {} A"
  shows "pH_proves \<Sigma> \<Gamma> A"
proof -
  obtain L where support: "set L \<subseteq> {}" and local_derivation: "pH_derivable \<Sigma> \<Gamma> L A"
    using derivation unfolding pH_set_derivable_def by (elim exE conjE)
  have empty: "L = []" using support by simp
  have local_empty: "pH_derivable \<Sigma> \<Gamma> [] A" using local_derivation by (simp only: empty)
  show ?thesis by (rule pH_local_empty_to_theorem[OF local_empty])
qed

lemma source_target_remove_unused_slot:
  fixes \<Sigma> :: "'c psignature" and A :: "'c pterm"
  assumes language: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and derivation: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pshift A)"
  shows "pH_proves \<Sigma> \<Gamma> A"
proof -
  have empty_typed: "pH_typed_theory \<Sigma> \<Gamma> {}"
    by (simp add: pH_typed_theory_def)
  have local_shifted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift {}) (pshift A)"
    by (rule pH_set_Theorem[OF derivation])
  have local_result: "pH_set_derivable \<Sigma> \<Gamma> {} A"
    by (rule pH_remove_unused_slot[OF empty_typed language local_shifted])
  show ?thesis by (rule source_target_empty_set_to_theorem[OF local_result])
qed

subsection \<open>Closed syntax is unchanged by shifting\<close>

lemma source_target_typed_rename_fixed:
  assumes typed: "has_ptype \<Gamma> A \<tau>"
    and fixed: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> r n = n"
  shows "prename r A = A"
  using typed fixed
proof (induction arbitrary: r rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  show ?case using PVar.prems[OF PVar.hyps] by simp
next
  case PConst
  show ?case by simp
next
  case PApp
  show ?case using PApp.IH(1)[OF PApp.prems] PApp.IH(2)[OF PApp.prems] by simp
next
  case PEq
  show ?case using PEq.IH(1)[OF PEq.prems] PEq.IH(2)[OF PEq.prems] by simp
next
  case PNeg
  show ?case using PNeg.IH[OF PNeg.prems] by simp
next
  case PConj
  show ?case using PConj.IH(1)[OF PConj.prems] PConj.IH(2)[OF PConj.prems] by simp
next
  case PDisj
  show ?case using PDisj.IH(1)[OF PDisj.prems] PDisj.IH(2)[OF PDisj.prems] by simp
next
  case PImp
  show ?case using PImp.IH(1)[OF PImp.prems] PImp.IH(2)[OF PImp.prems] by simp
next
  case (PLam \<sigma> \<Gamma> A \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow> lift_ren r n = n"
    using PLam.prems by (case_tac n) auto
  show ?case using PLam.IH[OF lifted] by simp
next
  case (PForall \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow> lift_ren r n = n"
    using PForall.prems by (case_tac n) auto
  show ?case using PForall.IH[OF lifted] by simp
next
  case (PExists \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow> lift_ren r n = n"
    using PExists.prems by (case_tac n) auto
  show ?case using PExists.IH[OF lifted] by simp
qed

lemma source_target_closed_rename:
  assumes closed_type: "has_ptype [] A \<tau>"
  shows "prename r A = A"
  by (rule source_target_typed_rename_fixed[OF closed_type]) (simp add: lookup_def)

lemma source_target_closed_shift:
  assumes closed_type: "has_ptype [] A \<tau>"
  shows "pshift A = A"
  unfolding pshift_def by (rule source_target_closed_rename[OF closed_type])

lemma source_target_closed_type_in_context:
  assumes closed_type: "has_ptype [] A \<tau>"
  shows "has_ptype \<Gamma> A \<tau>"
proof -
  have renamed: "has_ptype \<Gamma> (prename id A) \<tau>"
    by (rule prename_preserves_typing[OF closed_type]) (simp add: lookup_def)
  show ?thesis using renamed source_target_closed_rename[OF closed_type, where r=id] by simp
qed

lemma source_target_closed_language_in_context:
  assumes closed_language: "pterm_in_language \<Sigma> [] A \<tau>"
  shows "pterm_in_language \<Sigma> \<Gamma> A \<tau>"
proof -
  have closed_type: "has_ptype [] A \<tau>"
    using closed_language unfolding pterm_in_language_def by (rule conjunct1)
  have signature: "pterm_in_signature \<Sigma> A"
    using closed_language unfolding pterm_in_language_def by (rule conjunct2)
  show ?thesis unfolding pterm_in_language_def
    by (rule conjI[OF source_target_closed_type_in_context[OF closed_type] signature])
qed

theorem source_target_closed_context_elimination:
  assumes closed_language: "pterm_in_language \<Sigma> [] A Prop"
    and derivation: "pH_proves \<Sigma> \<Gamma> A"
  shows "pH_proves \<Sigma> [] A"
  using derivation
proof (induction \<Gamma>)
  case Nil
  show ?case by (rule Nil.prems)
next
  case (Cons \<sigma> \<Gamma>)
  have smaller_language: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    by (rule source_target_closed_language_in_context[OF closed_language])
  have closed_type: "has_ptype [] A Prop"
    using closed_language unfolding pterm_in_language_def by (rule conjunct1)
  have shifted_derivation: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pshift A)"
    using Cons.prems by (simp only: source_target_closed_shift[OF closed_type])
  have descended: "pH_proves \<Sigma> \<Gamma> A"
    by (rule source_target_remove_unused_slot[OF smaller_language shifted_derivation])
  show ?case by (rule Cons.IH[OF descended])
qed

end
