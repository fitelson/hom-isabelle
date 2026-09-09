theory Bacon_Source_Target_Set_Context_Elimination
  imports Bacon_Source_Target_Context_Elimination
begin

section \<open>A closed premise set is unchanged by extending the variable frame\<close>

text \<open>
  Let S be a set of closed sentences of ℒ(Σ). Every member remains typed
  in a larger variable frame, and shifting its free slots changes nothing.
  Source role: retaining the variables needed by a proof before removing
  unused variables from a closed conclusion (Bacon–Dorr pp.7–9).

  Isabelle representation: pH_typed_theory Σ [] S requires empty-context
  typing and signature membership for every member. It does not require
  S to be finite. The shift equality below is equality of raw syntax.

  Status: target typing and set equations only, with no model or
  signature-inhabitant assumption.
\<close>

lemma source_target_closed_theory_member:
  assumes closed_S: "pH_typed_theory \<Sigma> [] S" and member: "A \<in> S"
  shows "pterm_in_language \<Sigma> [] A Prop"
  unfolding pterm_in_language_def
  by (rule bspec[OF closed_S[unfolded pH_typed_theory_def] member])

lemma source_target_closed_theory_in_context:
  assumes closed_S: "pH_typed_theory \<Sigma> [] S"
  shows "pH_typed_theory \<Sigma> \<Gamma> S"
proof (unfold pH_typed_theory_def, rule ballI)
  fix A
  assume member: "A \<in> S"
  have closed: "pterm_in_language \<Sigma> [] A Prop"
    by (rule source_target_closed_theory_member[OF closed_S member])
  have current: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    by (rule source_target_closed_language_in_context[OF closed])
  show "has_ptype \<Gamma> A Prop \<and> pterm_in_signature \<Sigma> A"
    using current by (simp only: pterm_in_language_def)
qed

lemma source_target_closed_set_shift:
  assumes closed_S: "pH_typed_theory \<Sigma> [] S"
  shows "image pshift S = S"
proof -
  have images: "image pshift S = image (\<lambda>A. A) S"
  proof (rule image_cong[OF refl])
    fix A
    assume member: "A \<in> S"
    have closed: "pterm_in_language \<Sigma> [] A Prop"
      by (rule source_target_closed_theory_member[OF closed_S member])
    have typed: "has_ptype [] A Prop"
      using closed unfolding pterm_in_language_def by (rule conjunct1)
    show "pshift A = A" by (rule source_target_closed_shift[OF typed])
  qed
  show ?thesis using images by simp
qed

section \<open>Removing unused target contexts from closed-set consequences\<close>

text \<open>
  If S and A are closed and Σ;Γ;S ⊢H A, then Σ;[];S ⊢H A.
  No finiteness of S is required: derivability already uses finite proofs.

  Isabelle representation: each context-induction step reuses
  pH_remove_unused_slot. Since image pshift S = S and pshift A = A,
  its shifted-premise form applies to the unchanged closed set.

  Status: syntactic target set-consequence transport. The underlying
  unused-slot lemma uses Inst and the represented target all-type Existence
  theorem, as in the theoremhood-only context helper. It assumes no
  closed term inhabiting a type in Σ and adds no source existence axiom.
\<close>

theorem source_target_closed_set_context_elimination:
  fixes \<Sigma> :: "'c psignature" and S :: "'c pterm set" and A :: "'c pterm"
  assumes closed_S: "pH_typed_theory \<Sigma> [] S"
    and language: "pterm_in_language \<Sigma> [] A Prop"
    and derivation: "pH_set_derivable \<Sigma> \<Gamma> S A"
  shows "pH_set_derivable \<Sigma> [] S A"
  using derivation
proof (induction \<Gamma>)
  case Nil
  show ?case by (rule Nil.prems)
next
  case (Cons \<sigma> \<Gamma>)
  have current_theory: "pH_typed_theory \<Sigma> \<Gamma> S"
    by (rule source_target_closed_theory_in_context[OF closed_S])
  have current_language: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    by (rule source_target_closed_language_in_context[OF language])
  have closed_type: "has_ptype [] A Prop"
    using language unfolding pterm_in_language_def by (rule conjunct1)
  have shifted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
    using Cons.prems
    by (simp only: source_target_closed_set_shift[OF closed_S] source_target_closed_shift[OF closed_type])
  have descended: "pH_set_derivable \<Sigma> \<Gamma> S A"
    by (rule pH_remove_unused_slot[OF current_theory current_language shifted])
  show ?case by (rule Cons.IH[OF descended])
qed

end
