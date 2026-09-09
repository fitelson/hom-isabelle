theory Bacon_Book_Conjunction_Background_Fresh_Constant
  imports Bacon_Book_Conjunction_Background_Retraction
begin

section \<open>A fresh variable replaces an old constant in a proof from fixed Π\<close>

text \<open>
  If Π∧ ⊢Γ A, replace Inl(c):σ by a fresh x:σ and obtain another
  proof from the SAME Π∧ in Γ=target(Σ). The tag Inr(⋆) is retained.
  Source role: the nonlogical-substitution closure required by Definition
  5.2, p.99, for the primitive conjunction extension of §5.2, p.104.

  The finite set N follows the actual proof. We choose x outside N and
  the supplied finite forbidden set, retract the proof into the smaller
  signature, widen it back to Γ, then use ret(Π∧)⊆Π∧. This does not
  require freshness against all names of the infinite background.
  No empty-premise constant-substitution rule is applied to a Π-proof.
  The result is only fresh-variable replacement, not yet arbitrary-payload
  or simultaneous substitution, and no model or consistency is assumed.
\<close>

theorem book_conj_background_fresh_constant_variable:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and derivation: "book_theory_derivable (book_conj_target_signature \<Sigma>) G (book_conj_axioms \<Sigma> G) A"
    and finite_F: "finite F"
  shows "\<exists>x. G x = \<sigma> \<and> x \<notin> named_vars A \<union> F \<and>
    book_theory_derivable (book_conj_target_signature \<Sigma>) G (book_conj_axioms \<Sigma> G)
      (book_const_subst (Inl c) \<sigma> (NVar x) A)"
proof -
  let ?\<Gamma> = "book_conj_target_signature \<Sigma>"
  let ?\<Omega> = "book_remove_constant ?\<Gamma> (Inl c) \<sigma>"
  let ?P = "book_conj_axioms \<Sigma> G"
  obtain N where support: "book_theory_retraction_support ?\<Omega> G ?P A N"
    using book_theory_derivable_retraction_support[where \<Omega>="?\<Omega>", OF derivation] by (elim exE)
  have finite_N: "finite N" by (rule book_theory_retraction_support_finite[OF support])
  have names_in_N: "named_vars A \<subseteq> N"
    by (rule conjunct1[OF conjunct2[OF support[unfolded book_theory_retraction_support_def]]])
  have finite_union: "finite (N \<union> F)" by (rule finite_UnI[OF finite_N finite_F])
  obtain x where xtype: "G x = \<sigma>" and fresh: "x \<notin> N \<union> F"
    using sg_rich_fresh[where \<sigma>=\<sigma> and S="N \<union> F", OF rich finite_union] by (elim exE conjE)
  have outside_N: "x \<notin> N" using fresh by blast
  have endpoint_fresh: "x \<notin> named_vars A \<union> F" using fresh names_in_N by blast
  let ?w = "\<lambda>\<rho>. SOME n. G n = \<rho> \<and> n \<notin> N"
  have choices: "G (?w \<rho>) = \<rho> \<and> ?w \<rho> \<notin> N" for \<rho>
    by (rule someI_ex; rule sg_rich_fresh[OF rich finite_N])
  have wtype: "G (?w \<rho>) = \<rho>" for \<rho> by (rule conjunct1[OF choices])
  have wfresh: "?w \<rho> \<notin> N" for \<rho> by (rule conjunct2[OF choices])
  let ?v = "\<lambda>\<rho>. if \<rho> = \<sigma> then x else ?w \<rho>"
  have stock: "G (?v \<rho>) = \<rho>" for \<rho>
    by (cases "\<rho> = \<sigma>") (simp_all add: xtype wtype)
  have avoids: "?v \<rho> \<notin> N" for \<rho>
    by (cases "\<rho> = \<sigma>") (simp_all add: outside_N wfresh)
  have retracted: "book_theory_derivable ?\<Omega> G (image (named_retract ?\<Omega> ?v) ?P)
    (named_retract ?\<Omega> ?v A)"
    by (rule book_theory_retraction_support_apply[OF support stock avoids])
  have widened: "book_theory_derivable ?\<Gamma> G (image (named_retract ?\<Omega> ?v) ?P)
    (named_retract ?\<Omega> ?v A)"
    by (rule book_theory_signature_mono[OF retracted]; rule book_remove_constant_subset)
  have background_subset: "image (named_retract ?\<Omega> ?v) ?P \<subseteq> ?P"
    by (rule book_conj_background_retract_subset[
      where G=G and v="?v" and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>, OF stock])
  have restored_background: "book_theory_derivable ?\<Gamma> G ?P (named_retract ?\<Omega> ?v A)"
    by (rule book_theory_derivable_mono[OF widened background_subset])
  have original_names: "named_in_signature ?\<Gamma> A"
    by (rule book_language_signature[OF book_theory_derivable_language[OF derivation rich]])
  have representation: "named_retract ?\<Omega> ?v A = book_const_subst (Inl c) \<sigma> (NVar x) A"
    using book_remove_constant_retract[where c="Inl c" and \<sigma>=\<sigma> and v="?v", OF original_names] by simp
  have result: "book_theory_derivable ?\<Gamma> G ?P (book_const_subst (Inl c) \<sigma> (NVar x) A)"
    using restored_background by (simp only: representation)
  show ?thesis by (rule exI[where x=x], rule conjI[OF xtype conjI[OF endpoint_fresh result]])
qed

end
