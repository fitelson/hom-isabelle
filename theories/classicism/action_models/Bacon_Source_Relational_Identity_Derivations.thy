theory Bacon_Source_Relational_Identity_Derivations
  imports Bacon_Source_Relational_Identity_Proof_Basics
begin

section \<open>Local theorem-identity is reflexive, symmetric and transitive\<close>

text \<open>
  S⊢HᴿA=A; from S⊢HᴿA=B infer S⊢HᴿB=A; and from
  S⊢HᴿA=B and S⊢HᴿB=C infer S⊢HᴿA=C.
  Source: Ref and LL in Figure 2, p.8, and the closed-term
  theorem-identity relation in Theorem 3.2, footnote 64, p.45.

  Terms may be open, and S is an arbitrary local premise set.
  Symmetry uses a genuinely fresh typed name in λn.(n=A), with
  explicit capture-safe β steps. Transitivity uses the already typed
  partial application (=σ A). No equality rule, model law, F proof,
  or assumption of consistent or closed premises is introduced.
\<close>

theorem paper_R_named_identity_refl:
  assumes language: "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A A)"
  by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H.Ref[
    OF paper_R_named_identity_language[OF language language]]])

lemma paper_R_named_reverse_identity_beta:
  assumes fresh: "n \<notin> named_fv A"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam n (named_paper_eq \<sigma> (NVar n) A)) B) (named_paper_eq \<sigma> B A)"
proof -
  have free_A: "named_free_for B n A" by (rule named_free_for_fresh[OF fresh])
  have free_for: "named_free_for B n (named_paper_eq \<sigma> (NVar n) A)"
    by (simp add: named_paper_eq_def free_A)
  have substitution: "named_subst n B (named_paper_eq \<sigma> (NVar n) A) = named_paper_eq \<sigma> B A"
    by (simp add: named_paper_eq_def named_subst_fresh[OF fresh])
  have contract: "named_beta_contract
    (NApp (NLam n (named_paper_eq \<sigma> (NVar n) A)) B) (named_paper_eq \<sigma> B A)"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[
    where R=named_beta_contract and M="NApp (NLam n (named_paper_eq \<sigma> (NVar n) A)) B"
      and N="named_paper_eq \<sigma> B A", OF contract])
qed

theorem paper_R_named_identity_sym:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> B A)"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF left])
  obtain n where nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv A"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<sigma> and S="named_fv A",
      OF rich rt named_fv_finite])
  let ?C = "named_paper_eq \<sigma> (NVar n) A"
  let ?F = "NLam n ?C"
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF nt rt])
  have body: "paper_R_in_language \<Sigma> G ?C Prop"
    by (rule paper_R_named_identity_language[OF variable left])
  have body_type: "paper_R_has_type G ?C Prop"
    using body unfolding paper_R_in_language_def by (rule conjunct1)
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have abstraction: "paper_R_has_type G ?F (Arr (G n) Prop)"
    by (rule paper_R_has_type.Lam[OF body_type nr]; simp)
  have predicate: "paper_R_in_language \<Sigma> G ?F (Arr \<sigma> Prop)"
    using abstraction body by (auto simp: paper_R_in_language_def nt)
  have fa: "paper_R_in_language \<Sigma> G (NApp ?F A) Prop" by (rule paper_R_language_App[OF predicate left])
  have fb: "paper_R_in_language \<Sigma> G (NApp ?F B) Prop" by (rule paper_R_language_App[OF predicate right])
  have aa: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A A) Prop"
    by (rule paper_R_named_identity_language[OF left left])
  have ba: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> B A) Prop"
    by (rule paper_R_named_identity_language[OF right left])
  have reflexive: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A A)"
    by (rule paper_R_named_identity_refl[OF left])
  have first_step: "named_compatible_step named_beta_contract (NApp ?F A) (named_paper_eq \<sigma> A A)"
    by (rule paper_R_named_reverse_identity_beta[OF fresh])
  have first: "paper_R_named_derivable \<Sigma> G S (NApp ?F A)"
    by (rule iffD2[OF paper_R_named_derivable_beta_iff[OF rich fa aa first_step] reflexive])
  have second: "paper_R_named_derivable \<Sigma> G S (NApp ?F B)"
    by (rule paper_R_named_derivable_LL[OF rich left right predicate equality first])
  have second_step: "named_compatible_step named_beta_contract (NApp ?F B) (named_paper_eq \<sigma> B A)"
    by (rule paper_R_named_reverse_identity_beta[OF fresh])
  show ?thesis by (rule iffD1[OF paper_R_named_derivable_beta_iff[OF rich fb ba second_step] second])
qed

theorem paper_R_named_identity_trans:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and bl: "paper_R_in_language \<Sigma> G B \<sigma>" and cl: "paper_R_in_language \<Sigma> G C \<sigma>"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> B C)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A C)"
proof -
  let ?F = "NApp (NLogical (SEq \<sigma>)) A"
  have predicate: "paper_R_in_language \<Sigma> G ?F (Arr \<sigma> Prop)"
    by (rule paper_R_language_App[OF paper_R_named_identity_operator_language[
      OF paper_R_language_result_type[OF al]] al])
  have antecedent: "paper_R_named_derivable \<Sigma> G S (NApp ?F B)"
    using first by (simp only: named_paper_eq_def)
  have consequent: "paper_R_named_derivable \<Sigma> G S (NApp ?F C)"
    by (rule paper_R_named_derivable_LL[OF rich bl cl predicate second antecedent])
  show ?thesis using consequent by (simp only: named_paper_eq_def)
qed

end
