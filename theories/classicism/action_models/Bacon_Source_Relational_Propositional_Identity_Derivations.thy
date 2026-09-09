theory Bacon_Source_Relational_Propositional_Identity_Derivations
  imports Bacon_Source_Relational_Application_Identity_Tests Bacon_Source_Relational_Identity_Classes
begin

section \<open>Propositional identity transfers local derivability by LL\<close>

lemma paper_R_named_identity_lambda_beta:
  "named_compatible_step named_beta_contract (NApp (NLam n (NVar n)) A) A"
proof -
  have free_for: "named_free_for A n (NVar n)" by simp
  have contract: "named_beta_contract (NApp (NLam n (NVar n)) A) A"
    using named_beta_contract.beta[OF free_for] by simp
  show ?thesis by (rule named_compatible_step.root[
    where R=named_beta_contract and M="NApp (NLam n (NVar n)) A" and N=A, OF contract])
qed

theorem paper_R_named_derivable_propositional_identity:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A Prop"
    and right: "paper_R_in_language \<Sigma> G B Prop"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop A B)"
    and antecedent: "paper_R_named_derivable \<Sigma> G S A"
  shows "paper_R_named_derivable \<Sigma> G S B"
proof -
  let ?n = "named_paper_p G"
  let ?F = "NLam ?n (NVar ?n)"
  have nt: "G ?n = Prop" by (rule paper_R_named_paper_p_type[OF rich])
  have rt: "paper_R_type Prop" by simp
  have variable: "paper_R_in_language \<Sigma> G (NVar ?n) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n="?n", OF nt rt])
  have nr: "paper_R_type (G ?n)" by (simp only: nt; rule rt)
  have raw_predicate: "paper_R_in_language \<Sigma> G ?F (Arr (G ?n) Prop)"
    by (rule paper_R_named_identity_test_language[OF variable nr])
  have predicate: "paper_R_in_language \<Sigma> G ?F (Arr Prop Prop)"
    using raw_predicate by (simp only: nt)
  show ?thesis by (rule paper_R_named_derivable_LL_beta[
    OF rich left right predicate left right paper_R_named_identity_lambda_beta
      paper_R_named_identity_lambda_beta equality antecedent])
qed

section \<open>Closed-consequence closure makes identity preserve membership\<close>

text \<open>
  If M is closed under its closed local consequences and A,B are
  closed propositions with M⊢HᴿA=B, then A∈M iff B∈M.
  Source: well-definedness of the valuation in Theorem 3.2,
  footnote 64, p.45. The proof is syntactic: assume membership,
  use the local Assumption rule and LL, and return by closed closure.

  No consistency or truth-value collapse is needed for this implication.
  It is not the converse Propositional Equivalence rule. Open formulas
  remain permitted in the preceding local transfer theorem.
\<close>

theorem paper_R_closed_propositional_identity_membership:
  assumes rich: "paper_R_rich G"
    and closure: "\<And>P. paper_R_named_derivable \<Omega> G M P \<Longrightarrow> named_fv P = {} \<Longrightarrow> P \<in> M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop"
    and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
    and equality: "paper_R_named_derivable \<Omega> G M (named_paper_eq Prop A B)"
  shows "A \<in> M \<longleftrightarrow> B \<in> M"
proof -
  have al: "paper_R_in_language \<Omega> G A Prop" by (rule paper_R_closed_terms_language[OF first])
  have bl: "paper_R_in_language \<Omega> G B Prop" by (rule paper_R_closed_terms_language[OF second])
  have ac: "named_fv A = {}" by (rule paper_R_closed_terms_closed[OF first])
  have bc: "named_fv B = {}" by (rule paper_R_closed_terms_closed[OF second])
  show ?thesis
  proof
    assume member: "A \<in> M"
    have a: "paper_R_named_derivable \<Omega> G M A" by (rule paper_R_named_derivable.Assumption[OF member al])
    have b: "paper_R_named_derivable \<Omega> G M B"
      by (rule paper_R_named_derivable_propositional_identity[OF rich al bl equality a])
    show "B \<in> M" by (rule closure[OF b bc])
  next
    assume member: "B \<in> M"
    have b: "paper_R_named_derivable \<Omega> G M B" by (rule paper_R_named_derivable.Assumption[OF member bl])
    have reverse: "paper_R_named_derivable \<Omega> G M (named_paper_eq Prop B A)"
      by (rule paper_R_named_identity_sym[OF rich al bl equality])
    have a: "paper_R_named_derivable \<Omega> G M A"
      by (rule paper_R_named_derivable_propositional_identity[OF rich bl al reverse b])
    show "A \<in> M" by (rule closure[OF a ac])
  qed
qed

end
