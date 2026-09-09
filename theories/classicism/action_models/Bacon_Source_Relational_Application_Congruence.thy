theory Bacon_Source_Relational_Application_Congruence
  imports Bacon_Source_Relational_Application_Identity_Tests
begin

section \<open>Changing an argument preserves local theorem-identity\<close>

text \<open>
  From A=σB derive FA=τFB by LL with λn.(FA=τF n).
  From F=σ→τH derive FA=τHA by LL with λn.(FA=τn A).
  The tests start from Ref and are unfolded by literal capture-safe β.
  Source: Figure 2, p.8; representative independence for the application
  in Theorem 3.2's closed-term model, footnote 64, p.45.

  All displayed terms retain independent R-language guards. In
  particular F:σ→τ entails σ→τ∈R and τ≠e. Terms and
  premises may be open, and each fresh name avoids only the finite
  free-variable set of the fixed terms in its predicate. No
  Functionality, model congruence or new equality rule is assumed.
\<close>

theorem paper_R_named_identity_App_argument:
  assumes rich: "paper_R_rich G" and head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp F A) (NApp F B))"
proof -
  let ?L = "NApp F A"
  have ll: "paper_R_in_language \<Sigma> G ?L \<tau>" by (rule paper_R_language_App[OF head left])
  have rl: "paper_R_in_language \<Sigma> G (NApp F B) \<tau>" by (rule paper_R_language_App[OF head right])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF left])
  obtain n where nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv ?L"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<sigma> and S="named_fv ?L", OF rich rt named_fv_finite])
  have fresh_head: "n \<notin> named_fv F" using fresh by auto
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF nt rt])
  have at_name: "paper_R_in_language \<Sigma> G (NApp F (NVar n)) \<tau>"
    by (rule paper_R_language_App[OF head variable])
  let ?P = "named_paper_eq \<tau> ?L (NApp F (NVar n))"
  let ?Test = "NLam n ?P"
  have body: "paper_R_in_language \<Sigma> G ?P Prop"
    by (rule paper_R_named_identity_language[OF ll at_name])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have raw_predicate: "paper_R_in_language \<Sigma> G ?Test (Arr (G n) Prop)"
    by (rule paper_R_named_identity_test_language[OF body nr])
  have predicate: "paper_R_in_language \<Sigma> G ?Test (Arr \<sigma> Prop)"
    using raw_predicate by (simp only: nt)
  have xl: "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> ?L ?L) Prop"
    by (rule paper_R_named_identity_language[OF ll ll])
  have yl: "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> ?L (NApp F B)) Prop"
    by (rule paper_R_named_identity_language[OF ll rl])
  have first_step: "named_compatible_step named_beta_contract (NApp ?Test A) (named_paper_eq \<tau> ?L ?L)"
    by (rule paper_R_identity_argument_test_beta[OF fresh fresh_head])
  have second_step: "named_compatible_step named_beta_contract (NApp ?Test B) (named_paper_eq \<tau> ?L (NApp F B))"
    by (rule paper_R_identity_argument_test_beta[OF fresh fresh_head])
  have initial: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?L ?L)"
    by (rule paper_R_named_identity_refl[OF ll])
  show ?thesis by (rule paper_R_named_derivable_LL_beta[
    OF rich left right predicate xl yl first_step second_step equality initial])
qed

section \<open>Changing the function uses a higher-type predicate, not Functionality\<close>

theorem paper_R_named_identity_App_head:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and right: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (Arr \<sigma> \<tau>) F H)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp F A) (NApp H A))"
proof -
  let ?L = "NApp F A"
  have ll: "paper_R_in_language \<Sigma> G ?L \<tau>" by (rule paper_R_language_App[OF left argument])
  have rl: "paper_R_in_language \<Sigma> G (NApp H A) \<tau>" by (rule paper_R_language_App[OF right argument])
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF left])
  obtain n where nt: "G n = Arr \<sigma> \<tau>" and fresh: "n \<notin> named_fv ?L"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="Arr \<sigma> \<tau>" and S="named_fv ?L",
      OF rich rt named_fv_finite])
  have fresh_argument: "n \<notin> named_fv A" using fresh by auto
  have variable: "paper_R_in_language \<Sigma> G (NVar n) (Arr \<sigma> \<tau>)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF nt rt])
  have at_name: "paper_R_in_language \<Sigma> G (NApp (NVar n) A) \<tau>"
    by (rule paper_R_language_App[OF variable argument])
  let ?P = "named_paper_eq \<tau> ?L (NApp (NVar n) A)"
  let ?Test = "NLam n ?P"
  have body: "paper_R_in_language \<Sigma> G ?P Prop"
    by (rule paper_R_named_identity_language[OF ll at_name])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have raw_predicate: "paper_R_in_language \<Sigma> G ?Test (Arr (G n) Prop)"
    by (rule paper_R_named_identity_test_language[OF body nr])
  have predicate: "paper_R_in_language \<Sigma> G ?Test (Arr (Arr \<sigma> \<tau>) Prop)"
    using raw_predicate by (simp only: nt)
  have xl: "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> ?L ?L) Prop"
    by (rule paper_R_named_identity_language[OF ll ll])
  have yl: "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> ?L (NApp H A)) Prop"
    by (rule paper_R_named_identity_language[OF ll rl])
  have first_step: "named_compatible_step named_beta_contract (NApp ?Test F) (named_paper_eq \<tau> ?L ?L)"
    by (rule paper_R_identity_head_test_beta[OF fresh fresh_argument])
  have second_step: "named_compatible_step named_beta_contract (NApp ?Test H) (named_paper_eq \<tau> ?L (NApp H A))"
    by (rule paper_R_identity_head_test_beta[OF fresh fresh_argument])
  have initial: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?L ?L)"
    by (rule paper_R_named_identity_refl[OF ll])
  show ?thesis by (rule paper_R_named_derivable_LL_beta[
    OF rich left right predicate xl yl first_step second_step equality initial])
qed

theorem paper_R_named_identity_App:
  assumes rich: "paper_R_rich G" and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
    and heads: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (Arr \<sigma> \<tau>) F H)"
    and arguments: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp F A) (NApp H B))"
proof -
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp F A) (NApp H A))"
    by (rule paper_R_named_identity_App_head[OF rich fl hl al heads])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp H A) (NApp H B))"
    by (rule paper_R_named_identity_App_argument[OF rich hl al bl arguments])
  show ?thesis by (rule paper_R_named_identity_trans[OF rich
    paper_R_language_App[OF fl al] paper_R_language_App[OF hl al] paper_R_language_App[OF hl bl] first second])
qed

end
