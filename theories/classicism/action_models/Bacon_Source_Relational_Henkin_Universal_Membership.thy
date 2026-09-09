theory Bacon_Source_Relational_Henkin_Universal_Membership
  imports Bacon_Source_Relational_Henkin_Existential_Membership
begin

section \<open>A negative universal supplies a genuine counterexample constant\<close>

lemma paper_R_negative_predicate_beta:
  assumes fresh: "n \<notin> named_fv F"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam n (named_paper_not (NApp F (NVar n)))) A) (named_paper_not (NApp F A))"
proof -
  have free_F: "named_free_for A n F" by (rule named_free_for_fresh[OF fresh])
  have free_for: "named_free_for A n (named_paper_not (NApp F (NVar n)))"
    by (simp add: named_paper_not_def free_F)
  have substitution: "named_subst n A (named_paper_not (NApp F (NVar n))) = named_paper_not (NApp F A)"
    by (simp add: named_paper_not_def named_subst_fresh[OF fresh])
  have contract: "named_beta_contract
    (NApp (NLam n (named_paper_not (NApp F (NVar n)))) A) (named_paper_not (NApp F A))"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam n (named_paper_not (NApp F (NVar n)))) A"
    and N="named_paper_not (NApp F A)", OF contract])
qed

lemma paper_R_closed_Henkin_forall_counterexample:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
    and negative: "named_paper_not (named_paper_all \<sigma> F) \<in> M"
  obtains c where "c \<in> \<Omega> \<sigma>" "named_paper_not (NApp F (NConst c \<sigma>)) \<in> M"
proof -
  have fl: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)" by (rule paper_R_closed_terms_language[OF predicate])
  have fc: "named_fv F = {}" by (rule paper_R_closed_terms_closed[OF predicate])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  obtain n where nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<sigma> and S="named_fv F", OF rich rt named_fv_finite])
  let ?NF = "NLam n (named_paper_not (NApp F (NVar n)))"
  let ?X = "named_paper_ex \<sigma> ?NF"
  let ?A = "named_paper_not (named_paper_all \<sigma> F)"
  have variable: "paper_R_in_language \<Omega> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Omega> and G=G and n=n, OF nt rt])
  have body: "paper_R_in_language \<Omega> G (named_paper_not (NApp F (NVar n))) Prop"
    by (rule paper_R_named_not_language[OF paper_R_language_App[OF fl variable]])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have nfl: "paper_R_in_language \<Omega> G ?NF (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body nr] by (simp only: nt)
  have nfc: "named_fv ?NF = {}" by (simp add: named_paper_primitive_fv fc)
  have nf_closed: "?NF \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)" by (rule paper_R_closed_termsI[OF nfl nfc])
  have xc: "?X \<in> paper_R_closed_terms \<Omega> G Prop" by (rule paper_R_closed_terms_Ex[OF nf_closed])
  have xl: "paper_R_in_language \<Omega> G ?X Prop" by (rule paper_R_closed_terms_language[OF xc])
  have ac: "?A \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_not[OF paper_R_closed_terms_All[OF predicate]])
  have al: "paper_R_in_language \<Omega> G ?A Prop" by (rule paper_R_closed_terms_language[OF ac])
  have duality: "paper_R_named_H \<Omega> G (named_paper_iff G ?A ?X)"
    by (rule paper_R_named_H_quantifier_duality[OF rich fl nt fresh])
  have conditional: "paper_R_named_H \<Omega> G (named_paper_imp G ?A ?X)"
    by (rule paper_R_named_H.MP[OF duality paper_R_named_H_iff_forward[OF rich al xl]
      paper_R_named_paper_imp_language[OF rich al xl]])
  have existential: "?X \<in> M" by (rule paper_R_closed_Henkin_H_MP[OF Henkin negative conditional xc])
  obtain c where declared: "c \<in> \<Omega> \<sigma>" and instance_member: "NApp ?NF (NConst c \<sigma>) \<in> M"
    by (rule paper_R_closed_constant_witness_completeD[
      OF paper_R_closed_Henkin_witness_complete[OF Henkin] nfl nfc existential])
  have cc: "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    by (rule paper_R_closed_terms_Const[where \<Omega>=\<Omega> and G=G and \<sigma>=\<sigma> and c=c, OF rt declared])
  have source_closed: "NApp ?NF (NConst c \<sigma>) \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_App[OF nf_closed cc])
  have target_closed: "named_paper_not (NApp F (NConst c \<sigma>)) \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_not[OF paper_R_closed_terms_App[OF predicate cc]])
  have step: "named_compatible_step named_beta_contract
    (NApp ?NF (NConst c \<sigma>)) (named_paper_not (NApp F (NConst c \<sigma>)))"
    by (rule paper_R_negative_predicate_beta[OF fresh])
  have source_proof: "paper_R_named_derivable \<Omega> G M (NApp ?NF (NConst c \<sigma>))"
    by (rule paper_R_closed_Henkin_member_derivable[OF Henkin instance_member])
  have target_proof: "paper_R_named_derivable \<Omega> G M (named_paper_not (NApp F (NConst c \<sigma>)))"
    by (rule iffD1[OF paper_R_named_derivable_beta_iff[OF rich
      paper_R_closed_terms_language[OF source_closed] paper_R_closed_terms_language[OF target_closed] step] source_proof])
  have target_member: "named_paper_not (NApp F (NConst c \<sigma>)) \<in> M"
    by (rule paper_R_closed_Henkin_consequence[OF Henkin target_proof paper_R_closed_terms_closed[OF target_closed]])
  show thesis by (rule that[OF declared target_member])
qed

section \<open>Universal membership tests every closed argument\<close>

text \<open>
  ∀σF∈M iff FA∈M for every closed A:σ. UI proves the
  forward direction. For the reverse, failure of universal membership
  gives ¬∀σF, then the proved native duality and the actual constant
  witness above give ¬Fc. The assumed universal collection of
  closed instances includes Fc, contradicting consistency.
  Source: Theorem 3.2, footnote 64, p.45. No semantic quantifier law
  or restriction to constant-represented argument classes is imposed.
\<close>

theorem paper_R_closed_Henkin_forall_member:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "named_paper_all \<sigma> F \<in> M \<longleftrightarrow>
    (\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M)"
proof -
  have all_closed: "named_paper_all \<sigma> F \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_All[OF predicate])
  have all_language: "paper_R_in_language \<Omega> G (named_paper_all \<sigma> F) Prop"
    by (rule paper_R_closed_terms_language[OF all_closed])
  show ?thesis
  proof
    assume universal: "named_paper_all \<sigma> F \<in> M"
    show "\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    proof (intro ballI)
      fix A
      assume argument: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
      have instance_closed: "NApp F A \<in> paper_R_closed_terms \<Omega> G Prop"
        by (rule paper_R_closed_terms_App[OF predicate argument])
      have ui: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A))"
        by (rule paper_R_named_H.UI[OF paper_R_named_paper_imp_language[
          OF rich all_language paper_R_closed_terms_language[OF instance_closed]]])
      show "NApp F A \<in> M" by (rule paper_R_closed_Henkin_H_MP[OF Henkin universal ui instance_closed])
    qed
  next
    assume every: "\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    show "named_paper_all \<sigma> F \<in> M"
    proof (rule ccontr)
      assume absent: "named_paper_all \<sigma> F \<notin> M"
      have negative: "named_paper_not (named_paper_all \<sigma> F) \<in> M"
        by (rule iffD2[OF paper_R_closed_Henkin_not_member[OF Henkin all_closed] absent])
      obtain c where declared: "c \<in> \<Omega> \<sigma>" and counterexample: "named_paper_not (NApp F (NConst c \<sigma>)) \<in> M"
        by (rule paper_R_closed_Henkin_forall_counterexample[OF rich Henkin predicate negative])
      have rt: "paper_R_type \<sigma>"
        by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF paper_R_closed_terms_language[OF predicate]]])
      have cc: "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
        by (rule paper_R_closed_terms_Const[where \<Omega>=\<Omega> and G=G and \<sigma>=\<sigma> and c=c, OF rt declared])
      have positive: "NApp F (NConst c \<sigma>) \<in> M" using every cc by blast
      have instance_closed: "NApp F (NConst c \<sigma>) \<in> paper_R_closed_terms \<Omega> G Prop"
        by (rule paper_R_closed_terms_App[OF predicate cc])
      have negative_instance: "NApp F (NConst c \<sigma>) \<notin> M"
        by (rule iffD1[OF paper_R_closed_Henkin_not_member[OF Henkin instance_closed] counterexample])
      show False using positive negative_instance by contradiction
    qed
  qed
qed

end
