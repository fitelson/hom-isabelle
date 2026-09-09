theory Bacon_Source_Relational_Henkin_Existential_Membership
  imports Bacon_Source_Relational_Henkin_Boolean_Membership
    Bacon_Source_Relational_Quantifier_Duality Bacon_Source_Relational_Identity_Application
begin

section \<open>Closed quantifier and constant terms\<close>

lemma paper_R_closed_terms_All:
  assumes predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "named_paper_all \<sigma> F \<in> paper_R_closed_terms \<Omega> G Prop"
proof (rule paper_R_closed_termsI)
  show "paper_R_in_language \<Omega> G (named_paper_all \<sigma> F) Prop"
    by (rule paper_R_predicate_all_language[OF paper_R_closed_terms_language[OF predicate]])
  show "named_fv (named_paper_all \<sigma> F) = {}"
    by (simp only: named_paper_primitive_fv; rule paper_R_closed_terms_closed[OF predicate])
qed

lemma paper_R_closed_terms_Ex:
  assumes predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "named_paper_ex \<sigma> F \<in> paper_R_closed_terms \<Omega> G Prop"
proof (rule paper_R_closed_termsI)
  show "paper_R_in_language \<Omega> G (named_paper_ex \<sigma> F) Prop"
    by (rule paper_R_predicate_exists_language[OF paper_R_closed_terms_language[OF predicate]])
  show "named_fv (named_paper_ex \<sigma> F) = {}"
    by (simp only: named_paper_primitive_fv; rule paper_R_closed_terms_closed[OF predicate])
qed

lemma paper_R_closed_terms_Const:
  assumes rt: "paper_R_type \<sigma>" and declared: "c \<in> \<Omega> \<sigma>"
  shows "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
proof (rule paper_R_closed_termsI)
  have ct: "paper_R_has_type G (NConst c \<sigma>) \<sigma>" by (rule paper_R_has_type.Const[OF rt])
  show "paper_R_in_language \<Omega> G (NConst c \<sigma>) \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF ct]; simp only: named_in_signature.simps; rule declared)
  show "named_fv (NConst c \<sigma>) = {}" by simp
qed

section \<open>Existential membership quantifies over every closed argument\<close>

text \<open>
  ∃σF∈M iff FA∈M for some closed A:σ. The forward implication
  supplies an actual declared constant by Henkin witness completeness;
  the reverse uses EG on an arbitrary closed argument, not just a
  constant. Source: Theorem 3.2, footnote 64, p.45.
  No semantic model or assumption of universal constant denotability
  is used.
\<close>

theorem paper_R_closed_Henkin_exists_member:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "named_paper_ex \<sigma> F \<in> M \<longleftrightarrow>
    (\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M)"
proof -
  have fl: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    by (rule paper_R_closed_terms_language[OF predicate])
  have fc: "named_fv F = {}" by (rule paper_R_closed_terms_closed[OF predicate])
  show ?thesis
  proof
    assume existential: "named_paper_ex \<sigma> F \<in> M"
    obtain c where declared: "c \<in> \<Omega> \<sigma>" and instance_member: "NApp F (NConst c \<sigma>) \<in> M"
      by (rule paper_R_closed_constant_witness_completeD[
        OF paper_R_closed_Henkin_witness_complete[OF Henkin] fl fc existential])
    have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
    have argument: "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
      by (rule paper_R_closed_terms_Const[where \<Omega>=\<Omega> and G=G and \<sigma>=\<sigma> and c=c, OF rt declared])
    show "\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
      by (rule bexI[where x="NConst c \<sigma>"], rule instance_member, rule argument)
  next
    assume some: "\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    obtain A where argument: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>" and member: "NApp F A \<in> M" using some by blast
    have fa: "paper_R_in_language \<Omega> G (NApp F A) Prop"
      by (rule paper_R_closed_terms_language[OF paper_R_closed_terms_App[OF predicate argument]])
    have existential: "named_paper_ex \<sigma> F \<in> paper_R_closed_terms \<Omega> G Prop"
      by (rule paper_R_closed_terms_Ex[OF predicate])
    have eg: "paper_R_named_H \<Omega> G (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F))"
      by (rule paper_R_named_H.EG[OF paper_R_named_paper_imp_language[
        OF rich fa paper_R_closed_terms_language[OF existential]]])
    show "named_paper_ex \<sigma> F \<in> M" by (rule paper_R_closed_Henkin_H_MP[OF Henkin member eg existential])
  qed
qed

end
