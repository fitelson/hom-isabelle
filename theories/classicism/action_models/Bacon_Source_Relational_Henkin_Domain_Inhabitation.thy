theory Bacon_Source_Relational_Henkin_Domain_Inhabitation
  imports Bacon_Source_Relational_Closed_Henkin_Theory Bacon_Source_Relational_Identity_Classes
    Bacon_Source_Relational_Language_Inversion
begin

section \<open>Native Existence and Henkin witnesses supply declared constants\<close>

text \<open>
  For σ∈R, choose a variable n:σ and let Iσ=λn.(n=σn).
  Native H proves ∃σIσ. This existential is closed, so the
  Henkin theory's closed-consequence closure puts it in M. Its
  constant-witness property then supplies a declared c:σ.
  Source: Existence, pp.8–9, and the domain construction of
  Theorem 3.2, footnote 64, p.45.

  The variable is only an intermediate proof witness. No closed term
  or constant in Ω is assumed beforehand. The proof uses the
  independently derived R-H Existence theorem, not F Existence or
  semantic nonemptiness. The Henkin predicate is syntactic; no
  interpretation or BBK model is asserted by this leaf.
\<close>

theorem paper_R_closed_Henkin_declared_constant:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and rt: "paper_R_type \<sigma>"
  obtains c where "c \<in> \<Omega> \<sigma>"
proof -
  obtain n where nt: "G n = \<sigma>" and unused: "n \<notin> {}"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<sigma> and S="{}", OF rich rt finite.emptyI])
  let ?F = "NLam n (named_paper_eq \<sigma> (NVar n) (NVar n))"
  let ?E = "named_paper_ex \<sigma> ?F"
  have existence: "paper_R_named_H \<Omega> G ?E" by (rule paper_R_named_type_existence[OF nt rt rich])
  have derivation: "paper_R_named_derivable \<Omega> G M ?E"
    by (rule paper_R_named_derivable.Theorem[OF existence])
  have existential_closed: "named_fv ?E = {}" by (rule paper_R_named_type_existence_closed)
  have existential_member: "?E \<in> M"
    by (rule paper_R_closed_Henkin_consequence[OF Henkin derivation existential_closed])
  have existential_language: "paper_R_in_language \<Omega> G ?E Prop"
    by (rule paper_R_named_H_language[OF existence])
  have predicate: "paper_R_in_language \<Omega> G ?F (Arr \<sigma> Prop)"
    by (rule paper_R_ex_language_operand[OF existential_language])
  have predicate_closed: "named_fv ?F = {}" by (simp add: named_paper_eq_def)
  obtain c where declared: "c \<in> \<Omega> \<sigma>" and witness: "NApp ?F (NConst c \<sigma>) \<in> M"
    by (rule paper_R_closed_constant_witness_completeD[
      OF paper_R_closed_Henkin_witness_complete[OF Henkin] predicate predicate_closed existential_member])
  show thesis by (rule that[OF declared])
qed

corollary paper_R_closed_Henkin_signature_nonempty:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and rt: "paper_R_type \<sigma>"
  shows "\<Omega> \<sigma> \<noteq> {}"
proof -
  obtain c where declared: "c \<in> \<Omega> \<sigma>"
    by (rule paper_R_closed_Henkin_declared_constant[OF rich Henkin rt])
  show ?thesis using declared by blast
qed

section \<open>Closed terms and theorem-identity fibers are consequently inhabited\<close>

lemma paper_R_closed_Henkin_closed_constant:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and rt: "paper_R_type \<sigma>"
  obtains c where "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
proof -
  obtain c where declared: "c \<in> \<Omega> \<sigma>"
    by (rule paper_R_closed_Henkin_declared_constant[OF rich Henkin rt])
  have ct: "paper_R_has_type G (NConst c \<sigma>) \<sigma>" by (rule paper_R_has_type.Const[OF rt])
  have language: "paper_R_in_language \<Omega> G (NConst c \<sigma>) \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF ct]; simp only: named_in_signature.simps; rule declared)
  have closed: "named_fv (NConst c \<sigma>) = {}" by simp
  show thesis by (rule that[OF paper_R_closed_termsI[OF language closed]])
qed

theorem paper_R_closed_Henkin_closed_terms_nonempty:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and rt: "paper_R_type \<sigma>"
  shows "paper_R_closed_terms \<Omega> G \<sigma> \<noteq> {}"
proof -
  obtain c where member: "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    by (rule paper_R_closed_Henkin_closed_constant[OF rich Henkin rt])
  show ?thesis using member by blast
qed

theorem paper_R_closed_Henkin_identity_domain_nonempty:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and rt: "paper_R_type \<sigma>"
  shows "paper_R_identity_domain \<Omega> G M \<sigma> \<noteq> {}"
proof -
  obtain c where closed_term: "NConst c \<sigma> \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    by (rule paper_R_closed_Henkin_closed_constant[OF rich Henkin rt])
  have member: "paper_R_identity_class \<Omega> G M \<sigma> (NConst c \<sigma>) \<in> paper_R_identity_domain \<Omega> G M \<sigma>"
    by (rule paper_R_identity_domainI[OF closed_term])
  show ?thesis using member by blast
qed

end
