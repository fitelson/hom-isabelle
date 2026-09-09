theory Bacon_Source_Prefix_Preservation
  imports Bacon_Source_Global_H Bacon_Source_Conversion_Axioms
begin

section \<open>Finite prefixes of the fixed source variable stock\<close>

text \<open>
  Every source expression uses finitely many variables, but a proof may
  use more variables than its conclusion (Bacon–Dorr pp.7–9). We therefore
  retain the whole proof's finite support while translating it, rather
  than restrict each step to the free variables of its conclusion.

  Isabelle representation: source_prefix G m records the first m types of
  the total variable stock G. The bound source_free_bound A suffices for
  typing A in every larger prefix. No richness assumption is needed for
  these structural facts.
\<close>

definition source_prefix :: "sgcontext \<Rightarrow> nat \<Rightarrow> ctx" where
  "source_prefix G m = map G [0..<m]"

lemma source_prefix_lookup:
  assumes "n < m"
  shows "lookup (source_prefix G m) n = Some (G n)"
  using assms by (simp add: source_prefix_def lookup_def)

lemma source_language_in_prefix:
  assumes language: "sgterm_in_language L \<Sigma> G A \<tau>"
    and bound: "source_free_bound A \<le> m"
  shows "sterm_in_language L \<Sigma> (source_prefix G m) A \<tau>"
proof -
  have global: "has_sgtype L G A \<tau>" and names: "sterm_in_signature \<Sigma> A"
    using language unfolding sgterm_in_language_def by blast+
  have finite_type: "has_stype L (source_prefix G m) A \<tau>"
  proof (rule source_global_to_finite_typing[OF global])
    fix n
    assume member: "n \<in> sfv A"
    have smaller: "n < source_free_bound A" by (rule source_free_bound_covers[OF member])
    have below: "n < m" by (rule less_le_trans[OF smaller bound])
    show "lookup (source_prefix G m) n = Some (G n)" by (rule source_prefix_lookup[OF below])
  qed
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF finite_type names])
qed

section \<open>Translation in every sufficiently large finite prefix\<close>

text \<open>
  A translated proof has a finite variable-support bound. Increasing the
  prefix beyond that bound preserves the same translated conclusion.
  This is the induction invariant for whole source proofs, not the final
  correspondence theorem. It does not remove unused variables or assert
  reverse proof translation.
\<close>

definition paper_target_eventual :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_target_eventual \<Sigma> G A \<longleftrightarrow>
    (\<exists>N. \<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A))"

lemma paper_target_eventual_from_axiom:
  assumes language: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and axiom: "\<And>\<Gamma>. sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<Longrightarrow>
      pH_proves \<Sigma> \<Gamma> (paper_to_pterm A)"
  shows "paper_target_eventual \<Sigma> G A"
  unfolding paper_target_eventual_def
proof (rule exI[where x="source_free_bound A"], intro allI impI)
  fix m
  assume bound: "source_free_bound A \<le> m"
  show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    by (rule axiom[OF source_language_in_prefix[OF language bound]])
qed

lemma paper_target_eventual_PC:
  assumes pc: "paper_global_PC \<Sigma> G A"
  shows "paper_target_eventual \<Sigma> G A"
  unfolding paper_target_eventual_def
proof (rule exI[where x="source_free_bound A"], intro allI impI)
  fix m
  assume bound: "source_free_bound A \<le> m"
  show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
  proof (rule paper_global_PC_translation[OF pc])
    fix n
    assume member: "n \<in> sfv A"
    have below: "n < m" by (rule less_le_trans[OF source_free_bound_covers[OF member] bound])
    show "lookup (source_prefix G m) n = Some (G n)" by (rule source_prefix_lookup[OF below])
  qed
qed

lemma paper_target_implication_languages:
  assumes proved: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp A B))"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
proof -
  have source: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop"
    by (rule iffD1[OF paper_to_pterm_language_iff pH_proves_in_language[OF proved]])
  show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source by (auto simp: sterm_in_language_def paper_imp_type_iff)
qed

lemma paper_target_eventual_MP:
  assumes first: "paper_target_eventual \<Sigma> G A"
    and second: "paper_target_eventual \<Sigma> G (paper_imp A B)"
  shows "paper_target_eventual \<Sigma> G B"
proof -
  obtain N where a: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    using first unfolding paper_target_eventual_def by (elim exE)
  obtain K where ab: "\<forall>m\<ge>K. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_imp A B))"
    using second unfolding paper_target_eventual_def by (elim exE)
  show ?thesis unfolding paper_target_eventual_def
  proof (rule exI[where x="max N K"], intro allI impI)
    fix m
    assume bound: "max N K \<le> m"
    have left: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)" using a bound by auto
    have right: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm (paper_imp A B))" using ab bound by auto
    show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm B)"
      by (rule paper_MP_translation[OF paper_target_implication_languages(1)[OF right]
        paper_target_implication_languages(2)[OF right] left right])
  qed
qed

end
