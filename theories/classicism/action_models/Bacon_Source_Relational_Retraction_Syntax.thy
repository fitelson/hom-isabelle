theory Bacon_Source_Relational_Retraction_Syntax
  imports Bacon_Source_Relational_H Bacon_Source_Relational_Signature_Conversion
begin

section \<open>Retraction retains the literal logical vocabulary\<close>

text \<open>
  Foreign-constant retraction leaves every variable, binder and logical
  symbol unchanged. In particular it fixes the literal constant-free
  λ heads defining → and ↔, without an α conversion or a richness
  premise. Source: Figure 1, p.6, and Figure 2, p.8.
\<close>

lemma paper_R_retract_from_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
  shows "paper_R_in_language \<Omega> G (named_retract \<Omega> v A) \<tau>"
proof -
  have typed: "paper_R_has_type G A \<tau>" using language unfolding paper_R_in_language_def by blast
  show ?thesis by (rule paper_R_retract_language[OF typed stock])
qed

lemma paper_R_retract_primitive:
  "named_retract \<Omega> v (named_paper_not A) = named_paper_not (named_retract \<Omega> v A)"
  "named_retract \<Omega> v (named_paper_and A B) = named_paper_and (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  "named_retract \<Omega> v (named_paper_or A B) = named_paper_or (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  "named_retract \<Omega> v (named_paper_eq \<sigma> A B) = named_paper_eq \<sigma> (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  "named_retract \<Omega> v (named_paper_all \<sigma> A) = named_paper_all \<sigma> (named_retract \<Omega> v A)"
  "named_retract \<Omega> v (named_paper_ex \<sigma> A) = named_paper_ex \<sigma> (named_retract \<Omega> v A)"
  by (simp_all only: named_paper_not_def named_paper_and_def named_paper_or_def
    named_paper_eq_def named_paper_all_def named_paper_ex_def named_retract.simps)

lemma paper_R_retract_defined_heads:
  "named_retract \<Omega> v (named_paper_imp_const G) = named_paper_imp_const G"
  "named_retract \<Omega> v (named_paper_iff_const G) = named_paper_iff_const G"
  by (simp_all only: named_paper_imp_const_def named_paper_iff_const_def
    paper_R_retract_primitive named_retract.simps)

lemma paper_R_retract_imp:
  "named_retract \<Omega> v (named_paper_imp G A B) = named_paper_imp G (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  by (simp only: named_paper_imp_def named_retract.simps paper_R_retract_defined_heads)

lemma paper_R_retract_iff:
  "named_retract \<Omega> v (named_paper_iff G A B) = named_paper_iff G (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  by (simp only: named_paper_iff_def named_retract.simps paper_R_retract_defined_heads)

lemma paper_R_retract_prop_instance:
  "named_retract \<Omega> v (named_paper_prop_instance G w P) =
    named_paper_prop_instance G (\<lambda>a. named_retract \<Omega> v (w a)) P"
  by (induction P) (simp_all only: named_paper_prop_instance.simps
    paper_R_retract_primitive paper_R_retract_imp paper_R_retract_iff)

lemma paper_R_retract_PC:
  assumes pc: "paper_R_named_PC \<Sigma> G A"
    and stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
  shows "paper_R_named_PC \<Omega> G (named_retract \<Omega> v A)"
proof -
  have language: "paper_R_in_language \<Omega> G (named_retract \<Omega> v A) Prop"
    by (rule paper_R_retract_from_language[OF paper_R_named_PC_language[OF pc] stock])
  obtain P :: "nat sprop_template" and w where taut: "sprop_tautology P"
    and shape: "A = named_paper_prop_instance G w P"
    using pc unfolding paper_R_named_PC_def by blast
  have instance_eq: "named_retract \<Omega> v A = named_paper_prop_instance G (\<lambda>a. named_retract \<Omega> v (w a)) P"
    by (simp only: shape paper_R_retract_prop_instance)
  show ?thesis unfolding paper_R_named_PC_def
    by (rule conjI[OF language], rule exI[where x=P], rule exI[where x="\<lambda>a. named_retract \<Omega> v (w a)"],
      rule conjI[OF taut instance_eq])
qed

end
