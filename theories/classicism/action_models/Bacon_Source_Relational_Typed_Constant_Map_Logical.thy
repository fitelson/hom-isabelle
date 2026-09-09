theory Bacon_Source_Relational_Typed_Constant_Map_Logical
  imports Bacon_Source_Relational_Typed_Constant_Map_Conversion
    Bacon_Source_Relational_H
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Vectors
begin

section \<open>Literal logical operators and prefixes under typed name transport\<close>

lemma paper_R_typed_constant_map_primitive:
  "paper_R_typed_constant_map \<rho> (named_paper_not A) = named_paper_not (paper_R_typed_constant_map \<rho> A)"
  "paper_R_typed_constant_map \<rho> (named_paper_and A B) =
    named_paper_and (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  "paper_R_typed_constant_map \<rho> (named_paper_or A B) =
    named_paper_or (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  "paper_R_typed_constant_map \<rho> (named_paper_eq \<sigma> A B) =
    named_paper_eq \<sigma> (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  "paper_R_typed_constant_map \<rho> (named_paper_all \<sigma> A) = named_paper_all \<sigma> (paper_R_typed_constant_map \<rho> A)"
  "paper_R_typed_constant_map \<rho> (named_paper_ex \<sigma> A) = named_paper_ex \<sigma> (paper_R_typed_constant_map \<rho> A)"
  by (simp_all only: named_paper_not_def named_paper_and_def named_paper_or_def
    named_paper_eq_def named_paper_all_def named_paper_ex_def paper_R_typed_constant_map.simps)

lemma paper_R_typed_constant_map_defined_heads:
  "paper_R_typed_constant_map \<rho> (named_paper_imp_const G) = named_paper_imp_const G"
  "paper_R_typed_constant_map \<rho> (named_paper_iff_const G) = named_paper_iff_const G"
  by (simp_all only: named_paper_imp_const_def named_paper_iff_const_def
    paper_R_typed_constant_map_primitive paper_R_typed_constant_map.simps)

lemma paper_R_typed_constant_map_imp:
  "paper_R_typed_constant_map \<rho> (named_paper_imp G A B) =
    named_paper_imp G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  by (simp only: named_paper_imp_def paper_R_typed_constant_map.simps paper_R_typed_constant_map_defined_heads)

lemma paper_R_typed_constant_map_iff:
  "paper_R_typed_constant_map \<rho> (named_paper_iff G A B) =
    named_paper_iff G (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  by (simp only: named_paper_iff_def paper_R_typed_constant_map.simps paper_R_typed_constant_map_defined_heads)

lemma paper_R_typed_constant_map_lam_vec:
  "paper_R_typed_constant_map \<rho> (named_lam_vec ns A) = named_lam_vec ns (paper_R_typed_constant_map \<rho> A)"
  by (induction ns) simp_all

lemma paper_R_typed_constant_map_prop_instance:
  "paper_R_typed_constant_map \<rho> (named_paper_prop_instance G v P) =
    named_paper_prop_instance G (\<lambda>a. paper_R_typed_constant_map \<rho> (v a)) P"
  by (induction P) (simp_all only: named_paper_prop_instance.simps
    paper_R_typed_constant_map_primitive paper_R_typed_constant_map_imp paper_R_typed_constant_map_iff)

lemma paper_R_typed_constant_map_PC:
  assumes pc: "paper_R_named_PC \<Sigma> G A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "paper_R_named_PC \<Omega> G (paper_R_typed_constant_map \<rho> A)"
proof -
  have language: "paper_R_in_language \<Omega> G (paper_R_typed_constant_map \<rho> A) Prop"
    by (rule paper_R_typed_constant_map_language[OF paper_R_named_PC_language[OF pc] maps])
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and shape: "A = named_paper_prop_instance G v P"
    using pc unfolding paper_R_named_PC_def by blast
  have instance_eq: "paper_R_typed_constant_map \<rho> A =
      named_paper_prop_instance G (\<lambda>a. paper_R_typed_constant_map \<rho> (v a)) P"
    by (simp only: shape paper_R_typed_constant_map_prop_instance)
  show ?thesis unfolding paper_R_named_PC_def
    by (rule conjI[OF language], rule exI[where x=P],
      rule exI[where x="\<lambda>a. paper_R_typed_constant_map \<rho> (v a)"],
      rule conjI[OF taut instance_eq])
qed

text \<open>
  The logical alphabet, the literal λ-defined → and ↔ operators,
  and every abstraction binder remain fixed. PC retains its original
  Boolean template, with typing only for the whole occurring instance.
  No condition is placed on unused atom assignments.
  Source: Figures 1–2 and the native Logical Equivalence schema.
\<close>

end
