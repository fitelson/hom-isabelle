theory Bacon_Source_Relational_Constant_Map_Logical
  imports Bacon_Source_Relational_Constant_Map_Binding Bacon_Source_Relational_H
begin

section \<open>The logical alphabet and literal abbreviations are fixed\<close>

lemma paper_R_constant_map_primitive:
  "paper_R_constant_map f (named_paper_not A) = named_paper_not (paper_R_constant_map f A)"
  "paper_R_constant_map f (named_paper_and A B) = named_paper_and (paper_R_constant_map f A) (paper_R_constant_map f B)"
  "paper_R_constant_map f (named_paper_or A B) = named_paper_or (paper_R_constant_map f A) (paper_R_constant_map f B)"
  "paper_R_constant_map f (named_paper_eq \<sigma> A B) = named_paper_eq \<sigma> (paper_R_constant_map f A) (paper_R_constant_map f B)"
  "paper_R_constant_map f (named_paper_all \<sigma> A) = named_paper_all \<sigma> (paper_R_constant_map f A)"
  "paper_R_constant_map f (named_paper_ex \<sigma> A) = named_paper_ex \<sigma> (paper_R_constant_map f A)"
  by (simp_all only: named_paper_not_def named_paper_and_def named_paper_or_def
    named_paper_eq_def named_paper_all_def named_paper_ex_def paper_R_constant_map_simps)

lemma paper_R_constant_map_defined_heads:
  "paper_R_constant_map f (named_paper_imp_const G) = named_paper_imp_const G"
  "paper_R_constant_map f (named_paper_iff_const G) = named_paper_iff_const G"
  by (simp_all only: named_paper_imp_const_def named_paper_iff_const_def
    paper_R_constant_map_primitive paper_R_constant_map_simps)

lemma paper_R_constant_map_imp:
  "paper_R_constant_map f (named_paper_imp G A B) = named_paper_imp G (paper_R_constant_map f A) (paper_R_constant_map f B)"
  by (simp only: named_paper_imp_def paper_R_constant_map_simps paper_R_constant_map_defined_heads)

lemma paper_R_constant_map_iff:
  "paper_R_constant_map f (named_paper_iff G A B) = named_paper_iff G (paper_R_constant_map f A) (paper_R_constant_map f B)"
  by (simp only: named_paper_iff_def paper_R_constant_map_simps paper_R_constant_map_defined_heads)

lemma paper_R_constant_map_prop_instance:
  "paper_R_constant_map f (named_paper_prop_instance G v P) =
    named_paper_prop_instance G (\<lambda>a. paper_R_constant_map f (v a)) P"
  by (induction P) (simp_all only: named_paper_prop_instance.simps
    paper_R_constant_map_primitive paper_R_constant_map_imp paper_R_constant_map_iff)

text \<open>
  PC retains the identical Boolean template. Only the instantiated whole
  formula is required to be R-typed, as in Figure 2; unused atom values
  acquire no extra language condition. The literal → and ↔ heads keep
  their bound names because G is unchanged.
\<close>

lemma paper_R_constant_map_PC:
  assumes pc: "paper_R_named_PC \<Sigma> G A"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "paper_R_named_PC \<Omega> G (paper_R_constant_map f A)"
proof -
  have language: "paper_R_in_language \<Omega> G (paper_R_constant_map f A) Prop"
    by (rule paper_R_constant_map_language[OF paper_R_named_PC_language[OF pc] maps])
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and shape: "A = named_paper_prop_instance G v P"
    using pc unfolding paper_R_named_PC_def by blast
  have instance_eq: "paper_R_constant_map f A = named_paper_prop_instance G (\<lambda>a. paper_R_constant_map f (v a)) P"
    by (simp only: shape paper_R_constant_map_prop_instance)
  show ?thesis unfolding paper_R_named_PC_def
    by (rule conjI[OF language], rule exI[where x=P], rule exI[where x="\<lambda>a. paper_R_constant_map f (v a)"],
      rule conjI[OF taut instance_eq])
qed

end
