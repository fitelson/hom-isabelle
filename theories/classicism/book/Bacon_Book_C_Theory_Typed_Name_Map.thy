theory Bacon_Book_C_Theory_Typed_Name_Map
  imports Bacon_Book_C_Typed_Name_Map Bacon_Book_Classicism_Theory_Rules
begin

section \<open>Type-indexed transport of C with additional assumptions\<close>

theorem book_C_theory_typed_name_map:
  assumes rich: "sg_rich G" and derivation: "book_C_theory_derivable \<Sigma> G S A"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "book_C_theory_derivable \<Omega> G (book_typed_name_map \<rho> ` S) (book_typed_name_map \<rho> A)"
proof -
  let ?C = "{B. book_C_proves \<Sigma> G B}"
  let ?D = "{B. book_C_proves \<Omega> G B}"
  have base: "book_theory_derivable \<Sigma> G (?C \<union> S) A"
    using derivation unfolding book_C_theory_derivable_def .
  have mapped: "book_theory_derivable \<Omega> G (book_typed_name_map \<rho> ` (?C \<union> S)) (book_typed_name_map \<rho> A)"
    by (rule book_theory_typed_name_map[OF base maps])
  show ?thesis unfolding book_C_theory_derivable_def
  proof (rule book_theory_derivable_cut[OF mapped])
    fix Q
    assume member: "Q \<in> book_typed_name_map \<rho> ` (?C \<union> S)"
    obtain B where original: "B \<in> ?C \<union> S" and shape: "Q = book_typed_name_map \<rho> B" using member by blast
    show "book_theory_derivable \<Omega> G (?D \<union> book_typed_name_map \<rho> ` S) Q"
    proof (cases "book_C_proves \<Sigma> G B")
      case True
      have target_C: "book_C_proves \<Omega> G (book_typed_name_map \<rho> B)" by (rule book_C_typed_name_map[OF rich True maps])
      have target_type: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> B)" by (rule book_C_proves_language[OF rich target_C])
      have target_member: "book_typed_name_map \<rho> B \<in> ?D \<union> book_typed_name_map \<rho> ` S"
        by (rule UnI1; simp only: mem_Collect_eq; rule target_C)
      show ?thesis by (simp only: shape; rule book_theory_derivable.Assumption[OF target_member target_type])
    next
      case False
      have in_S: "B \<in> S" using original False by simp
      have target_type: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> B)"
        by (rule book_typed_name_map_language[OF language[OF in_S] maps])
      have target_member: "book_typed_name_map \<rho> B \<in> book_typed_name_map \<rho> ` S" by (rule imageI[OF in_S])
      show ?thesis by (simp only: shape; rule book_theory_derivable.Assumption[OF UnI2[OF target_member] target_type])
    qed
  qed
qed


end

