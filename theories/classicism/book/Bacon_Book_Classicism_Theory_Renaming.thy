theory Bacon_Book_Classicism_Theory_Renaming
  imports Bacon_Book_Classicism_Constant_Renaming Bacon_Book_Classicism_Theory_Rules
    Bacon_Book_Environment_Development.Bacon_Book_Constant_Renaming_Reflection
begin

section \<open>Transport the complete C background as well as the assumptions\<close>

theorem book_C_theory_constant_rename:
  assumes rich: "sg_rich G" and derivation: "book_C_theory_derivable \<Sigma> G S A"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_C_theory_derivable \<Omega> G (book_constant_rename f ` S) (book_constant_rename f A)"
proof -
  let ?C = "{B. book_C_proves \<Sigma> G B}"
  let ?D = "{B. book_C_proves \<Omega> G B}"
  have base: "book_theory_derivable \<Sigma> G (?C \<union> S) A"
    using derivation unfolding book_C_theory_derivable_def .
  have mapped: "book_theory_derivable \<Omega> G (book_constant_rename f ` (?C \<union> S)) (book_constant_rename f A)"
    by (rule book_theory_constant_rename[OF base maps])
  show ?thesis unfolding book_C_theory_derivable_def
  proof (rule book_theory_derivable_cut[OF mapped])
    fix Q
    assume member: "Q \<in> book_constant_rename f ` (?C \<union> S)"
    obtain B where original: "B \<in> ?C \<union> S" and shape: "Q = book_constant_rename f B" using member by blast
    show "book_theory_derivable \<Omega> G (?D \<union> book_constant_rename f ` S) Q"
    proof (cases "book_C_proves \<Sigma> G B")
      case True
      have target_C: "book_C_proves \<Omega> G (book_constant_rename f B)" by (rule book_C_constant_rename[OF rich True maps])
      have target_type: "book_theory_formula \<Omega> G (book_constant_rename f B)" by (rule book_C_proves_language[OF rich target_C])
      have target_member: "book_constant_rename f B \<in> ?D \<union> book_constant_rename f ` S"
        by (rule UnI1; simp only: mem_Collect_eq; rule target_C)
      show ?thesis by (simp only: shape; rule book_theory_derivable.Assumption[OF target_member target_type])
    next
      case False
      have in_S: "B \<in> S" using original False by simp
      have target_type: "book_theory_formula \<Omega> G (book_constant_rename f B)"
        by (rule book_constant_rename_language[OF language[OF in_S] maps])
      have target_member: "book_constant_rename f B \<in> book_constant_rename f ` S" by (rule imageI[OF in_S])
      show ?thesis by (simp only: shape; rule book_theory_derivable.Assumption[OF UnI2[OF target_member] target_type])
    qed
  qed
qed

theorem book_C_theory_constant_rename_iff:
  assumes rich: "sg_rich G" and injective: "inj f"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_C_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_C_theory_derivable (\<lambda>\<tau>. f ` \<Sigma> \<tau>) G (book_constant_rename f ` S) (book_constant_rename f A)"
proof
  assume derivation: "book_C_theory_derivable \<Sigma> G S A"
  have maps: "f c \<in> (\<lambda>\<tau>. f ` \<Sigma> \<tau>) \<tau>" if "c \<in> \<Sigma> \<tau>" for \<tau> c
    by (rule imageI[OF that])
  show "book_C_theory_derivable (\<lambda>\<tau>. f ` \<Sigma> \<tau>) G (book_constant_rename f ` S) (book_constant_rename f A)"
    by (rule book_C_theory_constant_rename[where f=f and \<Omega>="\<lambda>\<tau>. f ` \<Sigma> \<tau>", OF rich derivation language maps])
next
  let ?\<Omega> = "\<lambda>\<tau>. f ` \<Sigma> \<tau>"
  assume derivation: "book_C_theory_derivable ?\<Omega> G (book_constant_rename f ` S) (book_constant_rename f A)"
  have inverse_maps: "inv f d \<in> \<Sigma> \<tau>" if "d \<in> ?\<Omega> \<tau>" for \<tau> d
  proof -
    have in_image: "d \<in> ?\<Omega> \<tau>" by (rule that)
    obtain c where member: "c \<in> \<Sigma> \<tau>" and shape: "d = f c" using in_image by blast
    show ?thesis by (simp only: shape inv_f_f[OF injective]; rule member)
  qed
  have mapped_language: "book_theory_formula ?\<Omega> G B" if "B \<in> book_constant_rename f ` S" for B
  proof -
    have in_image: "B \<in> book_constant_rename f ` S" by (rule that)
    obtain A where member: "A \<in> S" and shape: "B = book_constant_rename f A" using in_image by blast
    show ?thesis by (simp only: shape; rule book_constant_rename_image_language[OF language[OF member]])
  qed
  have restored: "book_C_theory_derivable \<Sigma> G
      (book_constant_rename (inv f) ` (book_constant_rename f ` S))
      (book_constant_rename (inv f) (book_constant_rename f A))"
    by (rule book_C_theory_constant_rename[OF rich derivation mapped_language inverse_maps])
  show "book_C_theory_derivable \<Sigma> G S A"
    using restored by (simp only: book_constant_rename_inverse_image[OF injective] book_constant_rename_inverse[OF injective])
qed

theorem book_C_consistent_constant_rename_iff:
  assumes rich: "sg_rich G" and injective: "inj f"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_C_theory_consistent (\<lambda>\<tau>. f ` \<Sigma> \<tau>) G (book_constant_rename f ` S)"
proof -
  have equivalence: "book_C_theory_derivable \<Sigma> G S (book_bottom G) \<longleftrightarrow>
    book_C_theory_derivable (\<lambda>\<tau>. f ` \<Sigma> \<tau>) G (book_constant_rename f ` S) (book_constant_rename f (book_bottom G))"
    by (rule book_C_theory_constant_rename_iff[OF rich injective language])
  show ?thesis using equivalence by (simp only: book_C_theory_consistent_def book_constant_rename_bottom)
qed

text \<open>
  Forward transport renames every used C theorem into a theorem of
  the target C, then cuts the renamed H proof into that background.
  Reflection uses an inverse only on the exact image signature.
  Injectivity is explicit, and no reflection from a noninjective map
  or a larger signature is asserted. These are proof/consistency
  transports between actual name carriers, not model assumptions.
\<close>

end
