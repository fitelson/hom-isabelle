theory Bacon_Source_Relational_Local_Constant_Map
  imports Bacon_Source_Relational_H_Constant_Map Bacon_Source_Relational_Local_Consequence
begin

section \<open>Local consequence transports both premises and conclusion\<close>

text \<open>
  The variable stock and logical vocabulary are unchanged. Every used
  assumption carries its original R-language guard, which the constant
  map preserves. Unused elements of S need no extra language condition.
  Source role: the original-name embedding in Theorem 3.2, p.45 n.64.
  No injection, richness, model or F proof is required for this direction.
\<close>

theorem paper_R_named_derivable_constant_map:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "paper_R_named_derivable \<Omega> G (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
  using derivation
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  have member: "paper_R_constant_map f A \<in> image (paper_R_constant_map f) S" by (rule imageI[OF Assumption.hyps(1)])
  have language: "paper_R_in_language \<Omega> G (paper_R_constant_map f A) Prop"
    by (rule paper_R_constant_map_language[OF Assumption.hyps(2) maps])
  show ?case by (rule paper_R_named_derivable.Assumption[OF member language])
next
  case (Theorem A S)
  show ?case by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_constant_map[OF Theorem.hyps maps]])
next
  case (MP S A B)
  have implication: "paper_R_named_derivable \<Omega> G (image (paper_R_constant_map f) S)
    (named_paper_imp G (paper_R_constant_map f A) (paper_R_constant_map f B))"
    using MP.IH(2) by (simp only: paper_R_constant_map_imp)
  show ?case by (rule paper_R_named_derivable.MP[OF MP.IH(1) implication paper_R_constant_map_language[OF MP.hyps(3) maps]])
qed

corollary paper_R_named_derivable_constant_map_image:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A"
  shows "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
    (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
  by (rule paper_R_named_derivable_constant_map[OF derivation]; rule imageI; assumption)

section \<open>A left inverse restores every raw premise and conclusion\<close>

lemma paper_R_constant_map_left_inverse:
  assumes inverse: "\<And>c. \<pi> (f c) = c"
  shows "paper_R_constant_map \<pi> (paper_R_constant_map f A) = A"
proof -
  have identity: "\<pi> \<circ> f = id" by (rule ext; simp add: inverse)
  show ?thesis by (simp only: paper_R_constant_map_comp identity paper_R_constant_map_id)
qed

lemma paper_R_constant_map_left_inverse_image:
  assumes inverse: "\<And>c. \<pi> (f c) = c"
  shows "image (paper_R_constant_map \<pi>) (image (paper_R_constant_map f) S) = S"
  by (simp add: image_image paper_R_constant_map_left_inverse[where \<pi>=\<pi> and f=f, OF inverse])

lemma paper_R_constant_map_inverse_names:
  assumes inverse: "\<And>c. \<pi> (f c) = c" and member: "d \<in> image f (\<Sigma> \<rho>)"
  shows "\<pi> d \<in> \<Sigma> \<rho>"
proof -
  obtain c where declared: "c \<in> \<Sigma> \<rho>" and shape: "d = f c" using member by blast
  show ?thesis by (simp only: shape inverse; rule declared)
qed

theorem paper_R_named_derivable_constant_map_iff:
  assumes inverse: "\<And>c. \<pi> (f c) = c"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow>
    paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
proof
  assume original: "paper_R_named_derivable \<Sigma> G S A"
  show "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
    by (rule paper_R_named_derivable_constant_map_image[OF original])
next
  assume mapped: "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
  have maps: "\<pi> d \<in> \<Sigma> \<rho>" if "d \<in> image f (\<Sigma> \<rho>)" for \<rho> d
    by (rule paper_R_constant_map_inverse_names[where \<pi>=\<pi> and f=f and \<Sigma>=\<Sigma> and \<rho>=\<rho> and d=d, OF inverse that])
  have restored: "paper_R_named_derivable \<Sigma> G
      (image (paper_R_constant_map \<pi>) (image (paper_R_constant_map f) S))
      (paper_R_constant_map \<pi> (paper_R_constant_map f A))"
    by (rule paper_R_named_derivable_constant_map[where f=\<pi> and \<Sigma>="\<lambda>\<rho>. image f (\<Sigma> \<rho>)"
      and \<Omega>=\<Sigma> and G=G and S="image (paper_R_constant_map f) S" and A="paper_R_constant_map f A", OF mapped maps])
  show "paper_R_named_derivable \<Sigma> G S A" using restored
    by (simp only: paper_R_constant_map_left_inverse_image[where \<pi>=\<pi> and f=f, OF inverse]
      paper_R_constant_map_left_inverse[where \<pi>=\<pi> and f=f, OF inverse])
qed

corollary paper_R_named_derivable_injective_constant_map_iff:
  assumes injective: "inj f"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow>
    paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
  by (rule paper_R_named_derivable_constant_map_iff[where \<pi>="inv f" and f=f]; rule inv_f_f[OF injective])

end
