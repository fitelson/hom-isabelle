theory Bacon_Source_Relational_Constant_Map_Consistency
  imports Bacon_Source_Relational_Local_Constant_Map Bacon_Source_Relational_Consistency
begin

section \<open>Exact-image consistency under an injective carrier embedding\<close>

text \<open>
  A target contradiction need not be an encoded old formula. Map BOTH
  target proofs through the left inverse π, obtaining π(A) and ¬π(A).
  The exact image signature ensures that every declared target constant
  returns to its original type-indexed signature. The premise set is
  restored exactly, even if it has unused malformed entries.

  Source role: initial consistency of the original-name image before
  witness formation in Theorem 3.2, p.45 n.64. No richness, F consistency,
  model or witness premise occurs. Proof reflection and the consistency
  equivalence require the left inverse and the exact image signature.
  The one-way consistency reflection needs no injection, since forward
  proof transport already sends any old contradiction to a new one.
\<close>

theorem paper_R_named_consistent_constant_map_preserve:
  assumes inverse: "\<And>c. \<pi> (f c) = c" and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "paper_R_named_consistent (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (image (paper_R_constant_map f) S)"
proof (rule paper_R_named_consistentI)
  fix A
  assume positive: "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (image (paper_R_constant_map f) S) A"
    and negative: "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (named_paper_not A)"
  have maps: "\<pi> d \<in> \<Sigma> \<rho>" if "d \<in> image f (\<Sigma> \<rho>)" for \<rho> d
    by (rule paper_R_constant_map_inverse_names[where \<pi>=\<pi> and f=f and \<Sigma>=\<Sigma> and \<rho>=\<rho> and d=d, OF inverse that])
  have positive_back: "paper_R_named_derivable \<Sigma> G S (paper_R_constant_map \<pi> A)"
    using paper_R_named_derivable_constant_map[where f=\<pi> and \<Sigma>="\<lambda>\<rho>. image f (\<Sigma> \<rho>)"
      and \<Omega>=\<Sigma> and G=G and S="image (paper_R_constant_map f) S" and A=A, OF positive maps]
    by (simp only: paper_R_constant_map_left_inverse_image[where \<pi>=\<pi> and f=f, OF inverse])
  have negative_back: "paper_R_named_derivable \<Sigma> G S (named_paper_not (paper_R_constant_map \<pi> A))"
    using paper_R_named_derivable_constant_map[where f=\<pi> and \<Sigma>="\<lambda>\<rho>. image f (\<Sigma> \<rho>)"
      and \<Omega>=\<Sigma> and G=G and S="image (paper_R_constant_map f) S" and A="named_paper_not A", OF negative maps]
    by (simp only: paper_R_constant_map_left_inverse_image[where \<pi>=\<pi> and f=f, OF inverse] paper_R_constant_map_primitive)
  show False by (rule paper_R_named_consistentD[OF consistent positive_back negative_back])
qed

lemma paper_R_named_consistent_constant_map_reflect:
  assumes consistent: "paper_R_named_consistent (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (image (paper_R_constant_map f) S)"
  shows "paper_R_named_consistent \<Sigma> G S"
proof (rule paper_R_named_consistentI)
  fix A
  assume positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
  have mapped_positive: "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (paper_R_constant_map f A)"
    by (rule paper_R_named_derivable_constant_map_image[where f=f, OF positive])
  have mapped_negative: "paper_R_named_derivable (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G
      (image (paper_R_constant_map f) S) (named_paper_not (paper_R_constant_map f A))"
    using paper_R_named_derivable_constant_map_image[where f=f, OF negative] by (simp only: paper_R_constant_map_primitive)
  show False by (rule paper_R_named_consistentD[OF consistent mapped_positive mapped_negative])
qed

theorem paper_R_named_consistent_constant_map_iff:
  assumes inverse: "\<And>c. \<pi> (f c) = c"
  shows "paper_R_named_consistent \<Sigma> G S \<longleftrightarrow>
    paper_R_named_consistent (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (image (paper_R_constant_map f) S)"
  using paper_R_named_consistent_constant_map_preserve[where \<pi>=\<pi> and f=f and \<Sigma>=\<Sigma> and G=G and S=S, OF inverse]
    paper_R_named_consistent_constant_map_reflect[where f=f and \<Sigma>=\<Sigma> and G=G and S=S] by blast

corollary paper_R_named_consistent_injective_constant_map_iff:
  assumes injective: "inj f"
  shows "paper_R_named_consistent \<Sigma> G S \<longleftrightarrow>
    paper_R_named_consistent (\<lambda>\<rho>. image f (\<Sigma> \<rho>)) G (image (paper_R_constant_map f) S)"
  by (rule paper_R_named_consistent_constant_map_iff[where \<pi>="inv f" and f=f]; rule inv_f_f[OF injective])

end
