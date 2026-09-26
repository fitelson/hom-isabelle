theory Bacon_Book_Lambda_I_Infinite_Witness_Family
  imports Bacon_Book_Lambda_I_Finite_Witness_Family Bacon_Book_Lambda_I_Finite_Image_Cover
begin

section \<open>Arbitrary families of fresh conditional witness premises\<close>

text \<open>
  Let every Fᵢ:τᵢ→t be a closed λI predicate of the OLD signature Σ and
  every premise a λI formula of Σ. If the names cᵢ are injective on I and
  fresh at their indicated types, λI consistency of S implies λI
  consistency of S∪W[I] in Σ[I].
  The index set I may have arbitrary cardinality. Source role: the
  finite-proof support argument in Bacon, Proposition 15.4, p.319,
  without an enumeration of predicates or constants.

  Each finite premise set is covered by S and finitely many witness
  indices J⊆I. The finite-family theorem first gives consistency in
  Σ[J]. All those premises belong to Σ[J], so foreign-constant
  elimination transfers consistency to Σ[I]; passing to a subset
  then handles the chosen finite premise set.

  This is syntactic finite-support reasoning, not semantic compactness.
  It assumes the displayed supply of distinct fresh names; it does not
  construct that supply or assert witness completeness/model existence.
  Predicates involving the newly added names are not covered by the
  OLD-signature hypothesis. S itself may be open and infinite.
\<close>

theorem book_lambda_I_consistent_witness_family:
  assumes rich: "sg_rich G"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and lambda_I: "\<And>i. i \<in> I \<Longrightarrow> book_lambda_I (F i)"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Sigma> (\<tau> i)"
    and injective: "inj_on c I"
  shows "book_lambda_I_consistent (book_witness_family_signature \<Sigma> \<tau> c I) G
    (S \<union> book_witness_family_axioms G \<tau> F c I)"
proof (rule iffD2[OF book_lambda_I_consistent_finite_iff])
  let ?full = "book_witness_family_signature \<Sigma> \<tau> c I"
  let ?W = "\<lambda>i. book_witness_axiom G (\<tau> i) (F i) (c i)"
  show "\<forall>B. finite B \<longrightarrow> B \<subseteq> S \<union> book_witness_family_axioms G \<tau> F c I
    \<longrightarrow> book_lambda_I_consistent ?full G B"
  proof (intro allI impI)
    fix B
    assume finite_B: "finite B"
      and covered: "B \<subseteq> S \<union> book_witness_family_axioms G \<tau> F c I"
    have image_cover: "B \<subseteq> S \<union> image ?W I"
      using covered by (simp only: book_witness_family_axioms_def)
    obtain J where finite_J: "finite J" and subset_J: "J \<subseteq> I"
      and covered_J: "B \<subseteq> S \<union> image ?W J"
      using book_lambda_I_finite_image_cover[OF finite_B image_cover] by blast
    let ?partial = "book_witness_family_signature \<Sigma> \<tau> c J"
    let ?premises = "S \<union> book_witness_family_axioms G \<tau> F c J"
    have predicates_J: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F j) (Arr (\<tau> j) Prop)"
      if "j \<in> J" for j
      by (rule predicates[OF subsetD[OF subset_J that]])
    have closed_J: "named_fv (F j) = {}" if "j \<in> J" for j
      by (rule closed[OF subsetD[OF subset_J that]])
    have fresh_J: "c j \<notin> \<Sigma> (\<tau> j)" if "j \<in> J" for j
      by (rule fresh[OF subsetD[OF subset_J that]])
    have lambda_I_J: "book_lambda_I (F j)" if "j \<in> J" for j
      by (rule lambda_I[OF subsetD[OF subset_J that]])
    have injective_J: "inj_on c J" by (rule inj_on_subset[OF injective subset_J])
    have partial_consistent: "book_lambda_I_consistent ?partial G ?premises"
      by (rule book_lambda_I_consistent_finite_witness_family[where \<Sigma>=\<Sigma> and G=G
        and S=S and \<tau>=\<tau> and F=F and c=c and I=J, OF finite_J rich consistent
        language predicates_J closed_J lambda_I_J fresh_J injective_J])
    have partial_names: "named_in_signature ?partial A" if "A \<in> ?premises" for A
    proof -
      have premise_member: "A \<in> ?premises" by (rule that)
      have premise_language: "book_lambda_I_formula ?partial G A"
        by (rule book_lambda_I_witness_family_premises_language[OF rich language predicates_J lambda_I_J premise_member])
      show "named_in_signature ?partial A" by (rule book_lambda_I_formula_signature[OF premise_language])
    qed
    have full_consistent: "book_lambda_I_consistent ?full G ?premises"
      by (rule book_lambda_I_consistent_signature_transport[OF rich partial_consistent partial_names])
    have selected_subset: "B \<subseteq> ?premises"
      using covered_J by (simp only: book_witness_family_axioms_def)
    show "book_lambda_I_consistent ?full G B"
      by (rule book_lambda_I_consistent_subset[OF full_consistent selected_subset])
  qed
qed

end
