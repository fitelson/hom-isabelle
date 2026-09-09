theory Bacon_Source_Relational_Henkin_Countable_Signature
  imports Bacon_Source_Relational_Henkin_Full_Signature Bacon_Source_Relational_Admitted_Terms_Countable
begin

section \<open>Each actual witness stage admits countably many names\<close>

text \<open>
  If the union of the declared original Σρ is countable, the same
  is true at each witness stage. At the successor stage, new names
  are an image of pairs (σ,F), where σ ranges over the countable
  object types and F over the admitted old-stage syntax. Closedness
  and R typing select a subset of that countable set of terms.

  The ambient original carrier 'c and the ambient recursive witness
  datatype are NOT assumed countable. Only their admitted subsets
  are counted. Source: the countable-language refinement of Theorem
  3.2, p.45 n.64. No consistency, Henkin theory or model is assumed.
\<close>

theorem paper_R_henkin_stage_names_countable:
  fixes \<Sigma> :: "'c ssignature"
  assumes names: "countable (\<Union>\<rho>. \<Sigma> \<rho>)"
  shows "countable (\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>)"
proof (induction k)
  case 0
  have equality: "(\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G 0 \<rho>) = image ROriginal (\<Union>\<rho>. \<Sigma> \<rho>)"
    by auto
  show ?case by (simp only: equality; rule countable_image[OF names])
next
  case (Suc k)
  let ?Old = "\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>"
  let ?Terms = "{F :: ('c paper_R_henkin_name) paper_named_term.
    named_in_signature (paper_R_henkin_signature \<Sigma> G k) F}"
  let ?New = "image (\<lambda>p. RWitness k (fst p) (snd p)) ((UNIV :: otype set) \<times> ?Terms)"
  have terms: "countable ?Terms" by (rule paper_R_admitted_terms_countable[OF Suc.IH])
  have pairs: "countable ((UNIV :: otype set) \<times> ?Terms)"
    by (rule countable_SIGMA[OF pHct_otypes_countable]; rule terms)
  have new_names: "countable ?New" by (rule countable_image[OF pairs])
  have bound: "countable (?Old \<union> ?New)" by (rule countable_Un[OF Suc.IH new_names])
  have subset: "(\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>) \<subseteq> ?Old \<union> ?New"
  proof
    fix c
    assume member: "c \<in> (\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>)"
    obtain \<rho> where declared: "c \<in> paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>" using member by blast
    show "c \<in> ?Old \<union> ?New"
    proof (cases "c \<in> paper_R_henkin_signature \<Sigma> G k \<rho>")
      case True
      then show ?thesis by blast
    next
      case False
      obtain F where shape: "c = RWitness k \<rho> F"
        and predicate: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<rho> Prop)"
        using declared False by auto
      have admitted: "F \<in> ?Terms" using predicate unfolding paper_R_in_language_def by blast
      have pair: "(\<rho>,F) \<in> (UNIV :: otype set) \<times> ?Terms" using admitted by simp
      have image_member: "(\<lambda>p. RWitness k (fst p) (snd p)) (\<rho>,F) \<in> ?New" by (rule imageI[OF pair])
      show ?thesis using image_member by (simp only: fst_conv snd_conv shape; blast)
    qed
  qed
  show ?case by (rule countable_subset[OF subset bound])
qed

section \<open>The full admitted signature is a countable union of countable stages\<close>

theorem paper_R_henkin_full_names_countable:
  assumes names: "countable (\<Union>\<rho>. \<Sigma> \<rho>)"
  shows "countable (\<Union>\<rho>. paper_R_henkin_full_signature \<Sigma> G \<rho>)"
proof -
  have levels: "countable (\<Union>k. \<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>)"
    by (rule countable_UN[OF countableI_type]; rule paper_R_henkin_stage_names_countable[OF names])
  have equality: "(\<Union>\<rho>. paper_R_henkin_full_signature \<Sigma> G \<rho>) =
      (\<Union>k. \<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>)"
    by (auto simp: paper_R_henkin_full_signature_def)
  show ?thesis by (simp only: equality; rule levels)
qed

corollary paper_R_henkin_full_admitted_terms_countable:
  assumes names: "countable (\<Union>\<rho>. \<Sigma> \<rho>)"
  shows "countable {A :: ('c paper_R_henkin_name) paper_named_term.
    named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A}"
  by (rule paper_R_admitted_terms_countable[OF paper_R_henkin_full_names_countable[OF names]])

end
