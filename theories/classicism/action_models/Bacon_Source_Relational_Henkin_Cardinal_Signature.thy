theory Bacon_Source_Relational_Henkin_Cardinal_Signature
  imports Bacon_Source_Relational_Henkin_Full_Signature
    Bacon_Source_Relational_Admitted_Syntax_Cardinal
begin

section \<open>Cardinal bounds for the actual successive witness signatures\<close>

text \<open>
  Let U be infinite and suppose the declared original names have cardinal
  at most |U|. A successor stage adds only names Witness(k,σ,F) with F
  admitted at the previous stage. The set of such pairs (σ,F) has cardinal
  at most |U|, and the countable union of stages has the same bound.

  A stage can be uncountable: no enumeration of predicates or countability
  of the ambient name carrier is assumed. Closedness and R typing merely
  select a subset of the bounded raw syntax. This is a signature bound,
  with no consistency, richness, Henkin theory or model premise.
\<close>

lemma paper_R_otypes_cardinal_bound:
  assumes infinite: "infinite U"
  shows "card_of (UNIV :: otype set) \<le>o card_of U"
proof -
  have types: "card_of (UNIV :: otype set) \<le>o card_of (UNIV :: nat set)"
  proof (rule card_of_ordLeqI[where f=paper_R_type_nat_code])
    show "inj_on paper_R_type_nat_code (UNIV :: otype set)"
      by (rule inj_onI) simp
  qed simp
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  show ?thesis by (rule ordLeq_transitive[OF types naturals])
qed

theorem paper_R_henkin_stage_names_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of U"
  shows "card_of (\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>) \<le>o card_of U"
proof (induction k)
  case 0
  have equality: "(\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G 0 \<rho>) =
      image ROriginal (\<Union>\<rho>. \<Sigma> \<rho>)"
    by auto
  show ?case
    unfolding equality by (rule ordLeq_transitive[OF card_of_image names])
next
  case (Suc k)
  let ?Old = "\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>"
  let ?Terms = "{F :: ('c paper_R_henkin_name) paper_named_term.
    named_in_signature (paper_R_henkin_signature \<Sigma> G k) F}"
  let ?New = "image (\<lambda>p. RWitness k (fst p) (snd p)) ((UNIV :: otype set) \<times> ?Terms)"
  have terms: "card_of ?Terms \<le>o card_of U"
    by (rule paper_R_admitted_syntax_cardinal_bound[OF infinite Suc.IH])
  have types: "card_of (UNIV :: otype set) \<le>o card_of U"
    by (rule paper_R_otypes_cardinal_bound[OF infinite])
  have pairs: "card_of ((UNIV :: otype set) \<times> ?Terms) \<le>o card_of U"
    by (rule card_of_Times_ordLeq_infinite[OF infinite types terms])
  have new_names: "card_of ?New \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image pairs])
  have bound: "card_of (?Old \<union> ?New) \<le>o card_of U"
    by (rule card_of_Un_ordLeq_infinite[OF infinite Suc.IH new_names])
  have subset: "(\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>) \<subseteq> ?Old \<union> ?New"
  proof
    fix c
    assume member: "c \<in> (\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>)"
    obtain \<rho> where declared: "c \<in> paper_R_henkin_signature \<Sigma> G (Suc k) \<rho>"
      using member by blast
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
      have image_member: "(\<lambda>p. RWitness k (fst p) (snd p)) (\<rho>,F) \<in> ?New"
        by (rule imageI[OF pair])
      show ?thesis using image_member by (simp only: fst_conv snd_conv shape; blast)
    qed
  qed
  show ?case by (rule ordLeq_transitive[OF card_of_mono1[OF subset] bound])
qed

section \<open>The full admitted witness language\<close>

theorem paper_R_henkin_full_names_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of U"
  shows "card_of (\<Union>\<rho>. paper_R_henkin_full_signature \<Sigma> G \<rho>) \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have stages: "\<forall>k\<in>(UNIV :: nat set).
    card_of (\<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>) \<le>o card_of U"
    by (intro ballI; rule paper_R_henkin_stage_names_cardinal_bound[OF infinite names])
  have levels: "card_of (\<Union>k. \<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>) \<le>o card_of U"
    by (rule card_of_UNION_ordLeq_infinite[OF infinite naturals stages])
  have equality: "(\<Union>\<rho>. paper_R_henkin_full_signature \<Sigma> G \<rho>) =
      (\<Union>k. \<Union>\<rho>. paper_R_henkin_signature \<Sigma> G k \<rho>)"
    by (auto simp: paper_R_henkin_full_signature_def)
  show ?thesis by (simp only: equality; rule levels)
qed

corollary paper_R_henkin_full_admitted_syntax_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of U"
  shows "card_of {A :: ('c paper_R_henkin_name) paper_named_term.
    named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A} \<le>o card_of U"
  by (rule paper_R_admitted_syntax_cardinal_bound[OF infinite
        paper_R_henkin_full_names_cardinal_bound[OF infinite names]])

end
