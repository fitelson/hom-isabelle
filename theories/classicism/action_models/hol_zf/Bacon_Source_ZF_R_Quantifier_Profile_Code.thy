theory Bacon_Source_ZF_R_Quantifier_Profile_Code
  imports Bacon_Source_ZF_R_Quantifier_Tests Bacon_Source_ZF_R_Negation_Profile_Code
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Quantifier_Profile
begin

section \<open>Quantified profiles are the literal outgoing subsets\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_quantifier_profile_code:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and predicate: "d \<in> paper_bbk_domain M (Arr \<sigma> Prop)"
  shows "proposition_code M (paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
      (Arr \<sigma> Prop) Prop (paper_bbk_denote M Map.empty
        (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) d) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M)
      (\<lambda>j. if universal then
        \<forall>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j))
            (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z))
        else \<exists>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j))
            (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z)))"
proof -
  let ?v = "paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
    (Arr \<sigma> Prop) Prop (paper_bbk_denote M Map.empty
      (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) d"
  let ?P = "\<lambda>j. if universal then
      \<forall>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
        Elem (Encoding.coded_identity (Encoding.coded_target j))
          (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z))
      else \<exists>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
        Elem (Encoding.coded_identity (Encoding.coded_target j))
          (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z))"
  show ?thesis
  proof (rule iffD2[OF Ext], intro allI)
    fix j
    show "Elem j (proposition_code M ?v) =
      Elem j (Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M) ?P)"
    proof (cases "j \<in> Encoding.coded_arrows")
      case True
      note ja = True
      let ?h = "Encoding.decode_arrow j"
      have ha: "?h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF True])
      have member: "Elem j (proposition_code M ?v) =
          (?h \<in> paper_bbk_truth_profile_on arrows M ?v)"
        using paper_ZF_R_truth_profile_code_on[where M=M and p="?v", OF ha]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      show ?thesis
      proof (cases "Encoding.coded_source j = M")
        case True
        note source = True
        have hs: "paper_arrow_source ?h = M" using source by (simp only: paper_ZF_recode_source_def)
        have truth: "paper_bbk_valuation (Encoding.coded_target j) (paper_arrow_map ?h Prop ?v) =
          (if universal then \<forall>a\<in>paper_bbk_domain (Encoding.coded_target j) \<sigma>.
            paper_bbk_valuation (Encoding.coded_target j) (paper_R_application signature stock
              (paper_bbk_domain (Encoding.coded_target j)) (paper_bbk_denote (Encoding.coded_target j))
              \<sigma> Prop (paper_arrow_map ?h (Arr \<sigma> Prop) d) a)
           else \<exists>a\<in>paper_bbk_domain (Encoding.coded_target j) \<sigma>.
            paper_bbk_valuation (Encoding.coded_target j) (paper_R_application signature stock
              (paper_bbk_domain (Encoding.coded_target j)) (paper_bbk_denote (Encoding.coded_target j))
              \<sigma> Prop (paper_arrow_map ?h (Arr \<sigma> Prop) d) a))"
          using paper_R_quantifier_profile_value[OF R_category object rt predicate ha hs]
          by (simp only: paper_ZF_recode_target_def)
        have tests: "?P j = paper_bbk_valuation (Encoding.coded_target j) (paper_arrow_map ?h Prop ?v)"
          using paper_ZF_R_quantifier_tests[OF bounded fregean functional rt object predicate ja source]
          by (simp only: truth)
        show ?thesis using tests
          by (simp only: member paper_bbk_truth_profile_on_member ha hs Sep
            paper_ZF_outgoing_code_member ja source paper_ZF_recode_target_def; blast)
      next
        case False
        have hs: "paper_arrow_source ?h \<noteq> M" using False by (simp add: paper_ZF_recode_source_def)
        show ?thesis
          by (simp only: member paper_bbk_truth_profile_on_member hs Sep paper_ZF_outgoing_code_member False; blast)
      qed
    next
      case False
      have absent: "\<not> Elem j (proposition_code M ?v)"
        by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      show ?thesis using absent False
        by (simp only: Sep paper_ZF_outgoing_code_member; blast)
    qed
  qed
qed

end

end
