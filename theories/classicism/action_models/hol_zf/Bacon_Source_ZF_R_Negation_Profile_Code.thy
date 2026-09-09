theory Bacon_Source_ZF_R_Negation_Profile_Code
  imports Bacon_Source_ZF_R_Truth_Profile_Coding
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Negation_Profile
begin

section \<open>The encoded negation profile is literal outgoing complement\<close>

text \<open>
  CodeM(¬a)=OutCode(M)−CodeM(a), where ¬a is the original
  R-model application of its logical negation value to a∈Mₜ.
  Source: the ¬ clause of Definition 3.19, p.56, and the
  profile construction of Proposition 3.22, p.72.
  This is an equality of actual ZF sets. It uses neither
  quasi-Fregeanness nor an assumption that the full outgoing
  powerset is the proposition stock.
\<close>

context paper_ZF_R_profile_encoding
begin

lemma paper_ZF_R_truth_profile_code_outside:
  assumes outside: "z \<notin> Encoding.coded_arrows"
  shows "\<not> Elem z (proposition_code M p)"
proof
  assume member: "Elem z (proposition_code M p)"
  obtain h where arrow: "h \<in> arrows" and shape: "z = encode h"
    using member by (simp only: paper_ZF_R_truth_profile_code_member; blast)
  have coded: "z \<in> Encoding.coded_arrows"
    by (simp only: shape; rule Encoding.paper_ZF_encode_arrow_type[OF arrow])
  show False using outside coded by contradiction
qed

theorem paper_ZF_R_negation_profile_code:
  assumes object: "M \<in> objects" and member: "a \<in> paper_bbk_domain M Prop"
  shows "proposition_code M (paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
      Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)
      (\<lambda>z. \<not> Elem z (proposition_code M a))"
proof -
  let ?n = "paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
    Prop Prop (paper_bbk_denote M Map.empty (NLogical SNot)) a"
  have complement: "paper_bbk_truth_profile_on arrows M ?n =
    paper_outgoing arrows paper_arrow_source M - paper_bbk_truth_profile_on arrows M a"
    by (rule paper_R_negation_truth_profile[OF R_category object member])
  show ?thesis
  proof (rule iffD2[OF Ext], intro allI)
    fix z
    show "Elem z (proposition_code M ?n) =
      Elem z (Sep (paper_ZF_outgoing_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)
        (\<lambda>z. \<not> Elem z (proposition_code M a)))"
    proof (cases "z \<in> Encoding.coded_arrows")
      case True
      let ?h = "Encoding.decode_arrow z"
      have arrow: "?h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF True])
      have neg_code: "Elem z (proposition_code M ?n) =
          (?h \<in> paper_bbk_truth_profile_on arrows M ?n)"
        using paper_ZF_R_truth_profile_code_on[where M=M and p="?n", OF arrow]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      have arg_code: "Elem z (proposition_code M a) =
          (?h \<in> paper_bbk_truth_profile_on arrows M a)"
        using paper_ZF_R_truth_profile_code_on[where M=M and p=a, OF arrow]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      show ?thesis
        by (simp only: neg_code Sep paper_ZF_outgoing_code_member arg_code complement Diff_iff
          paper_outgoing_member True arrow paper_ZF_recode_source_def; blast)
    next
      case False
      have absent: "\<not> Elem z (proposition_code M ?n)"
        by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      show ?thesis using absent False
        by (simp only: Sep paper_ZF_outgoing_code_member; blast)
    qed
  qed
qed

end

end
