theory Bacon_Source_ZF_R_Boolean_Profile_Code
  imports Bacon_Source_ZF_R_Negation_Profile_Code
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Boolean_Profiles
begin

section \<open>Actual intersection and union of coded proposition profiles\<close>

text \<open>
  CodeM(a∧b)=CodeM(a)∩CodeM(b) and CodeM(a∨b)=CodeM(a)∪CodeM(b).
  Source: Definitions 3.10 and 3.19, pp.50 and 56.
  The original all-domain operations use their actual logical values.
  These set equalities follow from outgoing truth tests, not from
  a stipulated Boolean structure or fullness of the proposition stock.
\<close>

context paper_ZF_R_profile_encoding
begin

theorem paper_ZF_R_conjunction_profile_code:
  assumes object: "M \<in> objects" and am: "a \<in> paper_bbk_domain M Prop" and bm: "b \<in> paper_bbk_domain M Prop"
  shows "proposition_code M (paper_R_binary_logical_application signature stock (paper_bbk_domain M)
      (paper_bbk_denote M) Prop SAnd a b) = Sep (proposition_code M a) (\<lambda>z. Elem z (proposition_code M b))"
proof -
  let ?v = "paper_R_binary_logical_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b"
  have profiles: "paper_bbk_truth_profile_on arrows M ?v =
    paper_bbk_truth_profile_on arrows M a \<inter> paper_bbk_truth_profile_on arrows M b"
    by (rule paper_R_conjunction_truth_profile[OF R_category am bm])
  show ?thesis
  proof (rule iffD2[OF Ext], intro allI)
    fix z
    show "Elem z (proposition_code M ?v) = Elem z (Sep (proposition_code M a) (\<lambda>z. Elem z (proposition_code M b)))"
    proof (cases "z \<in> Encoding.coded_arrows")
      case True
      let ?h = "Encoding.decode_arrow z"
      have arrow: "?h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF True])
      have code: "Elem z (proposition_code M p) = (?h \<in> paper_bbk_truth_profile_on arrows M p)" for p
        using paper_ZF_R_truth_profile_code_on[where M=M and p=p, OF arrow]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      show ?thesis by (simp only: Sep code profiles Int_iff; blast)
    next
      case False
      have absent_value: "\<not> Elem z (proposition_code M ?v)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      have absent_a: "\<not> Elem z (proposition_code M a)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      have absent_b: "\<not> Elem z (proposition_code M b)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      show ?thesis using absent_value absent_a absent_b by (simp only: Sep; blast)
    qed
  qed
qed

theorem paper_ZF_R_disjunction_profile_code:
  assumes object: "M \<in> objects" and am: "a \<in> paper_bbk_domain M Prop" and bm: "b \<in> paper_bbk_domain M Prop"
  shows "proposition_code M (paper_R_binary_logical_application signature stock (paper_bbk_domain M)
      (paper_bbk_denote M) Prop SOr a b) = union (proposition_code M a) (proposition_code M b)"
proof -
  let ?v = "paper_R_binary_logical_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b"
  have profiles: "paper_bbk_truth_profile_on arrows M ?v =
    paper_bbk_truth_profile_on arrows M a \<union> paper_bbk_truth_profile_on arrows M b"
    by (rule paper_R_disjunction_truth_profile[OF R_category am bm])
  show ?thesis
  proof (rule iffD2[OF Ext], intro allI)
    fix z
    show "Elem z (proposition_code M ?v) = Elem z (union (proposition_code M a) (proposition_code M b))"
    proof (cases "z \<in> Encoding.coded_arrows")
      case True
      let ?h = "Encoding.decode_arrow z"
      have arrow: "?h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF True])
      have code: "Elem z (proposition_code M p) = (?h \<in> paper_bbk_truth_profile_on arrows M p)" for p
        using paper_ZF_R_truth_profile_code_on[where M=M and p=p, OF arrow]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      show ?thesis by (simp only: union code profiles Un_iff; blast)
    next
      case False
      have absent_value: "\<not> Elem z (proposition_code M ?v)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      have absent_a: "\<not> Elem z (proposition_code M a)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      have absent_b: "\<not> Elem z (proposition_code M b)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      show ?thesis using absent_value absent_a absent_b by (simp only: union; blast)
    qed
  qed
qed

end

end
