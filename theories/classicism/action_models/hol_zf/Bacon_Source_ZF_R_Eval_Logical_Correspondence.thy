theory Bacon_Source_ZF_R_Eval_Logical_Correspondence
  imports Bacon_Source_ZF_R_Boolean_Correspondence Bacon_Source_ZF_R_Identity_Correspondence
    Bacon_Source_ZF_R_Quantifier_Correspondence
begin

section \<open>All six logical families use their independently constructed graphs\<close>

text \<open>
  Each primitive logical value of Definition 3.19, p.56, is
  exactly the representation of the corresponding original R value.
  This theorem assembles the six proved cases; ∀ and ∃ instantiate
  the universal flag by True and False respectively.

  No logical-stock membership, evaluator equation, or whole-term
  correspondence is an assumption. The source bounds and
  quasi-Fregean/quasi-functional hypotheses remain explicit.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_eval_Logical:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type (paper_logical_type l)"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical l) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (paper_logical_type l)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical l)))"
proof (cases l)
  case SNot
  show ?thesis by (simp only: SNot paper_logical_type.simps; rule paper_ZF_R_eval_Not[OF bounded fregean functional arrow typed])
next
  case SAnd
  show ?thesis by (simp only: SAnd paper_logical_type.simps; rule paper_ZF_R_eval_And[OF bounded fregean functional arrow typed])
next
  case SOr
  show ?thesis by (simp only: SOr paper_logical_type.simps; rule paper_ZF_R_eval_Or[OF bounded fregean functional arrow typed])
next
  case (SAll \<sigma>)
  have sr: "paper_R_type \<sigma>" using rt by (simp add: SAll)
  show ?thesis
    using paper_ZF_R_eval_quantifier[where universal=True, OF bounded fregean functional sr arrow typed]
    by (simp only: SAll paper_logical_type.simps if_True)
next
  case (SEx \<sigma>)
  have sr: "paper_R_type \<sigma>" using rt by (simp add: SEx)
  show ?thesis
    using paper_ZF_R_eval_quantifier[where universal=False, OF bounded fregean functional sr arrow typed]
    by (simp only: SEx paper_logical_type.simps if_False)
next
  case (SEq \<sigma>)
  have sr: "paper_R_type \<sigma>" using rt by (simp add: SEq)
  show ?thesis by (simp only: SEq paper_logical_type.simps; rule paper_ZF_R_eval_Eq[OF bounded fregean functional sr arrow typed])
qed

end

end
