theory Bacon_Source_ZF_R_Base_Invariants
  imports Bacon_Source_ZF_R_Proposition_Base Bacon_Source_ZF_R_Type_Invariant
begin

section \<open>The recursion satisfies the invariant at e and t\<close>

text \<open>
  The individual identity map and proposition truth-profile map satisfy
  the action, forward-equivariance, and fiber-bijection invariant.
  Source: the two base clauses of Proposition 3.22, p.72.
  These conclusions assemble the preceding actual base proofs; they
  are not fields of an assumed all-type representation.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_Ind_invariant:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "paper_ZF_R_type_invariant objects arrows encode ArrowBound Ind (type_representation Ind)"
proof (rule paper_ZF_R_type_invariantI[OF paper_ZF_R_Ind_action[OF bounded] paper_ZF_R_Ind_forward_map[OF bounded]])
  fix M
  assume object: "M \<in> objects"
  show "bij_betw (paper_ZF_rep_encode (type_representation Ind) M) (paper_bbk_domain M Ind)
      (explode (paper_ZF_rep_domain (type_representation Ind) M))"
    by (rule paper_ZF_R_Ind_bijection[OF bounded[OF object]])
qed

theorem paper_ZF_R_Prop_invariant:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows"
  shows "paper_ZF_R_type_invariant objects arrows encode ArrowBound Prop (type_representation Prop)"
proof (rule paper_ZF_R_type_invariantI[OF paper_ZF_R_Prop_action paper_ZF_R_Prop_forward_map])
  fix M
  assume object: "M \<in> objects"
  show "bij_betw (paper_ZF_rep_encode (type_representation Prop) M) (paper_bbk_domain M Prop)
      (explode (paper_ZF_rep_domain (type_representation Prop) M))"
    by (rule paper_ZF_R_Prop_bijection[OF quasi object])
qed

end

end
