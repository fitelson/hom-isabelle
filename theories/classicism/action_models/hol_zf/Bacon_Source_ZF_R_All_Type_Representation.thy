theory Bacon_Source_ZF_R_All_Type_Representation
  imports Bacon_Source_ZF_R_Base_Invariants Bacon_Source_ZF_R_Arrow_Invariant
begin

section \<open>The simultaneous representation at every R type\<close>

text \<open>
  The structural recursion now satisfies its invariant at EVERY R
  type, uniformly over all objects of the supplied category.
  This establishes the simultaneous range/action/bijection part of
  Proposition 3.22's construction on p.72.

  The source category consists of independently validated R models
  whose original values are ZF values. Selected arrows have the
  explicitly supplied bounded injection, and individual fibers lie
  in IndividualBound. Quasi-Fregeanness and quasi-functionality are
  source hypotheses. No higher-type representability bound or
  all-type decoder is assumed.

  This theorem is not yet Proposition 3.22 in full: it constructs
  the carrier actions and their bijections. Root constants, the
  partial interpretation, its totality and truth preservation still
  require proofs. Arbitrary HOL-valued source-category recoding is
  a separate representability obligation.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_all_type_invariant:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<rho>"
  shows "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<rho> (type_representation \<rho>)"
  using rt
proof (induction \<rho>)
  case Ind
  show ?case by (rule paper_ZF_R_Ind_invariant[OF bounded])
next
  case Prop
  show ?case by (rule paper_ZF_R_Prop_invariant[OF fregean])
next
  case (Arr \<sigma> \<tau>)
  have argument_type: "paper_R_type \<sigma>" and result_type: "paper_R_type \<tau>"
    using Arr.prems by simp_all
  have encoding: "paper_ZF_R_profile_encoding signature stock objects arrows encode ArrowBound"
    by unfold_locales
  have child_input: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule Arr.IH(1)[OF argument_type])
  have child_output: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<tau> (type_representation \<tau>)"
    by (rule Arr.IH(2)[OF result_type])
  show ?case
    by (simp only: paper_ZF_R_type_representation_arrow[OF Arr.prems];
      rule paper_ZF_R_arrow_invariant[OF encoding functional Arr.prems child_input child_output])
qed

end

end
