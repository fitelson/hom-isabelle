theory Bacon_Source_ZF_R_Eval_Correspondence
  imports Bacon_Source_ZF_R_Eval_Logical_Correspondence Bacon_Source_ZF_R_Eval_Lambda_Correspondence
begin

section \<open>Correspondence for every independently typed R term\<close>

text \<open>
  For every A:ρ∈ℒᴿ(Σ), every coded h:Root→M, and every old
  typed assignment g adequate for A, the independent evaluator returns
  Some(fρM(⟦A⟧ᵍM)) under the encoded assignment.
  Source: the term induction in Proposition 3.22, p.72, using the
  clauses of Definition 3.19, p.56.

  Induction follows the independent R typing judgment, with signature
  membership kept as a separate invariant. Both h and g are generalized.
  The abstraction step therefore receives only a strict-body induction
  hypothesis, uniformly at subsequent root arrows and their assignments.
  All six logical cases are proved, not assumed. No action-model,
  interpretation-totality or whole-term correspondence premise is used.

  This is a conditional representation theorem for the specified
  ZF-valued source category and explicit bounds. It does not remove
  those representability hypotheses or identify arbitrary HOL carriers.
\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_eval_typed_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and term_type: "paper_R_has_type stock A \<rho>"
    and names: "named_in_signature signature A"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_R_constructed_eval Root A h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation \<rho>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g A))"
  using term_type names arrow source typed adequate
proof (induction arbitrary: h g rule: paper_R_has_type.induct)
  case (Var n)
  show ?case by (rule paper_ZF_R_eval_Var[OF Var.prems(2) Var.prems(4) Var.prems(5)])
next
  case Const
  have root_object: "Root \<in> objects" by (rule paper_rooted_category.root_object[OF rooted])
  show ?case by (rule paper_ZF_R_eval_Const[
    OF bounded fregean functional root_object Const.prems(1)[unfolded named_in_signature.simps]
      Const.hyps Const.prems(2,3,4)])
next
  case (Logical l)
  show ?case by (rule paper_ZF_R_eval_Logical[OF bounded fregean functional Logical.hyps Logical.prems(2,4)])
next
  case (App F \<sigma> \<tau> B)
  have fn: "named_in_signature signature F" and bn: "named_in_signature signature B"
    using App.prems(1) by simp_all
  have fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    unfolding paper_R_in_language_def by (rule conjI[OF App.hyps(1) fn])
  have bl: "paper_R_in_language signature stock B \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF App.hyps(2) bn])
  have fa: "named_adequate g F" and ba: "named_adequate g B"
    using App.prems(5) by (auto simp: named_adequate_def)
  have head: "paper_ZF_R_constructed_eval Root F h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g F))"
    by (rule App.IH(1)[where h=h and g=g, OF fn App.prems(2,3,4) fa])
  have argument: "paper_ZF_R_constructed_eval Root B h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g B))"
    by (rule App.IH(2)[where h=h and g=g, OF bn App.prems(2,3,4) ba])
  show ?case by (rule paper_ZF_R_eval_App[
    OF bounded fregean functional rooted App.prems(2,3) fl bl App.prems(4,5) head argument])
next
  case (Lam B \<tau> n)
  have bn: "named_in_signature signature B" using Lam.prems(1) by simp
  have body: "paper_R_in_language signature stock B \<tau>"
    unfolding paper_R_in_language_def by (rule conjI[OF Lam.hyps(1) bn])
  show ?case
  proof (rule paper_ZF_R_eval_Lam[
      OF bounded fregean functional body Lam.hyps(2,3) Lam.prems(2,3,4,5)])
    fix j k
    assume ja: "j \<in> Encoding.coded_arrows" and js: "Encoding.coded_source j = Root"
      and kt: "named_env_typed (paper_bbk_domain (Encoding.coded_target j)) stock k"
      and ka: "named_adequate k B"
    show "paper_ZF_R_constructed_eval Root B j
        (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target j) k) =
      Some (paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target j)
        (paper_bbk_denote (Encoding.coded_target j) k B))"
      by (rule Lam.IH[where h=j and g=k, OF bn ja js kt ka])
  qed
qed

theorem paper_ZF_R_eval_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A \<rho>"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_R_constructed_eval Root A h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation \<rho>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g A))"
proof -
  have term_type: "paper_R_has_type stock A \<rho>" and names: "named_in_signature signature A"
    using language unfolding paper_R_in_language_def by blast+
  show ?thesis by (rule paper_ZF_R_eval_typed_correspondence[
    OF bounded fregean functional rooted term_type names arrow source typed adequate])
qed

end

end
