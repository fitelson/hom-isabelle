theory Bacon_Source_ZF_Action_BBK_Model
  imports Bacon_Source_ZF_Action_BBK_Propositional_Truth Bacon_Source_ZF_Action_BBK_Identity_Truth
    Bacon_Source_ZF_Action_BBK_Quantifier_Truth Bacon_Source_ZF_Model_Conversion
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_BBK_Interface
begin

section \<open>Raw βη invariance of the candidate denotation\<close>

lemma paper_ZF_action_bbk_denote_beta_eta:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and conversion: "paper_R_raw_beta_eta G \<rho> A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A =
    paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B"
proof -
  have action_typed: "paper_ZF_action_env_typed D G (target h) g"
    using typed by (simp only: paper_ZF_action_bbk_env_iff)
  have equal: "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h g"
    by (rule paper_ZF_action_model_raw_conversion[
      OF model conversion left right arrow origin action_typed adequate_left adequate_right])
  show ?thesis by (simp only: paper_ZF_action_bbk_denote_def equal)
qed

section \<open>Every root arrow yields an actual independent R-BBK model\<close>

text \<open>
  At each h:Root→W, the domain is Wρ at R indices, Jₕ is the value
  of the independent evaluator, and Vₕ tests idW membership. Every
  field below is discharged from the action-model criterion and the
  separately proved structural, conversion and logical graph lemmas.
  Source: Proposition 3.21, p.70, through Proposition C.6, p.71.

  Non-R domains are empty only to extend the source R-indexed family
  to the ambient type datatype. Application remains heterogeneous;
  quantifiers range over every domain value; identity is actual value
  equality. No BBK-model, logical-stock closure, Functionality or unique
  root-arrow premise is assumed. C.7 and Logical Equivalence remain a
  separate argument and are not asserted by this model certificate.
\<close>

theorem paper_ZF_action_to_R_bbk_model:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
  shows "paper_R_bbk_model \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
    (paper_ZF_action_bbk_valuation target identity h)"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity Root"
    using model unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity Root by (rule rooted)
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  show ?thesis
  proof (rule paper_R_bbk_model.intro)
    show "paper_R_rich G" using model unfolding paper_ZF_action_model_def by (rule conjunct1)
  next
    fix \<sigma>
    assume rt: "paper_R_type \<sigma>"
    show "?D \<sigma> \<noteq> {}" by (rule paper_ZF_action_bbk_domain_nonempty[OF model object rt])
  next
    fix \<sigma>
    assume outside: "\<not> paper_R_type \<sigma>"
    show "?D \<sigma> = {}" by (rule paper_ZF_action_bbk_domain_nonR[OF outside])
  next
    fix A \<sigma> g
    assume language: "paper_R_in_language \<Sigma> G A \<sigma>"
      and typed: "named_env_typed ?D G g" and adequate: "named_adequate g A"
    show "?J g A \<in> ?D \<sigma>"
      by (rule paper_ZF_action_bbk_denote_type[OF model language arrow origin typed adequate])
  next
    fix g n a
    assume typed: "named_env_typed ?D G g" and assigned: "g n = Some a"
    show "?J g (NVar n) = a" by (rule paper_ZF_action_bbk_denote_var[where g=g and n=n, OF assigned])
  next
    fix F \<sigma> \<tau> A H \<upsilon> \<rho> B g k
    assume fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and al: "paper_R_in_language \<Sigma> G A \<sigma>"
      and hl: "paper_R_in_language \<Sigma> G H (Arr \<upsilon> \<rho>)" and bl: "paper_R_in_language \<Sigma> G B \<upsilon>"
      and gt: "named_env_typed ?D G g" and kt: "named_env_typed ?D G k"
      and ga: "named_adequate g (NApp F A)" and ka: "named_adequate k (NApp H B)"
      and heads: "?J g F = ?J k H" and arguments: "?J g A = ?J k B"
    show "?J g (NApp F A) = ?J k (NApp H B)"
      by (rule paper_ZF_action_bbk_denote_application_cong[
        OF model arrow origin fl al hl bl gt kt ga ka heads arguments])
  next
    fix A \<sigma> g k
    assume language: "paper_R_in_language \<Sigma> G A \<sigma>"
      and gt: "named_env_typed ?D G g" and kt: "named_env_typed ?D G k"
      and ga: "named_adequate g A" and ka: "named_adequate k A"
      and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
    show "?J g A = ?J k A" by (rule paper_ZF_action_bbk_denote_locality[OF agree])
  next
    fix \<sigma> A B g
    assume conversion: "paper_R_raw_beta_eta G \<sigma> A B"
      and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
      and typed: "named_env_typed ?D G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
    show "?J g A = ?J g B"
      by (rule paper_ZF_action_bbk_denote_beta_eta[OF model arrow origin conversion left right typed aa ba])
  next
    fix A g
    assume language: "paper_R_in_language \<Sigma> G A Prop"
      and typed: "named_env_typed ?D G g" and adequate: "named_adequate g A"
    show "?V (?J g (NApp (NLogical SNot) A)) = (\<not> ?V (?J g A))"
      by (rule paper_ZF_action_bbk_valuation_neg[OF model arrow origin language typed adequate])
  next
    fix A B g
    assume left: "paper_R_in_language \<Sigma> G A Prop" and right: "paper_R_in_language \<Sigma> G B Prop"
      and typed: "named_env_typed ?D G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
    show "?V (?J g (NApp (NApp (NLogical SAnd) A) B)) = (?V (?J g A) \<and> ?V (?J g B))"
      by (rule paper_ZF_action_bbk_valuation_conj[OF model arrow origin left right typed aa ba])
  next
    fix A B g
    assume left: "paper_R_in_language \<Sigma> G A Prop" and right: "paper_R_in_language \<Sigma> G B Prop"
      and typed: "named_env_typed ?D G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
    show "?V (?J g (NApp (NApp (NLogical SOr) A) B)) = (?V (?J g A) \<or> ?V (?J g B))"
      by (rule paper_ZF_action_bbk_valuation_disj[OF model arrow origin left right typed aa ba])
  next
    fix F \<sigma> g n
    assume predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
      and typed: "named_env_typed ?D G g" and adequate: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    show "?V (?J g (NApp (NLogical (SAll \<sigma>)) F)) = (\<forall>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n))))"
      by (rule paper_ZF_action_bbk_valuation_forall[OF model arrow origin predicate typed adequate nt fresh])
  next
    fix F \<sigma> g n
    assume predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
      and typed: "named_env_typed ?D G g" and adequate: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    show "?V (?J g (NApp (NLogical (SEx \<sigma>)) F)) = (\<exists>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n))))"
      by (rule paper_ZF_action_bbk_valuation_exists[OF model arrow origin predicate typed adequate nt fresh])
  next
    fix A \<sigma> B g
    assume left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
      and typed: "named_env_typed ?D G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
    show "?V (?J g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (?J g A = ?J g B)"
      by (rule paper_ZF_action_bbk_valuation_identity[OF model arrow origin left right typed aa ba])
  qed
qed

end
