theory Bacon_Source_ZF_Hull_Representation
  imports Bacon_Source_ZF_Natural_Bounds Bacon_Source_ZF_R_Represented_Category_Action_Model
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Classical_Hull_Cardinal
begin

section \<open>An actual action model from the size-controlled classical hull\<close>

text \<open>
  Start with a bounded C-model Root whose values already belong to
  the HOL-ZF carrier. The proved separating hull has at most |B|
  arrows, so a bounded injective arrow code is obtained from cardinal
  comparison, not assumed. Every original individual domain lies inside
  explode(B). The same B supplies both representation bounds.

  The existing Proposition 3.22 construction performs the reachable
  restriction and the simultaneous type recursion, constructs an actual
  action model, and preserves root truth for all typed adequate partial
  assignments. Root is the same model record, not a chosen quotient of
  objects. No action-model, premodel, coding-map, or all-type-decoder
  premise is introduced. Source: pp.57 and 72, relative to HOL-ZF.
\<close>

theorem paper_ZF_classicism_hull_action_representation:
  fixes B :: ZF and \<Sigma> :: "'c ssignature" and Root :: "('c,ZF) paper_bbk_model_data"
  assumes infinite: "infinite (explode B)"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of (explode B)"
    and root: "Root \<in> paper_R_bounded_classicism_models \<Sigma> G (explode B)"
  shows "\<exists>Obj :: ('c,ZF) paper_bbk_model_data set. \<exists>Ar :: ZF.
    \<exists>s :: ZF \<Rightarrow> ('c,ZF) paper_bbk_model_data. \<exists>t :: ZF \<Rightarrow> ('c,ZF) paper_bbk_model_data.
    \<exists>c :: ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>i :: ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>D :: otype \<Rightarrow> ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>T :: otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>I :: otype \<Rightarrow> 'c \<Rightarrow> ZF.
      paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I \<and>
      (\<forall>A. paper_R_in_language \<Sigma> G A Prop \<longrightarrow>
        ((\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
            paper_ZF_action_holds Ar s t c i D T I G (i Root) g A) =
         (\<forall>g. named_env_typed (paper_bbk_domain Root) G g \<longrightarrow> named_adequate g A \<longrightarrow>
            paper_bbk_valuation Root (paper_bbk_denote Root g A))))"
proof -
  interpret H: paper_R_classicism_hull \<Sigma> G "explode B" Root
    by (rule paper_R_classicism_hull.intro[OF infinite names root])
  have arrow_cardinal: "card_of H.generated_arrows \<le>o card_of (explode B)"
    by (rule H.paper_R_classicism_hull_arrows_cardinal_bound)
  obtain encode :: "('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF"
    where injective: "inj_on encode H.generated_arrows" and bounded: "encode ` H.generated_arrows \<subseteq> explode B"
    by (rule paper_ZF_cardinal_bounded_encoding[OF arrow_cardinal])
  interpret Representation: paper_ZF_R_type_encoding \<Sigma> G H.generated_objects H.generated_arrows encode B B
    by unfold_locales (rule H.paper_R_classicism_hull_subcategory, rule injective, rule bounded)
  have individuals: "paper_bbk_domain M Ind \<subseteq> explode B" if object: "M \<in> H.generated_objects" for M
    using H.paper_R_classicism_hull_domains[OF object] by blast
  let ?Obj = "Representation.paper_ZF_R_reachable_objects Root"
  let ?Ar = "Representation.paper_ZF_R_reachable_arrow_code Root"
  let ?s = "Representation.paper_ZF_R_reachable_source Root"
  let ?t = "Representation.paper_ZF_R_reachable_target Root"
  let ?c = "Representation.paper_ZF_R_reachable_compose Root"
  let ?i = "Representation.Encoding.coded_identity"
  obtain D T I where model: "paper_ZF_action_model \<Sigma> G ?Obj ?Ar ?s ?t ?c ?i Root D T I"
    and truth: "\<forall>A. paper_R_in_language \<Sigma> G A Prop \<longrightarrow>
      ((\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
          paper_ZF_action_holds ?Ar ?s ?t ?c ?i D T I G (?i Root) g A) =
       (\<forall>g. named_env_typed (paper_bbk_domain Root) G g \<longrightarrow> named_adequate g A \<longrightarrow>
          paper_bbk_valuation Root (paper_bbk_denote Root g A)))"
    using Representation.paper_ZF_R_represented_category_action_model[
      OF individuals H.paper_R_classicism_hull_intensional H.paper_R_classicism_hull_root] by blast
  show ?thesis
    by (rule exI[where x="?Obj"], rule exI[where x="?Ar"], rule exI[where x="?s"], rule exI[where x="?t"],
      rule exI[where x="?c"], rule exI[where x="?i"], rule exI[where x=D], rule exI[where x=T], rule exI[where x=I],
      rule conjI[OF model truth])
qed

end
