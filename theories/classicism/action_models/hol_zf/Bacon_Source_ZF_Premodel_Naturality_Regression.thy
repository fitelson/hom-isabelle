theory Bacon_Source_ZF_Premodel_Naturality_Regression
  imports Bacon_Source_ZF_Degenerate_Premodel Bacon_Source_ZF_Action_Model
begin

section \<open>Defined interpretation need not be in a premodel's selected stock\<close>

text \<open>
  Proposition C.1, p.70, is printed for an action PREMODEL and
  a defined interpretation. Definition 3.19 permits a logical graph
  to be defined without membership in the selected fiber; the latter
  is an additional requirement in Definition 3.20.

  In the preceding genuine premodel, ¬ denotes the empty function
  graph because its proposition-argument pair domain is empty. Its
  value is not in the selected type-(t→t) fiber, which is empty.
  Consequently the source action map is not defined at that value.
  A total-HOL reading of the unguarded C.1 equation can even be false:
  our legal off-domain extension sends Empty to Singleton Empty.

  This is not a counterexample to model-level naturality, nor to a
  statement guarded by membership of the interpreted value. It
  identifies the missing definedness/membership qualification in a
  premodel-only reading. No BBK model or proof judgment is used.
\<close>

abbreviation paper_ZF_degenerate_eval where
  "paper_ZF_degenerate_eval G A h g \<equiv>
    paper_ZF_action_eval paper_ZF_degenerate_arrows
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>i j. Empty) (\<lambda>_. Empty)
      paper_ZF_degenerate_domain paper_ZF_degenerate_transport (\<lambda>\<rho> c. Empty) G A h g"

lemma paper_ZF_empty_pair_code:
  "paper_ZF_pair_code A source target (\<lambda>W. Empty) W = Empty"
proof -
  have absent: "\<not> Elem z (paper_ZF_pair_code A source target (\<lambda>W. Empty) W)" for z
    using paper_ZF_pair_code_projections[where z=z and A=A and source=source and target=target
      and X="\<lambda>W. Empty" and W=W]
    by (auto simp: explode_Elem Empty)
  show ?thesis by (rule iffD2[OF Ext]; simp add: absent Empty)
qed

lemma paper_ZF_empty_Lambda:
  "Lambda Empty b = Empty"
  by (rule iffD2[OF Ext]; simp add: Lambda_def Repl Empty)

lemma paper_ZF_degenerate_Not_eval:
  "paper_ZF_degenerate_eval G (NLogical SNot) h g = Some Empty"
  by (simp add: paper_ZF_action_eval.simps paper_ZF_logical_value.simps
    paper_ZF_pair_lambda_def paper_ZF_degenerate_Prop_domain
    paper_ZF_empty_pair_code paper_ZF_empty_Lambda)

lemma paper_ZF_degenerate_Not_outside:
  "Empty \<notin> explode (paper_ZF_degenerate_domain (Arr Prop Prop) ())"
  by (simp add: paper_ZF_degenerate_domain_def explode_Elem Empty)

lemma paper_ZF_degenerate_regression_guards:
  "paper_R_in_language (\<lambda>\<rho>. {} :: 'c set) G (NLogical SNot) (Arr Prop Prop) \<and>
    paper_ZF_action_env_typed paper_ZF_degenerate_domain G () Map.empty \<and>
    named_adequate Map.empty (NLogical SNot :: 'c paper_named_term) \<and>
    Empty \<in> explode paper_ZF_degenerate_arrows"
  by (auto simp: paper_R_in_language_def named_in_signature.simps
    paper_ZF_action_env_typed_def named_env_typed_def named_adequate_def
    paper_ZF_degenerate_arrow_set intro: paper_R_has_type.Logical[where G=G and l=SNot, simplified])

lemma paper_ZF_singleton_Empty_distinct:
  "Singleton Empty \<noteq> Empty"
proof
  assume equal: "Singleton Empty = Empty"
  have "Elem Empty (Singleton Empty)" by (simp only: Singleton)
  then show False by (simp only: equal Empty)
qed

theorem paper_ZF_degenerate_totalized_naturality_fails:
  "paper_ZF_degenerate_eval G (NLogical SNot) Empty
      (paper_ZF_action_transport_assignment G paper_ZF_degenerate_transport Empty Map.empty) \<noteq>
    map_option (paper_ZF_degenerate_transport (Arr Prop Prop) Empty)
      (paper_ZF_degenerate_eval G (NLogical SNot) Empty Map.empty)"
proof -
  have left: "paper_ZF_degenerate_eval G (NLogical SNot) Empty
      (paper_ZF_action_transport_assignment G paper_ZF_degenerate_transport Empty Map.empty) = Some Empty"
    by (rule paper_ZF_degenerate_Not_eval)
  have right: "map_option (paper_ZF_degenerate_transport (Arr Prop Prop) Empty)
      (paper_ZF_degenerate_eval G (NLogical SNot) Empty Map.empty) = Some (Singleton Empty)"
    by (simp only: paper_ZF_degenerate_Not_eval option.map;
      simp add: paper_ZF_degenerate_transport_def)
  show ?thesis
  proof
    assume equal: "paper_ZF_degenerate_eval G (NLogical SNot) Empty
        (paper_ZF_action_transport_assignment G paper_ZF_degenerate_transport Empty Map.empty) =
      map_option (paper_ZF_degenerate_transport (Arr Prop Prop) Empty)
        (paper_ZF_degenerate_eval G (NLogical SNot) Empty Map.empty)"
    have values_equal: "Some Empty = Some (Singleton Empty)"
      by (rule trans[OF left[symmetric] trans[OF equal right]])
    have "Singleton Empty = Empty" using values_equal by simp
    then show False using paper_ZF_singleton_Empty_distinct by contradiction
  qed
qed

theorem paper_ZF_degenerate_partial_transport_undefined:
  "paper_ZF_degenerate_eval G (NLogical SNot) Empty Map.empty = Some Empty \<and>
    (if Empty \<in> explode (paper_ZF_degenerate_domain (Arr Prop Prop) ())
     then Some (paper_ZF_degenerate_transport (Arr Prop Prop) Empty Empty)
     else None) = None"
  by (simp only: paper_ZF_degenerate_Not_eval paper_ZF_degenerate_Not_outside if_False; simp)

theorem paper_ZF_premodel_defined_value_need_not_be_selected:
  "paper_ZF_action_premodel (\<lambda>\<rho>. {} :: 'c set) {()} paper_ZF_degenerate_arrows
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>i j. Empty) (\<lambda>_. Empty) ()
      paper_ZF_degenerate_domain paper_ZF_degenerate_transport (\<lambda>\<rho> c. Empty) \<and>
    paper_ZF_degenerate_eval G (NLogical SNot :: 'c paper_named_term) Empty Map.empty = Some Empty \<and>
    Empty \<notin> explode (paper_ZF_degenerate_domain (Arr Prop Prop) ())"
  by (rule conjI[OF paper_ZF_degenerate_premodel];
    simp only: paper_ZF_degenerate_Not_eval paper_ZF_degenerate_Not_outside; simp)

end
