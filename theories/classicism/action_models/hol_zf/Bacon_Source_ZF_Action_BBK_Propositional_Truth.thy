theory Bacon_Source_ZF_Action_BBK_Propositional_Truth
  imports Bacon_Source_ZF_Action_BBK_Logical_Application
begin

section \<open>Negation, conjunction and disjunction at every root arrow\<close>

text \<open>
  The candidate valuation tests membership of idW. The literal logical
  graphs give outgoing complement, intersection and union; the action
  identity law removes the intervening transport. Source: Definition
  3.1(iii.a–c), p.44, and Definition 3.19, p.56.
  Only the independent action model is assumed, never a BBK model or
  separate logical-stock closure. All assignments remain partial.
\<close>

theorem paper_ZF_action_bbk_valuation_neg:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and language: "paper_R_in_language \<Sigma> G A Prop"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g" and adequate: "named_adequate g A"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical SNot) A)) =
    (\<not> paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A))"
proof -
  let ?p = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A"
  have symbol: "paper_logical_type SNot = Arr Prop Prop" by simp
  have member: "?p \<in> paper_ZF_action_bbk_domain D (target h) Prop"
    by (rule paper_ZF_action_bbk_denote_type[OF model language arrow origin typed adequate])
  have pair: "Elem (Opair (identity (target h)) ?p) (paper_ZF_pair_code Ar source target (D Prop) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=Prop, OF model arrow member])
  show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
    paper_ZF_action_bbk_unary_logical_denote[OF model symbol language arrow origin typed adequate]
    paper_ZF_logical_not_apply[where D=D and W="target h", OF pair]
    paper_ZF_action_bbk_identity_data[OF model arrow] Sep paper_ZF_outgoing_code_member; simp)
qed

theorem paper_ZF_action_bbk_valuation_conj:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and left: "paper_R_in_language \<Sigma> G A Prop" and right: "paper_R_in_language \<Sigma> G B Prop"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NApp (NLogical SAnd) A) B)) =
    (paper_ZF_action_bbk_valuation target identity h
       (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) \<and>
     paper_ZF_action_bbk_valuation target identity h
       (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B))"
proof -
  let ?p = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A"
  let ?q = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B"
  have symbol: "paper_logical_type SAnd = Arr Prop (Arr Prop Prop)" by simp
  have pm: "?p \<in> paper_ZF_action_bbk_domain D (target h) Prop"
    by (rule paper_ZF_action_bbk_denote_type[OF model left arrow origin typed adequate_left])
  have qm: "?q \<in> paper_ZF_action_bbk_domain D (target h) Prop"
    by (rule paper_ZF_action_bbk_denote_type[OF model right arrow origin typed adequate_right])
  have first: "Elem (Opair (identity (target h)) ?p) (paper_ZF_pair_code Ar source target (D Prop) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=Prop, OF model arrow pm])
  have second: "Elem (Opair (identity (target h)) ?q)
      (paper_ZF_pair_code Ar source target (D Prop) (target (identity (target h))))"
    by (simp only: paper_ZF_action_bbk_identity_data(3)[OF model arrow];
      rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=Prop, OF model arrow qm])
  have fixed: "T Prop (identity (target h)) ?p = ?p"
    by (rule paper_ZF_action_bbk_identity_transport[where D=D and h=h and \<sigma>=Prop, OF model arrow pm])
  show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
    paper_ZF_action_bbk_binary_logical_denote[OF model symbol left right arrow origin typed adequate_left adequate_right]
    paper_ZF_logical_and_apply[where D=D and W="target h", OF first second] fixed Sep)
qed

theorem paper_ZF_action_bbk_valuation_disj:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and left: "paper_R_in_language \<Sigma> G A Prop" and right: "paper_R_in_language \<Sigma> G B Prop"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NApp (NLogical SOr) A) B)) =
    (paper_ZF_action_bbk_valuation target identity h
       (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) \<or>
     paper_ZF_action_bbk_valuation target identity h
       (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B))"
proof -
  let ?p = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A"
  let ?q = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B"
  have symbol: "paper_logical_type SOr = Arr Prop (Arr Prop Prop)" by simp
  have pm: "?p \<in> paper_ZF_action_bbk_domain D (target h) Prop"
    by (rule paper_ZF_action_bbk_denote_type[OF model left arrow origin typed adequate_left])
  have qm: "?q \<in> paper_ZF_action_bbk_domain D (target h) Prop"
    by (rule paper_ZF_action_bbk_denote_type[OF model right arrow origin typed adequate_right])
  have first: "Elem (Opair (identity (target h)) ?p) (paper_ZF_pair_code Ar source target (D Prop) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=Prop, OF model arrow pm])
  have second: "Elem (Opair (identity (target h)) ?q)
      (paper_ZF_pair_code Ar source target (D Prop) (target (identity (target h))))"
    by (simp only: paper_ZF_action_bbk_identity_data(3)[OF model arrow];
      rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=Prop, OF model arrow qm])
  have fixed: "T Prop (identity (target h)) ?p = ?p"
    by (rule paper_ZF_action_bbk_identity_transport[where D=D and h=h and \<sigma>=Prop, OF model arrow pm])
  show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
    paper_ZF_action_bbk_binary_logical_denote[OF model symbol left right arrow origin typed adequate_left adequate_right]
    paper_ZF_logical_or_apply[where D=D and W="target h", OF first second] fixed union)
qed

end
