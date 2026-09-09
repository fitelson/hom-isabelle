theory Bacon_Source_ZF_Action_BBK_Identity_Truth
  imports Bacon_Source_ZF_Action_BBK_Logical_Application
begin

section \<open>Identity means equality of the actual denoted values\<close>

text \<open>
  At identity pairs the graph for =σ yields a proposition containing idW
  exactly when a=b. This is equality of ZF values, not equality of their
  truth values or an assumed separation/Functionality condition.
  Source: Definition 3.1(iii.f), p.44, and Definition 3.19, p.56.
  The operand language entails σ∈R; σ may be any higher R type.
\<close>

theorem paper_ZF_action_bbk_valuation_identity:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g
        (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A =
      paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B)"
proof -
  let ?a = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A"
  let ?b = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g B"
  have symbol: "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)" by simp
  have am: "?a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
    by (rule paper_ZF_action_bbk_denote_type[OF model left arrow origin typed adequate_left])
  have bm: "?b \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
    by (rule paper_ZF_action_bbk_denote_type[OF model right arrow origin typed adequate_right])
  have first: "Elem (Opair (identity (target h)) ?a) (paper_ZF_pair_code Ar source target (D \<sigma>) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=\<sigma>, OF model arrow am])
  have second: "Elem (Opair (identity (target h)) ?b)
      (paper_ZF_pair_code Ar source target (D \<sigma>) (target (identity (target h))))"
    by (simp only: paper_ZF_action_bbk_identity_data(3)[OF model arrow];
      rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>=\<sigma>, OF model arrow bm])
  have af: "T \<sigma> (identity (target h)) ?a = ?a"
    by (rule paper_ZF_action_bbk_identity_transport[where D=D and h=h and \<sigma>=\<sigma>, OF model arrow am])
  have bf: "T \<sigma> (identity (target h)) ?b = ?b"
    by (rule paper_ZF_action_bbk_identity_transport[where D=D and h=h and \<sigma>=\<sigma>, OF model arrow bm])
  show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
    paper_ZF_action_bbk_binary_logical_denote[OF model symbol left right arrow origin typed adequate_left adequate_right]
    paper_ZF_logical_identity_apply[where D=D and W="target h" and \<sigma>=\<sigma>, OF first second]
    paper_ZF_action_bbk_identity_data[OF model arrow] Sep paper_ZF_outgoing_code_member af bf; simp)
qed

end
