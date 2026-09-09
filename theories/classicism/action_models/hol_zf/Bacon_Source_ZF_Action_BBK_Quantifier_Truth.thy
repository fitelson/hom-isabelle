theory Bacon_Source_ZF_Action_BBK_Quantifier_Truth
  imports Bacon_Source_ZF_Action_BBK_Logical_Application
begin

section \<open>A fresh variable realizes every target-domain argument\<close>

text \<open>
  For each a∈Wσ, update g at a fresh variable n:σ. Locality keeps
  the predicate value unchanged, while the variable denotes a. Hence
  evaluating Fn under the update is actual graph application at ⟨idW,a⟩.
  This covers every domain value, not merely closed-denotable values.
  Source: Definition 3.1(iii.d–e), p.44, and Definition 3.19, p.56.
\<close>

lemma paper_ZF_action_bbk_fresh_predicate_test:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    and member: "a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h (g(n := Some a)) (NApp F (NVar n)) =
    app (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F) (Opair (identity (target h)) a)"
proof -
  let ?k = "g(n := Some a)"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have at_name: "a \<in> paper_ZF_action_bbk_domain D (target h) (G n)"
    by (simp only: nt; rule member)
  have kt: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G ?k"
    by (rule named_assignment_update_typed[where D="paper_ZF_action_bbk_domain D (target h)" and G=G and n=n,
      OF typed at_name])
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF nt rt])
  have whole: "named_adequate ?k (NApp F (NVar n))"
    using adequate by (auto simp: named_adequate_def named_assignment_update_domain)
  have same: "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h ?k F =
      paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F"
  proof (rule paper_ZF_action_bbk_denote_locality)
    fix m
    assume free: "m \<in> named_fv F"
    have distinct: "m \<noteq> n" using free fresh by blast
    show "?k m = g m" by (simp add: distinct)
  qed
  have assigned: "?k n = Some a" by simp
  show ?thesis by (simp only: paper_ZF_action_bbk_denote_application[OF model predicate variable arrow origin kt whole]
    same paper_ZF_action_bbk_denote_var[where g="?k" and n=n, OF assigned])
qed

section \<open>Universal quantifier truth in the candidate interpretation\<close>

theorem paper_ZF_action_bbk_valuation_forall:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>a\<in>paper_ZF_action_bbk_domain D (target h) \<sigma>.
      paper_ZF_action_bbk_valuation target identity h
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h (g(n := Some a)) (NApp F (NVar n))))"
proof -
  let ?d = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F"
  let ?test = "\<lambda>a. Elem (identity (target h)) (app ?d (Opair (identity (target h)) a))"
  let ?body = "\<lambda>a. paper_ZF_action_bbk_valuation target identity h
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h (g(n := Some a)) (NApp F (NVar n)))"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have symbol: "paper_logical_type (SAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  have member: "?d \<in> paper_ZF_action_bbk_domain D (target h) (Arr \<sigma> Prop)"
    by (rule paper_ZF_action_bbk_denote_type[OF model predicate arrow origin typed adequate])
  have pair: "Elem (Opair (identity (target h)) ?d)
      (paper_ZF_pair_code Ar source target (D (Arr \<sigma> Prop)) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>="Arr \<sigma> Prop", OF model arrow member])
  have quantified: "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>explode (D \<sigma> (target h)). ?test a)"
    by (simp only: paper_ZF_action_bbk_valuation_def
      paper_ZF_action_bbk_unary_logical_denote[OF model symbol predicate arrow origin typed adequate]
      paper_ZF_logical_forall_apply[where D=D and W="target h" and \<sigma>=\<sigma>, OF pair]
      paper_ZF_action_bbk_identity_data[OF model arrow] Sep paper_ZF_outgoing_code_member; simp)
  have tests: "?body a = ?test a" if am: "a \<in> explode (D \<sigma> (target h))" for a
  proof -
    have bm: "a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
      by (simp only: paper_ZF_action_bbk_domain_R[OF rt]; rule am)
    show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
      paper_ZF_action_bbk_fresh_predicate_test[OF model arrow origin predicate typed adequate nt fresh bm])
  qed
  have all_tests: "(\<forall>a\<in>explode (D \<sigma> (target h)). ?body a) =
      (\<forall>a\<in>explode (D \<sigma> (target h)). ?test a)"
    by (rule ball_cong[OF refl]; rule tests; assumption)
  show ?thesis by (simp only: quantified paper_ZF_action_bbk_domain_R[OF rt] all_tests)
qed

section \<open>Existential quantifier truth in the candidate interpretation\<close>

theorem paper_ZF_action_bbk_valuation_exists:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>a\<in>paper_ZF_action_bbk_domain D (target h) \<sigma>.
      paper_ZF_action_bbk_valuation target identity h
        (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h (g(n := Some a)) (NApp F (NVar n))))"
proof -
  let ?d = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F"
  let ?test = "\<lambda>a. Elem (identity (target h)) (app ?d (Opair (identity (target h)) a))"
  let ?body = "\<lambda>a. paper_ZF_action_bbk_valuation target identity h
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h (g(n := Some a)) (NApp F (NVar n)))"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have symbol: "paper_logical_type (SEx \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
  have member: "?d \<in> paper_ZF_action_bbk_domain D (target h) (Arr \<sigma> Prop)"
    by (rule paper_ZF_action_bbk_denote_type[OF model predicate arrow origin typed adequate])
  have pair: "Elem (Opair (identity (target h)) ?d)
      (paper_ZF_pair_code Ar source target (D (Arr \<sigma> Prop)) (target h))"
    by (rule paper_ZF_action_bbk_identity_pair[where D=D and h=h and \<sigma>="Arr \<sigma> Prop", OF model arrow member])
  have quantified: "paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>explode (D \<sigma> (target h)). ?test a)"
    by (simp only: paper_ZF_action_bbk_valuation_def
      paper_ZF_action_bbk_unary_logical_denote[OF model symbol predicate arrow origin typed adequate]
      paper_ZF_logical_exists_apply[where D=D and W="target h" and \<sigma>=\<sigma>, OF pair]
      paper_ZF_action_bbk_identity_data[OF model arrow] Sep paper_ZF_outgoing_code_member; simp)
  have tests: "?body a = ?test a" if am: "a \<in> explode (D \<sigma> (target h))" for a
  proof -
    have bm: "a \<in> paper_ZF_action_bbk_domain D (target h) \<sigma>"
      by (simp only: paper_ZF_action_bbk_domain_R[OF rt]; rule am)
    show ?thesis by (simp only: paper_ZF_action_bbk_valuation_def
      paper_ZF_action_bbk_fresh_predicate_test[OF model arrow origin predicate typed adequate nt fresh bm])
  qed
  have some_tests: "(\<exists>a\<in>explode (D \<sigma> (target h)). ?body a) =
      (\<exists>a\<in>explode (D \<sigma> (target h)). ?test a)"
    by (rule bex_cong[OF refl]; rule tests; assumption)
  show ?thesis by (simp only: quantified paper_ZF_action_bbk_domain_R[OF rt] some_tests)
qed

end
