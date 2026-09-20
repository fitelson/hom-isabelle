theory Goodman_Exact_Leibniz_Characterization
  imports Goodman_Exact_Logical_Values
begin

section \<open>A separating predicate in Bacon's exact restricted carrier\<close>

text \<open>
  At world w, a =σ b is represented by pp_e_eqv σ w a b, not generally
  by equality of the global HOL–ZF values a and b. We compare this local
  relation with the book's Leibniz condition: every admitted σ→t predicate
  has the same truth value at a and b.

  The separating predicate is x ↦ (x =σ a). Its membership in the exact
  function space is proved by the existing typed evaluation theorem,
  applied to λx. x =σ a. We do not quantify over all HOL functions or
  assume that every mathematical predicate belongs to the exact carrier.
\<close>

definition gi_exact_identity_test :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "gi_exact_identity_test \<sigma> a =
    Lambda (pp_e_domain \<sigma>)
      (\<lambda>x. pp_e_prop (\<lambda>v. pp_e_eqv \<sigma> v x a))"

lemma gi_exact_identity_test_term_type:
  "[\<sigma>] \<turnstile> Lam \<sigma> (Eq \<sigma> (Var 0) (Var 1)) : Arr \<sigma> Prop"
  by (intro has_type.Lam has_type.Eq has_type.Var; simp add: lookup_def)

lemma gi_exact_identity_test_denotation:
  "pp_e_eval pp_e_default_constants (extend_env a pp_e_closed_env)
      (Lam \<sigma> (Eq \<sigma> (Var 0) (Var 1))) =
    gi_exact_identity_test \<sigma> a"
  by (simp add: gi_exact_identity_test_def)

lemma gi_exact_identity_test_member:
  assumes parameter_member: "a \<in> gi_exact_domain \<sigma>"
  shows "gi_exact_identity_test \<sigma> a \<in> gi_exact_domain (Arr \<sigma> Prop)"
proof -
  have exact_member: "Elem a (pp_e_domain \<sigma>)"
    using parameter_member by (simp only: gi_exact_domain_member)
  have assignment_type: "pp_e_env_typed [\<sigma>] (extend_env a pp_e_closed_env)"
    by (rule pp_e_env_typed_extend[OF pp_e_empty_env_typed exact_member])
  have denotation_type:
      "pp_e_dom (Arr \<sigma> Prop)
        (pp_e_eval pp_e_default_constants (extend_env a pp_e_closed_env)
          (Lam \<sigma> (Eq \<sigma> (Var 0) (Var 1))))"
    by (rule DefaultExactBaconConstants.pp_e_eval_type[
      OF gi_exact_identity_test_term_type assignment_type])
  show ?thesis using denotation_type
    by (simp only: gi_exact_identity_test_denotation pp_e_dom_def gi_exact_domain_member)
qed

lemma gi_exact_identity_test_apply:
  assumes argument_member: "x \<in> gi_exact_domain \<sigma>"
  shows "gi_exact_app \<sigma> Prop (gi_exact_identity_test \<sigma> a) x =
    pp_e_prop (\<lambda>v. pp_e_eqv \<sigma> v x a)"
  using argument_member
  by (simp add: gi_exact_app_def gi_exact_identity_test_def Lambda_app)

lemma gi_exact_identity_test_truth:
  assumes argument_member: "x \<in> gi_exact_domain \<sigma>"
  shows "gi_exact_valuation w
      (gi_exact_app \<sigma> Prop (gi_exact_identity_test \<sigma> a) x) =
    pp_e_eqv \<sigma> w x a"
  apply (simp only: gi_exact_identity_test_apply[OF argument_member])
  by (simp add: gi_exact_valuation_def)

section \<open>Leibniz equivalence is precisely local identity\<close>

lemma gi_exact_local_identity_implies_leibniz:
  assumes left_member: "a \<in> gi_exact_domain \<sigma>"
    and right_member: "b \<in> gi_exact_domain \<sigma>"
    and local_identity: "pp_e_eqv \<sigma> w a b"
  shows "book_leibniz_equiv gi_exact_domain gi_exact_app
    (gi_exact_valuation w) \<sigma> a b"
proof (rule book_leibniz_equivI[where D=gi_exact_domain and app=gi_exact_app
    and V="gi_exact_valuation w" and \<sigma>=\<sigma> and a=a and b=b,
    OF left_member right_member])
  fix f
  assume predicate_member: "f \<in> gi_exact_domain (Arr \<sigma> Prop)"
  have exact_f: "Elem f (pp_e_domain (Arr \<sigma> Prop))"
    using predicate_member by (simp only: gi_exact_domain_member)
  have exact_a: "Elem a (pp_e_domain \<sigma>)"
    using left_member by (simp only: gi_exact_domain_member)
  have exact_b: "Elem b (pp_e_domain \<sigma>)"
    using right_member by (simp only: gi_exact_domain_member)
  have reflexive_f: "pp_e_eqv (Arr \<sigma> Prop) w f f"
    by (rule pp_e_eqv_reflexive[OF exact_f])
  have applications_related: "pp_e_eqv Prop w (f \<acute> a) (f \<acute> b)"
    by (rule pp_e_app_respects[OF reflexive_f exact_a exact_b local_identity])
  have current_world: "prefix w w" by simp
  have same_truth: "pp_e_holds (f \<acute> a) w \<longleftrightarrow> pp_e_holds (f \<acute> b) w"
    by (rule pp_e_prop_eqv_at[OF applications_related current_world])
  show "gi_exact_valuation w (gi_exact_app \<sigma> Prop f a) =
      gi_exact_valuation w (gi_exact_app \<sigma> Prop f b)"
    using same_truth by (simp only: gi_exact_valuation_def gi_exact_app_value)
qed

lemma gi_exact_leibniz_implies_local_identity:
  assumes equivalent: "book_leibniz_equiv gi_exact_domain gi_exact_app
    (gi_exact_valuation w) \<sigma> a b"
  shows "pp_e_eqv \<sigma> w a b"
proof -
  have left_member: "a \<in> gi_exact_domain \<sigma>"
    by (rule book_leibniz_left[OF equivalent])
  have right_member: "b \<in> gi_exact_domain \<sigma>"
    by (rule book_leibniz_right[OF equivalent])
  have exact_a: "Elem a (pp_e_domain \<sigma>)"
    using left_member by (simp only: gi_exact_domain_member)
  have exact_b: "Elem b (pp_e_domain \<sigma>)"
    using right_member by (simp only: gi_exact_domain_member)
  have test_member: "gi_exact_identity_test \<sigma> a \<in> gi_exact_domain (Arr \<sigma> Prop)"
    by (rule gi_exact_identity_test_member[OF left_member])
  have same_test:
      "gi_exact_valuation w (gi_exact_app \<sigma> Prop (gi_exact_identity_test \<sigma> a) a) =
       gi_exact_valuation w (gi_exact_app \<sigma> Prop (gi_exact_identity_test \<sigma> a) b)"
    by (rule book_leibniz_test[OF equivalent test_member])
  have same_relation: "pp_e_eqv \<sigma> w a a = pp_e_eqv \<sigma> w b a"
    using same_test
    by (simp only: gi_exact_identity_test_truth[OF left_member]
        gi_exact_identity_test_truth[OF right_member])
  have reflexive_a: "pp_e_eqv \<sigma> w a a"
    by (rule pp_e_eqv_reflexive[OF exact_a])
  have reverse_relation: "pp_e_eqv \<sigma> w b a"
    using same_relation reflexive_a by blast
  show ?thesis by (rule pp_e_eqv_symmetric[OF exact_b exact_a reverse_relation])
qed

theorem gi_exact_leibniz_iff_local_identity:
  assumes left_member: "a \<in> gi_exact_domain \<sigma>"
    and right_member: "b \<in> gi_exact_domain \<sigma>"
  shows "book_leibniz_equiv gi_exact_domain gi_exact_app
      (gi_exact_valuation w) \<sigma> a b \<longleftrightarrow>
    pp_e_eqv \<sigma> w a b"
proof
  assume equivalent: "book_leibniz_equiv gi_exact_domain gi_exact_app
    (gi_exact_valuation w) \<sigma> a b"
  show "pp_e_eqv \<sigma> w a b"
    by (rule gi_exact_leibniz_implies_local_identity[OF equivalent])
next
  assume local_identity: "pp_e_eqv \<sigma> w a b"
  show "book_leibniz_equiv gi_exact_domain gi_exact_app
    (gi_exact_valuation w) \<sigma> a b"
    by (rule gi_exact_local_identity_implies_leibniz[
      OF left_member right_member local_identity])
qed

corollary gi_exact_leibniz_iff_action_identity:
  assumes left_member: "a \<in> gi_exact_domain \<sigma>"
    and right_member: "b \<in> gi_exact_domain \<sigma>"
  shows "book_leibniz_equiv gi_exact_domain gi_exact_app
      (gi_exact_valuation w) \<sigma> a b \<longleftrightarrow>
    pp_b_action \<sigma> (rev w) a = pp_b_action \<sigma> (rev w) b"
proof -
  have exact_a: "Elem a (pp_e_domain \<sigma>)"
    using left_member by (simp only: gi_exact_domain_member)
  have exact_b: "Elem b (pp_e_domain \<sigma>)"
    using right_member by (simp only: gi_exact_domain_member)
  show ?thesis
    by (simp only: gi_exact_leibniz_iff_local_identity[OF left_member right_member]
        pp_e_eqv_iff_action_eq[OF exact_a exact_b])
qed

corollary gi_exact_root_leibniz_iff_equality:
  assumes left_member: "a \<in> gi_exact_domain \<sigma>"
    and right_member: "b \<in> gi_exact_domain \<sigma>"
  shows "book_leibniz_equiv gi_exact_domain gi_exact_app
    (gi_exact_valuation []) \<sigma> a b \<longleftrightarrow> a = b"
proof -
  have exact_a: "Elem a (pp_e_domain \<sigma>)"
    using left_member by (simp only: gi_exact_domain_member)
  have exact_b: "Elem b (pp_e_domain \<sigma>)"
    using right_member by (simp only: gi_exact_domain_member)
  show ?thesis
    by (simp only: gi_exact_leibniz_iff_action_identity[OF left_member right_member]
        rev.simps pp_b_action_one_all[OF exact_a] pp_b_action_one_all[OF exact_b])
qed

text \<open>
  The characterization is uniform in the represented object type σ and
  world w. Global HOL–ZF equality appears only in the root corollary,
  where the empty-word action is the identity. No assertion that the pure
  logical stock contains the separating predicate is needed: the book's
  Leibniz condition tests all values in Dσ→t, not merely Pure values.
\<close>

end
