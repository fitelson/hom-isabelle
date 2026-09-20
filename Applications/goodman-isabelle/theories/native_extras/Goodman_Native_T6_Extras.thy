theory Goodman_Native_T6_Extras
  imports "Goodman_Integration_Individual.Goodman_T2a_Transfer"
begin

section \<open>Native operators and relations with explicit protected names\<close>

text \<open>
  These definitions are written directly in the named minimal language.
  None is defined as gi_to_book applied to an old formula. The existing
  native T2a builders supply reversibility, group membership and fun′.
  Reversibility requires a pure two-sided inverse; group membership also
  requires purity of the operator itself.

  The list ns protects the free names of the displayed arguments. The
  closed principles below supply the whole surrounding binder chart.
  The primitive correspondence lemmas use chart variables, so no false
  literal-renaming claim for arbitrary lambda-containing arguments is
  needed. All literal correspondences retain gi_goodman_names k.

  Material biconditional is spelled as (P→Q)∧(Q→P). This is not identity
  at type t. We retain this explicit abbreviation so its correspondence
  with the earlier constructor presentation is literal.
\<close>

definition gb_T6_iff where
  "gb_T6_iff G P Q = book_and G (book_imp P Q) (book_imp Q P)"

definition gb_T6_identity where "gb_T6_identity n = NLam n (NVar n)"
definition gb_T6_negation where "gb_T6_negation G n = NLam n (book_not G (NVar n))"
definition gb_T6_compose where
  "gb_T6_compose n F H = NLam n (NApp F (NApp H (NVar n)))"

definition gb_reversible_on_chart where
  "gb_reversible_on_chart G ns Z = gb_T2a_reversible G ns Z"
definition gb_group_member_on_chart where
  "gb_group_member_on_chart G ns Z = gb_T2a_group_member G ns Z"
definition gb_fun_prime_on_chart where
  "gb_fun_prime_on_chart G ns p = gb_T2a_fun_prime_on_chart G ns p"

definition gb_same_kind_on_chart where
  "gb_same_kind_on_chart G ns X Y =
    (let z = named_chart_fresh G ns gb_unary;
         p = named_chart_fresh G (z # ns) Prop
     in book_exists G z (book_and G (gb_group_member_on_chart G (z # ns) (NVar z))
       (book_leibniz G gb_unary X (gb_T6_compose p Y (NVar z)))))"

definition gb_strong_same_kind_on_chart where
  "gb_strong_same_kind_on_chart G ns X Y p q =
    (let z = named_chart_fresh G ns gb_unary;
         a = named_chart_fresh G (z # ns) Prop
     in book_exists G z (book_and G (gb_group_member_on_chart G (z # ns) (NVar z))
       (book_and G (book_leibniz G gb_unary X (gb_T6_compose a Y (NVar z)))
         (book_leibniz G Prop q (NApp (NVar z) p)))))"

definition gb_truth_preserving_on_chart where
  "gb_truth_preserving_on_chart G ns Z =
    (let p = named_chart_fresh G ns Prop
     in book_all G p (gb_T6_iff G (NApp Z (NVar p)) (NVar p)))"

definition gb_truth_flipping_on_chart where
  "gb_truth_flipping_on_chart G ns Z =
    (let p = named_chart_fresh G ns Prop
     in book_all G p (gb_T6_iff G (NApp Z (NVar p)) (book_not G (NVar p))))"

definition gb_biconditional_builder_on_chart where
  "gb_biconditional_builder_on_chart G ns =
    (let a = named_chart_fresh G ns Prop;
         p = named_chart_fresh G (a # ns) Prop
     in NLam a (NLam p (gb_T6_iff G (NVar p) (NVar a))))"

definition gb_biconditional_operator_on_chart where
  "gb_biconditional_operator_on_chart G ns A = NApp (gb_biconditional_builder_on_chart G ns) A"

definition gb_biconditional_member_on_chart where
  "gb_biconditional_member_on_chart G ns Z =
    (let a = named_chart_fresh G ns Prop
     in book_exists G a (book_and G (gb_pure Prop (NVar a))
       (book_leibniz G gb_unary Z (gb_biconditional_operator_on_chart G (a # ns) (NVar a)))))"

section \<open>L2 and its strong version\<close>

definition gb_T6_L2_guard where
  "gb_T6_L2_guard G ns X Y p q =
    book_and G (gb_pure gb_unary X)
      (book_and G (gb_pure gb_unary Y)
        (book_and G (gb_fun_prime_on_chart G ns p)
          (book_and G (gb_fun_prime_on_chart G ns q)
            (book_leibniz G Prop (NApp X p) (NApp Y q)))))"

definition gb_L2 where
  "gb_L2 G =
    (let x = named_chart_fresh G [] gb_unary;
         y = named_chart_fresh G [x] gb_unary;
         p = named_chart_fresh G [y,x] Prop;
         q = named_chart_fresh G [p,y,x] Prop;
         ns = [q,p,y,x]
     in book_all G x (book_all G y (book_all G p (book_all G q
       (book_imp (gb_T6_L2_guard G ns (NVar x) (NVar y) (NVar p) (NVar q))
         (gb_same_kind_on_chart G ns (NVar x) (NVar y)))))))"

definition gb_strong_L2 where
  "gb_strong_L2 G =
    (let x = named_chart_fresh G [] gb_unary;
         y = named_chart_fresh G [x] gb_unary;
         p = named_chart_fresh G [y,x] Prop;
         q = named_chart_fresh G [p,y,x] Prop;
         ns = [q,p,y,x]
     in book_all G x (book_all G y (book_all G p (book_all G q
       (book_imp (gb_T6_L2_guard G ns (NVar x) (NVar y) (NVar p) (NVar q))
         (gb_strong_same_kind_on_chart G ns (NVar x) (NVar y) (NVar p) (NVar q)))))))"

text \<open>
  The weak conclusion is ∃Z∈Group. X = Y∘Z: composition is on the input
  side. Strong L2 additionally requires q = Zp, with that orientation.
\<close>

definition gb_Inv where
  "gb_Inv G =
    (let z = named_chart_fresh G [] gb_unary;
         p = named_chart_fresh G [z] Prop
     in book_all G z (gb_T6_iff G (gb_group_member_on_chart G [z] (NVar z))
       (book_or G (book_leibniz G gb_unary (NVar z) (gb_T6_identity p))
         (book_leibniz G gb_unary (NVar z) (gb_T6_negation G p)))))"

definition gb_WI where
  "gb_WI G =
    (let z = named_chart_fresh G [] gb_unary
     in book_all G z (book_imp (gb_group_member_on_chart G [z] (NVar z))
       (gb_biconditional_member_on_chart G [z] (NVar z))))"

definition gb_TU where
  "gb_TU G =
    (let z = named_chart_fresh G [] gb_unary
     in book_all G z (book_imp (gb_group_member_on_chart G [z] (NVar z))
       (book_or G (gb_truth_preserving_on_chart G [z] (NVar z))
         (gb_truth_flipping_on_chart G [z] (NVar z)))))"

section \<open>Rigid specifications: an actual nonempty pure selector\<close>

definition gb_spec_instantiated_on_chart where
  "gb_spec_instantiated_on_chart G ns R =
    (let p = named_chart_fresh G ns Prop in book_exists G p (NApp R (NVar p)))"

definition gb_spec_only_fun_prime_on_chart where
  "gb_spec_only_fun_prime_on_chart G ns R =
    (let p = named_chart_fresh G ns Prop
     in book_all G p (book_imp (NApp R (NVar p)) (gb_fun_prime_on_chart G (p # ns) (NVar p))))"

definition gb_spec_rigid_on_chart where
  "gb_spec_rigid_on_chart G ns R =
    (let z = named_chart_fresh G ns gb_unary;
         p = named_chart_fresh G (z # ns) Prop;
         q = named_chart_fresh G (p # z # ns) Prop
     in book_all G z (book_all G p (book_all G q
       (book_imp
         (book_and G (gb_group_member_on_chart G (q # p # z # ns) (NVar z))
           (book_and G (NApp R (NVar p))
             (book_and G (NApp R (NVar q)) (book_leibniz G Prop (NVar q) (NApp (NVar z) (NVar p))))))
         (book_leibniz G Prop (NVar p) (NVar q))))))"

definition gb_rigid_specification_on_chart where
  "gb_rigid_specification_on_chart G ns R =
    book_and G (gb_pure gb_unary R)
      (book_and G (gb_spec_instantiated_on_chart G ns R)
        (book_and G (gb_spec_only_fun_prime_on_chart G ns R) (gb_spec_rigid_on_chart G ns R)))"

definition gb_RS where
  "gb_RS G =
    (let r = named_chart_fresh G [] gb_unary
     in book_exists G r (gb_rigid_specification_on_chart G [r] (NVar r)))"

text \<open>
  RS asserts a pure R with at least one instance, all instances fun′,
  and ∀Zpq. (Group(Z) ∧ R(p) ∧ R(q) ∧ q=Zp) → p=q. Both R-conditions
  and the existence clause are part of the formula. It does not assert
  that every fun′ proposition is selected or that R is itself fundamental.
\<close>

section \<open>Primitive literal correspondence on chart variables\<close>

lemma gi_T6_identity_native_translation:
  "gi_to_book G ns k pp_identity_operator = gb_T6_identity (named_chart_fresh G ns Prop)"
  by (simp add: pp_identity_operator_def gb_T6_identity_def Let_def)

lemma gi_T6_negation_native_translation:
  "gi_to_book G ns k pp_negation_operator = gb_T6_negation G (named_chart_fresh G ns Prop)"
  by (simp add: pp_negation_operator_def gb_T6_negation_def Let_def)

lemma gi_T6_compose_variables_native_translation:
  "gi_to_book G ns k (pp_compose (Var i) (Var j)) =
    gb_T6_compose (named_chart_fresh G ns Prop) (NVar (ns ! i)) (NVar (ns ! j))"
  by (simp add: pp_compose_def gb_T6_compose_def shift_def Let_def)

lemma gi_T6_fun_prime_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_fun_prime (Var i)) = gb_fun_prime_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_fun_prime_def gb_fun_prime_on_chart_def gb_T2a_fun_prime_on_chart_def
      gb_fun_prime_with_names_def pp_unary_ty_def gi_pure_translation Let_def
      shift_by_def shift_ren_def numeral_2_eq_2)

lemma gi_T6_reversible_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_reversible (Var i)) = gb_reversible_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_reversible_def pp_compose_def pp_identity_operator_def
      gb_reversible_on_chart_def gb_T2a_reversible_def pp_unary_ty_def
      gi_pure_translation Let_def shift_def)

lemma gi_T6_group_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_group_member (Var i)) = gb_group_member_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_group_member_def gb_group_member_on_chart_def gb_T2a_group_member_def
      gi_T6_reversible_variable_native_translation gb_reversible_on_chart_def gi_pure_translation pp_unary_ty_def)

lemma gi_T6_same_kind_variables_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_same_kind (Var i) (Var j)) =
      gb_same_kind_on_chart G ns (NVar (ns ! i)) (NVar (ns ! j))"
  by (simp add: pp_same_kind_def gb_same_kind_on_chart_def pp_compose_def gb_T6_compose_def
      gi_T6_group_variable_native_translation pp_unary_ty_def shift_def Let_def)

lemma gi_T6_strong_kind_variables_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_strong_same_kind (Var i) (Var j) (Var a) (Var b)) =
      gb_strong_same_kind_on_chart G ns (NVar (ns ! i)) (NVar (ns ! j)) (NVar (ns ! a)) (NVar (ns ! b))"
  by (simp add: pp_strong_same_kind_def gb_strong_same_kind_on_chart_def pp_compose_def gb_T6_compose_def
      gi_T6_group_variable_native_translation pp_unary_ty_def shift_def Let_def)

lemma gi_T6_truth_preserving_variable_native_translation:
  "gi_to_book G ns k (pp_truth_preserving (Var i)) = gb_truth_preserving_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_truth_preserving_def gb_truth_preserving_on_chart_def gb_T6_iff_def shift_def Let_def)

lemma gi_T6_truth_flipping_variable_native_translation:
  "gi_to_book G ns k (pp_truth_flipping (Var i)) = gb_truth_flipping_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_truth_flipping_def gb_truth_flipping_on_chart_def gb_T6_iff_def shift_def Let_def)

lemma gi_T6_biconditional_builder_native_translation:
  "gi_to_book G ns k pp_biconditional_builder = gb_biconditional_builder_on_chart G ns"
  by (simp add: pp_biconditional_builder_def gb_biconditional_builder_on_chart_def gb_T6_iff_def Let_def)

lemma gi_T6_biconditional_operator_variable_native_translation:
  "gi_to_book G ns k (pp_biconditional_operator (Var i)) = gb_biconditional_operator_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_biconditional_operator_def gb_biconditional_operator_on_chart_def gi_T6_biconditional_builder_native_translation)

lemma gi_T6_biconditional_member_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_biconditional_member (Var i)) = gb_biconditional_member_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_biconditional_member_def gb_biconditional_member_on_chart_def gi_pure_translation
      gi_T6_biconditional_operator_variable_native_translation pp_unary_ty_def shift_def Let_def)

lemma gi_T6_spec_instantiated_variable_native_translation:
  "gi_to_book G ns k (pp_spec_instantiated (Var i)) = gb_spec_instantiated_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_spec_instantiated_def gb_spec_instantiated_on_chart_def shift_def Let_def)

lemma gi_T6_spec_only_fun_prime_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_spec_only_fun_prime (Var i)) = gb_spec_only_fun_prime_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_spec_only_fun_prime_def gb_spec_only_fun_prime_on_chart_def
      gi_T6_fun_prime_variable_native_translation shift_def Let_def)

lemma gi_T6_spec_rigid_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_spec_rigid (Var i)) = gb_spec_rigid_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_spec_rigid_def gb_spec_rigid_on_chart_def
      gi_T6_group_variable_native_translation pp_unary_ty_def shift_def Let_def numeral_2_eq_2)

lemma gi_T6_rigid_specification_variable_native_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_rigid_specification (Var i)) = gb_rigid_specification_on_chart G ns (NVar (ns ! i))"
  by (simp add: pp_rigid_specification_def gb_rigid_specification_on_chart_def gi_pure_translation pp_unary_ty_def
      gi_T6_spec_instantiated_variable_native_translation gi_T6_spec_only_fun_prime_variable_native_translation
      gi_T6_spec_rigid_variable_native_translation)

section \<open>Closed principles agree literally with their original encodings\<close>

theorem gi_L2_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_L2 = gb_L2 G"
  by (simp add: pp_L2_def gb_L2_def gb_T6_L2_guard_def pp_unary_ty_def gi_pure_translation
      gi_T6_fun_prime_variable_native_translation gi_T6_same_kind_variables_native_translation Let_def)

theorem gi_strong_L2_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_strong_L2 = gb_strong_L2 G"
  by (simp add: pp_strong_L2_def gb_strong_L2_def gb_T6_L2_guard_def pp_unary_ty_def gi_pure_translation
      gi_T6_fun_prime_variable_native_translation gi_T6_strong_kind_variables_native_translation Let_def)

theorem gi_Inv_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_Inv = gb_Inv G"
  by (simp add: pp_Inv_def gb_Inv_def gb_T6_iff_def pp_unary_ty_def
      gi_T6_group_variable_native_translation gi_T6_identity_native_translation gi_T6_negation_native_translation Let_def)

theorem gi_WI_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_WI = gb_WI G"
  by (simp add: pp_WI_def gb_WI_def pp_unary_ty_def
      gi_T6_group_variable_native_translation gi_T6_biconditional_member_variable_native_translation Let_def)

theorem gi_TU_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_TU = gb_TU G"
  by (simp add: pp_TU_def gb_TU_def pp_unary_ty_def
      gi_T6_group_variable_native_translation gi_T6_truth_preserving_variable_native_translation
      gi_T6_truth_flipping_variable_native_translation Let_def)

theorem gi_RS_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_RS = gb_RS G"
  by (simp add: pp_RS_def gb_RS_def pp_unary_ty_def gi_T6_rigid_specification_variable_native_translation Let_def)

section \<open>Declared-signature typing and closedness of the six principles\<close>

lemma gi_native_T6_extra_language_closed:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> M : Prop"
    and admitted: "\<And>k. gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature M"
    and correspondence: "\<And>k. gi_goodman_names k \<Longrightarrow> gi_to_book G [] k M = B"
  shows "book_theory_formula gb_signature G B" and "named_fv B = {}"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have language: "book_theory_formula gb_signature G (gi_to_book G [] k M)"
    by (rule gi_to_book_language[OF rich typed _ admitted[OF names]]; simp)
  have closed_term: "named_fv (gi_to_book G [] k M) = {}"
    by (rule gi_closed_translation[OF rich typed])
  show "book_theory_formula gb_signature G B" using language by (simp only: correspondence[OF names])
  show "named_fv B = {}" using closed_term by (simp only: correspondence[OF names])
qed

lemma gb_L2_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_L2 G)" and "named_fv (gb_L2 G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_L2 and B="gb_L2 G",
    OF rich typed_pp_L2 gi_L2_admitted gi_L2_native_translation] by blast+

lemma gb_strong_L2_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_strong_L2 G)" and "named_fv (gb_strong_L2 G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_strong_L2 and B="gb_strong_L2 G",
    OF rich typed_pp_strong_L2 gi_strong_L2_admitted gi_strong_L2_native_translation] by blast+

lemma gb_Inv_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_Inv G)" and "named_fv (gb_Inv G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_Inv and B="gb_Inv G",
    OF rich typed_pp_Inv gi_Inv_admitted gi_Inv_native_translation] by blast+

lemma gb_WI_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_WI G)" and "named_fv (gb_WI G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_WI and B="gb_WI G",
    OF rich typed_pp_WI gi_WI_admitted gi_WI_native_translation] by blast+

lemma gb_TU_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_TU G)" and "named_fv (gb_TU G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_TU and B="gb_TU G",
    OF rich typed_pp_TU gi_TU_admitted gi_TU_native_translation] by blast+

lemma gb_RS_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_RS G)" and "named_fv (gb_RS G) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M=pp_RS and B="gb_RS G",
    OF rich typed_pp_RS gi_RS_admitted gi_RS_native_translation] by blast+

text \<open>
  Each extra principle now has an independent named definition, a literal
  correspondence to its precise earlier encoding, and a declared-signature
  typing/closedness certificate under a rich variable stock. The preserved
  distinctions are: group versus mere reversibility; input-side composition;
  material truth-uniformity versus proposition identity; the q=Zp strong-L2
  direction; and the complete nonempty rigid-specification witness.
  These are encoding correspondences, not new proofs of the extra axioms
  from PP and not new semantic model claims.
\<close>

end
