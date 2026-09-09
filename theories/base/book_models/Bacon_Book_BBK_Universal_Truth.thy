theory Bacon_Book_BBK_Universal_Truth
  imports Bacon_Book_BBK_Logical_Values
begin

section \<open>The translated universal value has the book's truth clause\<close>

text \<open>
  For every f ∈ Dσ→t, κ(∀σ) is true when applied to f exactly when
  f is true at every a ∈ Dσ. Source role: the universal clause of
  Bacon's Definition 15.1, pp.314–315, for the represented minimal basis.

  Representation. Interpret f by slot 0 in [σ→t]. The existing literal
  wrapper conversion reduces its application to ∀σ.(v₁v₀). Beneath
  that quantifier, the environment is exactly the two-slot environment
  defining pbbk_book_app. The only model premise is the original BBK
  model; no full book environment, Functionality, identity clause,
  closed representation of f, or different carrier is used.
\<close>

context pbbk_model
begin

theorem pbbk_book_forall_truth:
  assumes predicate_member: "f \<in> domain (Arr \<sigma> Prop)"
  shows "valuation (pbbk_book_app (Arr \<sigma> Prop) Prop (pbbk_book_logical_value (SBAll \<sigma>)) f) =
    (\<forall>a \<in> domain \<sigma>. valuation (pbbk_book_app \<sigma> Prop f a))"
proof -
  let ?\<Gamma> = "[Arr \<sigma> Prop]"
  let ?g = "pbbk_extend f (\<lambda>_. undefined)"
  let ?W = "book_minimal_logical_translation (SBAll \<sigma>) :: 'c pterm"
  let ?L = "PApp ?W (PVar 0)"
  let ?body = "PApp (PVar 1) (PVar 0) :: 'c pterm"
  let ?R = "PForall \<sigma> ?body"
  have empty_env: "pbbk_env_typed domain [] (\<lambda>_. undefined)" by (rule pbbk_env_empty)
  have env: "pbbk_env_typed domain ?\<Gamma> ?g"
    by (rule pbbk_env_extend[where D=domain and \<sigma>="Arr \<sigma> Prop", OF empty_env predicate_member])
  have slot: "lookup ?\<Gamma> 0 = Some (Arr \<sigma> Prop)" by simp
  have source_type: "has_stype book_minimal_logical_type ?\<Gamma> (SVar 0 :: 'c book_minimal_term) (Arr \<sigma> Prop)"
    by (rule has_stype.Var[OF slot])
  have source_names: "sterm_in_signature signature (SVar 0 :: 'c book_minimal_term)" by simp
  have source_language: "sterm_in_language book_minimal_logical_type signature ?\<Gamma> (SVar 0) (Arr \<sigma> Prop)"
    unfolding sterm_in_language_def by (rule conjI[OF source_type source_names])
  have conversion: "pbeta_eta_equiv_in_signature signature ?\<Gamma> Prop ?L ?R"
    using book_all_application[OF source_language] by (simp add: pshift_def)
  have wrapper_type: "has_ptype ?\<Gamma> ?W (Arr (Arr \<sigma> Prop) Prop)"
    using book_minimal_logical_translation_type[where \<Gamma>="?\<Gamma>" and l="SBAll \<sigma>"] by simp
  have variable_type: "has_ptype ?\<Gamma> (PVar 0 :: 'c pterm) (Arr \<sigma> Prop)"
    by (rule has_ptype.PVar[OF slot])
  have wrapper_names: "pterm_in_signature signature ?W" by (rule book_minimal_logical_translation_signature)
  have variable_names: "pterm_in_signature signature (PVar 0 :: 'c pterm)" by simp
  have left_names: "pterm_in_signature signature ?L" using wrapper_names variable_names by simp
  have right_names: "pterm_in_signature signature ?R" by simp
  have variable_value: "denote ?g (PVar 0) = f" using denote_var[OF slot env] by simp
  have represented: "denote ?g ?L = pbbk_book_app (Arr \<sigma> Prop) Prop (denote ?g ?W) (denote ?g (PVar 0))"
    by (rule pbbk_book_app_represents[OF wrapper_type variable_type wrapper_names variable_names env])
  have application: "denote ?g ?L = pbbk_book_app (Arr \<sigma> Prop) Prop (pbbk_book_logical_value (SBAll \<sigma>)) f"
    using represented by (simp only: pbbk_book_logical_value_at variable_value)
  have converted: "denote ?g ?L = denote ?g ?R"
    by (rule denote_beta_eta[OF conversion left_names right_names env])
  have left_value: "pbbk_book_app (Arr \<sigma> Prop) Prop (pbbk_book_logical_value (SBAll \<sigma>)) f = denote ?g ?R"
    by (rule trans[OF sym[OF application] converted])
  have body_type: "has_ptype (\<sigma> # ?\<Gamma>) ?body Prop"
    by (rule has_ptype.PApp[OF pbbk_book_app_head_type pbbk_book_app_argument_type])
  have body_names: "pterm_in_signature signature ?body" by simp
  have universal: "valuation (denote ?g ?R) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?g) ?body))"
    by (rule valuation_forall[OF body_type body_names env])
  have right_values: "(\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?g) ?body)) =
    (\<forall>a \<in> domain \<sigma>. valuation (pbbk_book_app \<sigma> Prop f a))"
    by (simp only: pbbk_book_app_def)
  have left_truth: "valuation (pbbk_book_app (Arr \<sigma> Prop) Prop (pbbk_book_logical_value (SBAll \<sigma>)) f) =
    valuation (denote ?g ?R)"
    by (rule arg_cong[where f=valuation, OF left_value])
  show ?thesis by (rule trans[OF left_truth trans[OF universal right_values]])
qed

end

end
