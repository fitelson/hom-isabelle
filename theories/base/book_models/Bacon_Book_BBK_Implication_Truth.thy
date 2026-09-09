theory Bacon_Book_BBK_Implication_Truth
  imports Bacon_Book_BBK_Logical_Values
begin

section \<open>The closed primitive-implication value has material truth conditions\<close>

text \<open>
  For p,q ∈ Dt, V(App(App(κ(→),p),q)) = (V(p) → V(q)).
  Represent p and q by slots 1 and 0 in [t,t]. The existing typed
  β conversion sends the saturated closed implication wrapper to
  PImp(Var 1,Var 0), whose truth clause is a BBK field.
  Source role: constructing the implication clause of Bacon's
  Definition 15.1, pp.314–315, from the separate target interpretation.

  Status: this is in pbbk_model, with explicit finite typing and
  signature guards. Neither a book model nor a full environment,
  Functionality, or identity premise is assumed. The wrapper contains
  primitive target PImp; no equality with the paper's λ-defined
  material operator is asserted.
\<close>

context pbbk_model
begin

theorem pbbk_book_implication_truth:
  assumes left: "p \<in> domain Prop" and right: "q \<in> domain Prop"
  shows "valuation (pbbk_book_app Prop Prop
    (pbbk_book_app Prop (Arr Prop Prop) (pbbk_book_logical_value SImp) p) q) =
    (valuation p \<longrightarrow> valuation q)"
proof -
  let ?\<Gamma> = "[Prop, Prop]"
  let ?g = "pbbk_extend q (pbbk_extend p (\<lambda>_. undefined))"
  let ?K = "book_minimal_logical_translation SImp :: 'c pterm"
  let ?R = "PApp (PApp ?K (PVar 1)) (PVar 0)"
  let ?I = "PImp (PVar 1) (PVar 0) :: 'c pterm"
  have first_env: "pbbk_env_typed domain [Prop] (pbbk_extend p (\<lambda>_. undefined))"
    by (rule pbbk_env_extend[where D=domain and \<sigma>=Prop, OF pbbk_env_empty left])
  have env: "pbbk_env_typed domain ?\<Gamma> ?g"
    by (rule pbbk_env_extend[OF first_env right])
  have lookup_one: "lookup ?\<Gamma> 1 = Some Prop" by (simp add: lookup_def)
  have lookup_zero: "lookup ?\<Gamma> 0 = Some Prop" by simp
  have one_type: "has_ptype ?\<Gamma> (PVar 1 :: 'c pterm) Prop"
    by (rule has_ptype.PVar[OF lookup_one])
  have zero_type: "has_ptype ?\<Gamma> (PVar 0 :: 'c pterm) Prop"
    by (rule has_ptype.PVar[OF lookup_zero])
  have one_names: "pterm_in_signature signature (PVar 1 :: 'c pterm)" by simp
  have zero_names: "pterm_in_signature signature (PVar 0 :: 'c pterm)" by simp
  have one_value: "denote ?g (PVar 1) = p"
    using denote_var[OF lookup_one env] by (simp add: One_nat_def)
  have zero_value: "denote ?g (PVar 0) = q"
    using denote_var[OF lookup_zero env] by simp
  have source_one: "sterm_in_language book_minimal_logical_type signature ?\<Gamma>
    (SVar 1 :: 'c book_minimal_term) Prop"
    unfolding sterm_in_language_def by (rule conjI) (rule has_stype.Var[OF lookup_one], simp)
  have source_zero: "sterm_in_language book_minimal_logical_type signature ?\<Gamma>
    (SVar 0 :: 'c book_minimal_term) Prop"
    unfolding sterm_in_language_def by (rule conjI) (rule has_stype.Var[OF lookup_zero], simp)
  have conversion: "pbeta_eta_equiv_in_signature signature ?\<Gamma> Prop ?R ?I"
    using book_imp_application[OF source_one source_zero] by (simp only: sterm_translation.simps)
  have k_type: "has_ptype ?\<Gamma> ?K (Arr Prop (Arr Prop Prop))"
    using book_minimal_logical_translation_type[where \<Gamma>="[Prop, Prop]" and l=SImp]
    by (simp only: book_minimal_logical_type.simps)
  have k_names: "pterm_in_signature signature ?K"
    by (rule book_minimal_logical_translation_signature)
  have first_type: "has_ptype ?\<Gamma> (PApp ?K (PVar 1)) (Arr Prop Prop)"
    by (rule has_ptype.PApp[OF k_type one_type])
  have first_names: "pterm_in_signature signature (PApp ?K (PVar 1))"
    using k_names one_names by simp
  have redex_names: "pterm_in_signature signature ?R"
    using first_names zero_names by simp
  have implication_names: "pterm_in_signature signature ?I"
    using one_names zero_names by simp
  have beta: "denote ?g ?R = denote ?g ?I"
    by (rule denote_beta_eta[OF conversion redex_names implication_names env])
  have k_value: "denote ?g ?K = pbbk_book_logical_value SImp"
    by (rule pbbk_book_logical_value_at)
  have first_app: "denote ?g (PApp ?K (PVar 1)) =
    pbbk_book_app Prop (Arr Prop Prop) (pbbk_book_logical_value SImp) p"
    using pbbk_book_app_represents[OF k_type one_type k_names one_names env]
    by (simp only: k_value one_value)
  have represented: "denote ?g ?R =
    pbbk_book_app Prop Prop
      (pbbk_book_app Prop (Arr Prop Prop) (pbbk_book_logical_value SImp) p) q"
    using pbbk_book_app_represents[OF first_type zero_type first_names zero_names env]
    by (simp only: first_app zero_value)
  have implication: "valuation (denote ?g ?I) = (valuation p \<longrightarrow> valuation q)"
    using valuation_imp[OF one_type zero_type one_names zero_names env]
    by (simp only: one_value zero_value)
  have redex_truth: "valuation (denote ?g ?R) = (valuation p \<longrightarrow> valuation q)"
    by (simp only: beta; rule implication)
  show ?thesis using redex_truth by (simp only: represented)
qed

end

end
