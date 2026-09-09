theory Bacon_Source_Chart_Quantifier_Instance
  imports Bacon_Source_Chart_Truth_Basics Bacon_Source_Named_Model_Vector_Denotation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Decoder_Eta
begin

section \<open>The extended chart interprets the fresh named quantifier instance\<close>

text \<open>
  Let F:σ → t in Γ, and let ns chart Γ. Choose a name x:σ outside
  ns. The extended chart interprets F↑ applied to slot zero exactly as
  the decoded F applied to x under g[x↦a], where g maps nsᵢ to ρ(i).
  Source: Bacon–Dorr Definition 3.1(iii.d–e), pp.43–44.

  Representation: decoding F↑ in x # ns is α-equivalent, not generally
  syntactically equal, to decoding F in ns. Lift this α-equivalence to
  application, use the arbitrary named model's derived α-denotation
  theorem, then apply the exact chart-assignment extension equation.
  Status: Γ, its chart, and all typing guards remain explicit. No weak
  finite-frame model, Functionality, or context-erasure premise is used.
\<close>

lemma chart_quantifier_body_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) (SApp (sshift F) (SVar 0)) Prop"
proof -
  have ft: "has_stype L \<Gamma> F (Arr \<sigma> Prop)"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have names: "sterm_in_signature \<Sigma> F"
    using language unfolding sterm_in_language_def by (rule conjunct2)
  have shifted: "has_stype L (\<sigma> # \<Gamma>) (sshift F) (Arr \<sigma> Prop)"
    by (rule sshift_preserves_typing[OF ft])
  have variable: "has_stype L (\<sigma> # \<Gamma>) (SVar 0) \<sigma>"
    by (rule has_stype.Var[OF lookup_Cons_0])
  have application: "has_stype L (\<sigma> # \<Gamma>) (SApp (sshift F) (SVar 0)) Prop"
    by (rule has_stype.App[OF shifted variable])
  have application_names: "sterm_in_signature \<Sigma> (SApp (sshift F) (SVar 0))"
    by (simp add: sshift_def srename_signature names)
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF application application_names])
qed

context paper_named_bbk_model
begin

theorem chart_quantifier_instance:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and chart: "named_chart stock \<Gamma> ns"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> set ns"
    and member: "a \<in> domain \<sigma>"
  shows "chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
    denote ((named_chart_assignment ns \<rho>)(n := Some a))
      (NApp (source_to_named stock ns F) (NVar n))"
proof -
  let ?X = "SApp (sshift F) (SVar 0)"
  let ?g = "named_chart_assignment (n # ns) (pbbk_extend a \<rho>)"
  have ft: "has_stype paper_logical_type \<Gamma> F (Arr \<sigma> Prop)"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have extended: "named_chart stock (\<sigma> # \<Gamma>) (n # ns)"
    by (rule named_chart_Cons[OF chart n_type fresh])
  have source_language: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) ?X Prop"
    by (rule chart_quantifier_body_language[OF language])
  have decoded_language: "named_in_language paper_logical_type signature stock
    (source_to_named stock (n # ns) ?X) Prop"
    by (rule source_to_named_language[OF source_language extended stock_rich])
  have extended_env: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)"
    by (rule pbbk_env_extend[OF env member])
  have typed_assignment: "named_env_typed domain stock ?g"
    by (rule named_chart_assignment_typed[OF extended extended_env])
  have adequate: "named_adequate ?g (source_to_named stock (n # ns) ?X)"
    by (rule chart_decoder_language_adequate[OF source_language extended])
  have head_alpha: "named_alpha stock (source_to_named stock (n # ns) (sshift F))
    (source_to_named stock ns F)"
    by (rule source_to_named_shift_alpha[OF ft chart extended stock_rich])
  have app_alpha: "named_alpha stock
    (NApp (source_to_named stock (n # ns) (sshift F)) (NVar n))
    (NApp (source_to_named stock ns F) (NVar n))"
    by (rule named_alpha.App[OF head_alpha named_alpha.Refl])
  have decoded_alpha: "named_alpha stock (source_to_named stock (n # ns) ?X)
    (NApp (source_to_named stock ns F) (NVar n))"
    using app_alpha by simp
  have same: "denote ?g (source_to_named stock (n # ns) ?X) =
    denote ?g (NApp (source_to_named stock ns F) (NVar n))"
    by (rule paper_named_alpha_denote[OF decoded_alpha decoded_language typed_assignment adequate])
  show ?thesis using same
    by (simp only: chart_denote_def named_chart_assignment_extend)
qed

end

end
