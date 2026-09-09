theory Bacon_Source_BBK_Pullback_Truth
  imports Bacon_Source_BBK_Interface Bacon_Source_Logical_Applications
begin

section \<open>Truth of first-class logical applications in the pullback\<close>

text \<open>
  Set ⟦A⟧S,g := ⟦tr(A)⟧T,g for a target BBK model T. Saturated
  logical constants have the truth clauses of Definition 3.1(iii).
  Each proof uses a guarded β computation followed by the corresponding
  target truth clause. This concerns arbitrary predicates, not merely
  closed logical predicates. No primitive implication identity is used.

  Status: the truth-clause part of a finite-frame interpretation pullback.
  The named-variable and adequate-assignment representation bridge is not
  asserted here, nor is a two-sided model isomorphism.
\<close>

context pbbk_model
begin

lemma paper_pullback_conversion_denotation:
  assumes conversion: "pbeta_eta_equiv_in_signature signature \<Gamma> \<sigma> (paper_to_pterm A) M"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "denote g (paper_to_pterm A) = denote g M"
proof -
  have data: "has_ptype \<Gamma> (paper_to_pterm A) \<sigma> \<and> has_ptype \<Gamma> M \<sigma> \<and>
      pterm_in_signature signature (paper_to_pterm A) \<and> pterm_in_signature signature M"
    by (rule pbeta_eta_equiv_in_signature_data[OF conversion])
  show ?thesis by (rule denote_beta_eta[OF conversion _ _ env]) (use data in blast)+
qed

lemma paper_pullback_neg:
  assumes A: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (paper_not A))) =
    (\<not> valuation (denote g (paper_to_pterm A)))"
proof -
  have lang: "pterm_in_language signature \<Gamma> (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A])
  have eq: "denote g (paper_to_pterm (paper_not A)) = denote g (PNeg (paper_to_pterm A))"
    unfolding paper_not_def by (rule paper_pullback_conversion_denotation[OF paper_not_application[OF A] env])
  have truth: "valuation (denote g (PNeg (paper_to_pterm A))) =
    (\<not> valuation (denote g (paper_to_pterm A)))"
    using lang env valuation_neg unfolding pterm_in_language_def by blast
  show ?thesis by (simp only: eq truth)
qed

lemma paper_pullback_conj:
  assumes A: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (paper_and A B))) =
    (valuation (denote g (paper_to_pterm A)) \<and> valuation (denote g (paper_to_pterm B)))"
proof -
  have langs: "pterm_in_language signature \<Gamma> (paper_to_pterm A) Prop"
    "pterm_in_language signature \<Gamma> (paper_to_pterm B) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A], rule iffD2[OF paper_to_pterm_language_iff B])
  have eq: "denote g (paper_to_pterm (paper_and A B)) =
    denote g (PConj (paper_to_pterm A) (paper_to_pterm B))"
    unfolding paper_and_def by (rule paper_pullback_conversion_denotation[OF paper_and_application[OF A B] env])
  have truth: "valuation (denote g (PConj (paper_to_pterm A) (paper_to_pterm B))) =
    (valuation (denote g (paper_to_pterm A)) \<and> valuation (denote g (paper_to_pterm B)))"
    using langs env valuation_conj unfolding pterm_in_language_def by blast
  show ?thesis by (simp only: eq truth)
qed

lemma paper_pullback_disj:
  assumes A: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (paper_or A B))) =
    (valuation (denote g (paper_to_pterm A)) \<or> valuation (denote g (paper_to_pterm B)))"
proof -
  have langs: "pterm_in_language signature \<Gamma> (paper_to_pterm A) Prop"
    "pterm_in_language signature \<Gamma> (paper_to_pterm B) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A], rule iffD2[OF paper_to_pterm_language_iff B])
  have eq: "denote g (paper_to_pterm (paper_or A B)) =
    denote g (PDisj (paper_to_pterm A) (paper_to_pterm B))"
    unfolding paper_or_def by (rule paper_pullback_conversion_denotation[OF paper_or_application[OF A B] env])
  have truth: "valuation (denote g (PDisj (paper_to_pterm A) (paper_to_pterm B))) =
    (valuation (denote g (paper_to_pterm A)) \<or> valuation (denote g (paper_to_pterm B)))"
    using langs env valuation_disj unfolding pterm_in_language_def by blast
  show ?thesis by (simp only: eq truth)
qed

lemma paper_pullback_identity:
  assumes A: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and B: "sterm_in_language paper_logical_type signature \<Gamma> B \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (SApp (SApp (SLogical (SEq \<sigma>)) A) B))) =
    (denote g (paper_to_pterm A) = denote g (paper_to_pterm B))"
proof -
  have langs: "pterm_in_language signature \<Gamma> (paper_to_pterm A) \<sigma>"
    "pterm_in_language signature \<Gamma> (paper_to_pterm B) \<sigma>"
    by (rule iffD2[OF paper_to_pterm_language_iff A], rule iffD2[OF paper_to_pterm_language_iff B])
  have eq: "denote g (paper_to_pterm (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) =
    denote g (PEq \<sigma> (paper_to_pterm A) (paper_to_pterm B))"
    by (rule paper_pullback_conversion_denotation[OF paper_eq_application[OF A B] env])
  have truth: "valuation (denote g (PEq \<sigma> (paper_to_pterm A) (paper_to_pterm B))) =
    (denote g (paper_to_pterm A) = denote g (paper_to_pterm B))"
    using langs env valuation_identity unfolding pterm_in_language_def by blast
  show ?thesis by (simp only: eq truth)
qed

lemma paper_pullback_forall:
  assumes F: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) F))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g)
      (paper_to_pterm (SApp (sshift F) (SVar 0)))))"
proof -
  let ?body = "PApp (pshift (paper_to_pterm F)) (PVar 0)"
  note conversion = paper_all_application[OF F]
  have eq: "denote g (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) F)) = denote g (PForall \<sigma> ?body)"
    by (rule paper_pullback_conversion_denotation[OF conversion env])
  have data: "has_ptype \<Gamma> (PForall \<sigma> ?body) Prop \<and> pterm_in_signature signature ?body"
    using pbeta_eta_equiv_in_signature_data[OF conversion] by auto
  have body: "has_ptype (\<sigma> # \<Gamma>) ?body Prop"
    using conjunct1[OF data] by (cases rule: has_ptype.cases) auto
  have truth: "valuation (denote g (PForall \<sigma> ?body)) =
      (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) ?body))"
    by (rule valuation_forall[OF body conjunct2[OF data] env])
  show ?thesis by (subst eq, subst truth)
    (simp only: sterm_translation.simps paper_to_pterm_shift)
qed

lemma paper_pullback_exists:
  assumes F: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) F))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g)
      (paper_to_pterm (SApp (sshift F) (SVar 0)))))"
proof -
  let ?body = "PApp (pshift (paper_to_pterm F)) (PVar 0)"
  note conversion = paper_ex_application[OF F]
  have eq: "denote g (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) F)) = denote g (PExists \<sigma> ?body)"
    by (rule paper_pullback_conversion_denotation[OF conversion env])
  have data: "has_ptype \<Gamma> (PExists \<sigma> ?body) Prop \<and> pterm_in_signature signature ?body"
    using pbeta_eta_equiv_in_signature_data[OF conversion] by auto
  have body: "has_ptype (\<sigma> # \<Gamma>) ?body Prop"
    using conjunct1[OF data] by (cases rule: has_ptype.cases) auto
  have truth: "valuation (denote g (PExists \<sigma> ?body)) =
      (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) ?body))"
    by (rule valuation_exists[OF body conjunct2[OF data] env])
  show ?thesis by (subst eq, subst truth)
    (simp only: sterm_translation.simps paper_to_pterm_shift)
qed

end

end
