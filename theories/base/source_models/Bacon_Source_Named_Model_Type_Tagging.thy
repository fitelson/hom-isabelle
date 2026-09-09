theory Bacon_Source_Named_Model_Type_Tagging
  imports Bacon_Source_Named_Model_Tag_Assignments Bacon_Source_Named_BBK_Interface
begin

section \<open>Tagging an arbitrary independent named BBK model\<close>

text \<open>
  For a named BBK model M, define D′σ = {⟨σ,a⟩ | a ∈ Dσ},
  ⟦A⟧′ᵍ = ⟨type(A),⟦A⟧ᵘⁿᵗᵃᵍ⁽ᵍ⁾⟩, and V′⟨σ,a⟩ = V(a).
  Source: the typed collections and interpretation clauses of Bacon–Dorr
  Definition 3.1(i–ii), pp.43–44.

  Representation: this locale is paper_named_bbk_model, not the weak
  finite-frame structure. Only the generic tagging and assignment helpers
  are reused from the earlier construction. Equality of head tags recovers
  the arrow types before the output pair is reconstructed.

  Status: structural clauses of a new model on a changed carrier.
  Original domains may overlap. No full-function condition, Γ erasure,
  source encoding equation, or converse model correspondence is assumed.
\<close>

context paper_named_bbk_model
begin

definition model_tag_denote ::
  "(otype \<times> 'v) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> (otype \<times> 'v)" where
  "model_tag_denote g A =
    (named_type_of paper_logical_type stock A, denote (named_untag_assignment g) A)"

definition model_tag_valuation :: "(otype \<times> 'v) \<Rightarrow> bool" where
  "model_tag_valuation v = valuation (snd v)"

lemma model_tag_denote_eq:
  assumes language: "named_in_language paper_logical_type signature stock A \<sigma>"
  shows "model_tag_denote g A = (\<sigma>, denote (named_untag_assignment g) A)"
  by (simp only: model_tag_denote_def named_type_of_language[OF language])

lemma model_tag_truth:
  "model_tag_valuation (model_tag_denote g A) =
    valuation (denote (named_untag_assignment g) A)"
  by (simp only: model_tag_valuation_def model_tag_denote_def snd_conv)

lemma model_tag_denote_type:
  assumes language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and adequate: "named_adequate g A"
  shows "model_tag_denote g A \<in> named_tag_domain domain \<sigma>"
proof -
  have old_typed: "named_env_typed domain stock (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have member: "denote (named_untag_assignment g) A \<in> domain \<sigma>"
    by (rule denote_type[OF language old_typed old_adequate])
  show ?thesis by (simp only: model_tag_denote_eq[OF language] named_tag_domain_pair_iff;
    rule conjI[OF refl member])
qed

lemma model_tag_denote_var:
  assumes typed: "named_env_typed (named_tag_domain domain) stock g" and assigned: "g n = Some v"
  shows "model_tag_denote g (NVar n) = v"
proof -
  have member: "v \<in> named_tag_domain domain (stock n)" by (rule named_env_value[OF typed assigned])
  have tag: "fst v = stock n" by (rule named_tag_domain_fst[OF member])
  have old_typed: "named_env_typed domain stock (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_assigned: "named_untag_assignment g n = Some (snd v)"
    by (rule named_untag_assignment_value[where g=g and n=n and v=v, OF assigned])
  have payload: "denote (named_untag_assignment g) (NVar n) = snd v"
    by (rule denote_var[OF old_typed old_assigned])
  have ty: "named_type_of paper_logical_type stock (NVar n) = stock n"
    by (rule named_type_of_eq[OF has_ntype.Var])
  have pair_eq: "(stock n, snd v) = v" using tag by (cases v) simp
  show ?thesis by (simp only: model_tag_denote_def ty payload pair_eq)
qed

lemma model_tag_denote_application:
  assumes fl: "named_in_language paper_logical_type signature stock F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type signature stock A \<sigma>"
    and hl: "named_in_language paper_logical_type signature stock H (Arr \<upsilon> \<rho>)"
    and bl: "named_in_language paper_logical_type signature stock B \<upsilon>"
    and gt: "named_env_typed (named_tag_domain domain) stock g"
    and ht: "named_env_typed (named_tag_domain domain) stock h"
    and ga: "named_adequate g (NApp F A)" and ha: "named_adequate h (NApp H B)"
    and heads: "model_tag_denote g F = model_tag_denote h H"
    and args: "model_tag_denote g A = model_tag_denote h B"
  shows "model_tag_denote g (NApp F A) = model_tag_denote h (NApp H B)"
proof -
  have tags: "fst (model_tag_denote g F) = fst (model_tag_denote h H)"
    by (rule arg_cong[where f=fst, OF heads])
  have arrows: "Arr \<sigma> \<tau> = Arr \<upsilon> \<rho>"
    using tags by (simp only: model_tag_denote_eq[OF fl] model_tag_denote_eq[OF hl] fst_conv)
  have result_type: "\<tau> = \<rho>" using arrows by simp
  have old_heads: "denote (named_untag_assignment g) F = denote (named_untag_assignment h) H"
    using arg_cong[where f=snd, OF heads] by (simp only: model_tag_denote_def snd_conv)
  have old_args: "denote (named_untag_assignment g) A = denote (named_untag_assignment h) B"
    using arg_cong[where f=snd, OF args] by (simp only: model_tag_denote_def snd_conv)
  have old_ga: "named_adequate (named_untag_assignment g) (NApp F A)"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_ha: "named_adequate (named_untag_assignment h) (NApp H B)"
    by (rule iffD2[OF named_untag_assignment_adequate ha])
  have payload: "denote (named_untag_assignment g) (NApp F A) =
    denote (named_untag_assignment h) (NApp H B)"
    by (rule denote_application_cong[OF fl al hl bl named_untag_assignment_typed[OF gt]
      named_untag_assignment_typed[OF ht] old_ga old_ha old_heads old_args])
  have ft: "has_ntype paper_logical_type stock F (Arr \<sigma> \<tau>)"
    and at: "has_ntype paper_logical_type stock A \<sigma>"
    using fl al unfolding named_in_language_def by blast+
  have ht': "has_ntype paper_logical_type stock H (Arr \<upsilon> \<rho>)"
    and bt: "has_ntype paper_logical_type stock B \<upsilon>"
    using hl bl unfolding named_in_language_def by blast+
  have fa_type: "named_type_of paper_logical_type stock (NApp F A) = \<tau>"
    by (rule named_type_of_eq[OF has_ntype.App[OF ft at]])
  have hb_type: "named_type_of paper_logical_type stock (NApp H B) = \<rho>"
    by (rule named_type_of_eq[OF has_ntype.App[OF ht' bt]])
  show ?thesis by (simp only: model_tag_denote_def fa_type hb_type result_type payload)
qed

lemma model_tag_denote_locality:
  assumes language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and gt: "named_env_typed (named_tag_domain domain) stock g"
    and ht: "named_env_typed (named_tag_domain domain) stock h"
    and ga: "named_adequate g A" and ha: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "model_tag_denote g A = model_tag_denote h A"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_ha: "named_adequate (named_untag_assignment h) A"
    by (rule iffD2[OF named_untag_assignment_adequate ha])
  have old_agree: "named_untag_assignment g n = named_untag_assignment h n"
    if "n \<in> named_fv A" for n
    by (simp only: named_untag_assignment_def agree[OF that])
  have payload: "denote (named_untag_assignment g) A = denote (named_untag_assignment h) A"
    by (rule denote_locality[OF language named_untag_assignment_typed[OF gt]
      named_untag_assignment_typed[OF ht] old_ga old_ha old_agree])
  show ?thesis by (simp only: model_tag_denote_def payload)
qed

lemma model_tag_denote_beta_eta:
  assumes raw: "named_raw_beta_eta paper_logical_type stock \<sigma> A B"
    and al: "named_in_language paper_logical_type signature stock A \<sigma>"
    and bl: "named_in_language paper_logical_type signature stock B \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  shows "model_tag_denote g A = model_tag_denote g B"
proof -
  have old_ga: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have old_gb: "named_adequate (named_untag_assignment g) B"
    by (rule iffD2[OF named_untag_assignment_adequate gb])
  have payload: "denote (named_untag_assignment g) A = denote (named_untag_assignment g) B"
    by (rule denote_beta_eta[OF raw al bl named_untag_assignment_typed[OF typed] old_ga old_gb])
  show ?thesis by (simp only: model_tag_denote_eq[OF al] model_tag_denote_eq[OF bl] payload)
qed

end

end
