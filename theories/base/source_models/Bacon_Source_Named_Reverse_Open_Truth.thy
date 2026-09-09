theory Bacon_Source_Named_Reverse_Open_Truth
  imports Bacon_Source_Named_Reverse_Closed_Truth Bacon_Source_Named_Prefix_Assignments
begin

section \<open>Open named values under corresponding finite assignments\<close>

text \<open>
  Let Γ be the length-m prefix of the fixed variable stock G, with m
  covering every free name of A. A tagged Γ-environment ρ gives a finite
  partial named assignment by taking the payload at each name below m.
  In the reverse model, the encoding of A denotes the tagged original
  value under this assignment. Source role: adequate assignments and
  locality in Bacon–Dorr Definition 3.1, pp.43–44.

  The assignment need not cover all variables of the language. Decoding
  the encoding gives an α-variant of A, not necessarily the same raw term.
  The finite environment is typed only on Γ; no condition is imposed on
  its values beyond that frame. This is denotation/truth transport, not
  named H proof preservation or a value-recovering model isomorphism.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_reverse_prefix_denote:
  assumes language: "named_in_language paper_logical_type signature stock A \<tau>"
    and bound: "source_free_bound (named_to_source stock [] A) \<le> m"
    and env: "pbbk_env_typed (named_tag_domain domain) (source_prefix stock m) \<rho>"
  shows "named_erased_denote stock model_tag_denote \<rho> (named_to_source stock [] A) =
    (\<tau>, denote (named_untag_assignment (named_prefix_assignment m \<rho>)) A)"
proof -
  let ?E = "named_to_source stock [] A"
  let ?B = "source_to_named stock [0..<m] ?E"
  let ?q = "named_untag_assignment (named_prefix_assignment m \<rho>)"
  have source_language: "sterm_in_language paper_logical_type signature (source_prefix stock m) ?E \<tau>"
    by (rule named_encoding_prefix_language[OF language bound])
  have decoded_language: "named_in_language paper_logical_type signature stock ?B \<tau>"
    by (rule source_to_named_language[OF source_language named_identity_prefix_chart stock_rich])
  have alpha: "named_alpha stock ?B A" by (rule named_prefix_roundtrip_alpha[OF language bound stock_rich])
  have support: "named_fv A \<subseteq> {..<m}"
  proof
    fix n
    assume free: "n \<in> named_fv A"
    show "n \<in> {..<m}" using named_prefix_free_name[OF bound free] by simp
  qed
  have qt: "named_env_typed domain stock ?q" by (rule named_untagged_prefix_typed[OF env])
  have qa: "named_adequate ?q A" by (rule named_untagged_prefix_adequate[OF support])
  have qb: "named_adequate ?q ?B"
    using qa named_alpha_fv[OF alpha] unfolding named_adequate_def by simp
  have payload: "denote ?q ?B = denote ?q A"
    by (rule paper_named_alpha_denote[OF alpha decoded_language qt qb])
  have erased: "named_erased_denote stock model_tag_denote \<rho> ?E =
    model_tag_denote (named_prefix_assignment m \<rho>) ?B"
    using named_erased_denote_agrees[OF model_type_tagging source_language env named_identity_prefix_chart]
    by (simp only: named_prefix_assignment_def)
  show ?thesis by (simp only: erased model_tag_denote_eq[OF decoded_language] payload)
qed

corollary paper_named_reverse_prefix_truth:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and bound: "source_free_bound (named_to_source stock [] A) \<le> m"
    and env: "pbbk_env_typed (named_tag_domain domain) (source_prefix stock m) \<rho>"
  shows "model_tag_valuation (named_erased_denote stock model_tag_denote \<rho> (named_to_source stock [] A)) =
    valuation (denote (named_untag_assignment (named_prefix_assignment m \<rho>)) A)"
  by (simp only: paper_named_reverse_prefix_denote[OF language bound env] model_tag_valuation_def snd_conv)

end

end
