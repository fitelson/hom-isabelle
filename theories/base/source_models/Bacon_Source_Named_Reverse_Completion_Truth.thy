theory Bacon_Source_Named_Reverse_Completion_Truth
  imports Bacon_Source_Named_Reverse_Open_Truth
begin

section \<open>Recovering every adequate partial named assignment\<close>

text \<open>
  Complete a typed partial assignment g to a total typed h. Interpret the
  source encoding using ρ(i) = ⟨G(i),h(i)⟩ in a prefix covering FV(A).
  The reverse value is exactly ⟨τ,⟦A⟧ᵍ⟩. Source role: adequate partial
  assignments and locality in Bacon–Dorr Definition 3.1, pp.43–44.

  The finite assignment may discard other values of g, and h may assign
  previously undefined names. Only agreement on FV(A) is used. This
  theorem is uniform over all such completions; it does not require
  equality of whole assignments or a chosen global assignment as an
  additional model field.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_reverse_completion_denote:
  assumes language: "named_in_language paper_logical_type signature stock A \<tau>"
    and bound: "source_free_bound (named_to_source stock [] A) \<le> m"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and completion: "named_completion domain stock g h"
  shows "named_erased_denote stock model_tag_denote (\<lambda>n. (stock n, h n)) (named_to_source stock [] A) =
    (\<tau>, denote g A)"
proof -
  let ?\<rho> = "\<lambda>n. (stock n, h n)"
  let ?q = "named_untag_assignment (named_prefix_assignment m ?\<rho>)"
  have env: "pbbk_env_typed (named_tag_domain domain) (source_prefix stock m) ?\<rho>"
    by (rule named_tagged_prefix_env_from_completion[OF completion])
  have support: "named_fv A \<subseteq> {..<m}"
  proof
    fix n
    assume free: "n \<in> named_fv A"
    show "n \<in> {..<m}" using named_prefix_free_name[OF bound free] by simp
  qed
  have qt: "named_env_typed domain stock ?q" by (rule named_untagged_prefix_typed[OF env])
  have qa: "named_adequate ?q A" by (rule named_untagged_prefix_adequate[OF support])
  have agree: "?q n = g n" if "n \<in> named_fv A" for n
    by (rule named_prefix_completion_fv_agree[OF completion adequate support that])
  have payload: "denote ?q A = denote g A"
    by (rule denote_locality[OF language qt typed qa adequate agree])
  show ?thesis by (simp only: paper_named_reverse_prefix_denote[OF language bound env] payload)
qed

corollary paper_named_reverse_completion_truth:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and bound: "source_free_bound (named_to_source stock [] A) \<le> m"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and completion: "named_completion domain stock g h"
  shows "model_tag_valuation (named_erased_denote stock model_tag_denote (\<lambda>n. (stock n, h n))
    (named_to_source stock [] A)) = valuation (denote g A)"
  by (simp only: paper_named_reverse_completion_denote[OF language bound typed adequate completion]
    model_tag_valuation_def snd_conv)

end

end
