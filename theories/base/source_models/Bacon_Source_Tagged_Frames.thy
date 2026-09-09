theory Bacon_Source_Tagged_Frames
  imports Bacon_Source_Named_Type_Tags
begin

section \<open>Recovering a finite frame from typed value tags\<close>

text \<open>
  If ρ(i) ∈ D′σᵢ, where D′σ = {(σ,a) | a ∈ Dσ}, the first
  component of ρ(i) recovers σᵢ. Thus the first k tags recover the
  length-k prefix of every frame that types ρ.
  Source role: representation of the typed collections in Bacon–Dorr
  Definition 3.1(i–ii), pp.43–44.

  Isabelle representation. named_tagged_frame reads a chosen number of
  tags, whether or not their payloads are well typed. Its recovery theorems
  require pbbk_env_typed and retain the finite length bound. Nothing is
  assumed about payloads beyond the end of the given frame. The original
  domains may overlap and need not be nonempty for these implications.
  No model, denotation, chart independence, or Γ-erasure is claimed here.
\<close>

definition named_tagged_frame :: "(nat \<Rightarrow> otype \<times> 'v) \<Rightarrow> nat \<Rightarrow> ctx" where
  "named_tagged_frame \<rho> k = map (fst \<circ> \<rho>) [0..<k]"

lemma named_tagged_frame_length:
  "length (named_tagged_frame \<rho> k) = k"
  by (simp add: named_tagged_frame_def)

lemma named_tagged_frame_zero:
  "named_tagged_frame \<rho> 0 = []"
  by (simp add: named_tagged_frame_def)

lemma named_tagged_frame_nth:
  assumes bound: "i < k"
  shows "named_tagged_frame \<rho> k ! i = fst (\<rho> i)"
  using bound by (simp add: named_tagged_frame_def)

lemma named_tagged_frame_lookup:
  assumes bound: "i < k"
  shows "lookup (named_tagged_frame \<rho> k) i = Some (fst (\<rho> i))"
  by (simp add: lookup_def named_tagged_frame_length named_tagged_frame_nth[OF bound] bound)

subsection \<open>Pointwise membership determines the declared slot type\<close>

lemma named_tagged_member_type_unique:
  assumes first: "v \<in> named_tag_domain D \<sigma>" and second: "v \<in> named_tag_domain E \<tau>"
  shows "\<sigma> = \<tau>"
  by (rule trans[OF sym[OF named_tag_domain_fst[OF first]] named_tag_domain_fst[OF second]])

lemma named_tagged_member_frame_lookup:
  assumes member: "\<rho> i \<in> named_tag_domain D \<sigma>" and bound: "i < k"
  shows "lookup (named_tagged_frame \<rho> k) i = Some \<sigma>"
  by (simp only: named_tagged_frame_lookup[OF bound] named_tag_domain_fst[OF member])

lemma named_tagged_env_slot_type:
  assumes env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>" and slot: "lookup \<Gamma> i = Some \<sigma>"
  shows "fst (\<rho> i) = \<sigma>"
  by (rule named_tag_domain_fst[OF pbbk_env_lookup[OF env slot]])

lemma named_tagged_env_slot_payload:
  assumes env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>" and slot: "lookup \<Gamma> i = Some \<sigma>"
  shows "snd (\<rho> i) \<in> D \<sigma>"
  by (rule named_tag_domain_snd[OF pbbk_env_lookup[OF env slot]])

lemma named_tagged_env_nth_type:
  assumes env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>" and bound: "i < length \<Gamma>"
  shows "fst (\<rho> i) = \<Gamma> ! i"
proof -
  have slot: "lookup \<Gamma> i = Some (\<Gamma> ! i)" by (simp add: lookup_def bound)
  show ?thesis by (rule named_tagged_env_slot_type[OF env slot])
qed

subsection \<open>Exact prefix and whole-frame recovery\<close>

theorem named_tagged_frame_prefix:
  assumes env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>" and bound: "k \<le> length \<Gamma>"
  shows "named_tagged_frame \<rho> k = take k \<Gamma>"
proof (rule nth_equalityI)
  show "length (named_tagged_frame \<rho> k) = length (take k \<Gamma>)"
    by (simp add: named_tagged_frame_length bound)
next
  fix i
  assume index: "i < length (named_tagged_frame \<rho> k)"
  have before_k: "i < k" using index by (simp only: named_tagged_frame_length)
  have before_frame: "i < length \<Gamma>" by (rule less_le_trans[OF before_k bound])
  have selected: "named_tagged_frame \<rho> k ! i = fst (\<rho> i)"
    by (rule named_tagged_frame_nth[OF before_k])
  have original: "fst (\<rho> i) = \<Gamma> ! i" by (rule named_tagged_env_nth_type[OF env before_frame])
  have prefix: "take k \<Gamma> ! i = \<Gamma> ! i" by (simp add: before_k)
  show "named_tagged_frame \<rho> k ! i = take k \<Gamma> ! i"
    by (rule trans[OF selected trans[OF original sym[OF prefix]]])
qed

theorem named_tagged_frame_recover:
  assumes env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_tagged_frame \<rho> (length \<Gamma>) = \<Gamma>"
  using named_tagged_frame_prefix[OF env order_refl] by simp

corollary named_tagged_frames_same_length:
  assumes first: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
    and second: "pbbk_env_typed (named_tag_domain E) \<Delta> \<rho>"
    and lengths: "length \<Gamma> = length \<Delta>"
  shows "\<Gamma> = \<Delta>"
proof -
  have left: "named_tagged_frame \<rho> (length \<Gamma>) = \<Gamma>"
    by (rule named_tagged_frame_recover[OF first])
  have right: "named_tagged_frame \<rho> (length \<Gamma>) = \<Delta>"
    using named_tagged_frame_recover[OF second] by (simp only: lengths)
  show ?thesis by (rule trans[OF sym[OF left] right])
qed

end
