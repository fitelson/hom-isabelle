theory Bacon_Source_ZF_Exponential_Transport
  imports Bacon_Source_ZF_Exponential_Codec Bacon_Source_ZF_Pair_Transport
begin

section \<open>Concrete precomposition of exponential function graphs\<close>

text \<open>
  Transport along f:W→V sends a graph F to the graph whose value
  at ⟨i,x⟩ is F⟨i∘f,x⟩. Source: Example 3.16(ii), p.54.
  The argument x is unchanged: it already lies at target(i).
  This differs from coherence, where a subsequent arrow also
  transports the argument.

  The graph is constructed by Lambda on the actual target pair
  code. No transport decoder is assumed, and all graph applications
  in the proof are guarded by membership in their pair domains.
\<close>

definition paper_ZF_exponential_transport_code ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_exponential_transport_code A source target compose X f F =
    Lambda (paper_ZF_pair_code A source target X (target f))
      (\<lambda>z. app F (Opair (compose (Fst z) f) (Snd z)))"

lemma paper_ZF_encode_exponential_graph:
  "paper_ZF_encode_exponential A source target X W b =
    Lambda (paper_ZF_pair_code A source target X W)
      (\<lambda>z. if Elem z (paper_ZF_pair_code A source target X W)
        then b (Fst z,Snd z) else undefined)"
proof -
  have body: "paper_ZF_flatten_pair_function (paper_ZF_outgoing_code A source W)
      (\<lambda>h. X (target h)) b =
    (\<lambda>z. if Elem z (paper_ZF_pair_code A source target X W)
      then b (Fst z,Snd z) else undefined)"
    by (rule ext, simp only: paper_ZF_flatten_pair_function_def paper_ZF_pair_code_def)
  show ?thesis by (simp only: paper_ZF_encode_exponential_def paper_ZF_encode_pair_function_def
    body paper_ZF_pair_code_def)
qed

theorem paper_ZF_encode_exponential_transport:
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and arrow: "f \<in> explode A"
  shows "paper_ZF_encode_exponential A source target X (target f)
      (paper_exponential_transport (explode A) source target compose (\<lambda>V. explode (X V)) f b) =
    paper_ZF_exponential_transport_code A source target compose X f
      (paper_ZF_encode_exponential A source target X (source f) b)"
proof -
  let ?D = "paper_ZF_pair_code A source target X (target f)"
  let ?T = "paper_exponential_transport (explode A) source target compose (\<lambda>V. explode (X V)) f b"
  let ?F = "paper_ZF_encode_exponential A source target X (source f) b"
  have bodies: "(if Elem z ?D then ?T (Fst z,Snd z) else undefined) =
      app ?F (Opair (compose (Fst z) f) (Snd z))" if member: "Elem z ?D" for z
  proof -
    have target_pair: "(Fst z,Snd z) \<in>
      paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) (target f)"
      by (rule paper_ZF_pair_code_decode_into[OF member])
    have source_pair: "Elem (Opair (compose (Fst z) f) (Snd z))
      (paper_ZF_pair_code A source target X (source f))"
      by (rule paper_ZF_pair_precompose_code[OF category arrow member])
    have transported: "?T (Fst z,Snd z) = b (compose (Fst z) f,Snd z)"
      by (rule paper_exponential_transport_on[OF target_pair])
    have encoded: "app ?F (Opair (compose (Fst z) f) (Snd z)) =
      b (compose (Fst z) f,Snd z)"
      by (rule paper_ZF_encode_exponential_value[OF source_pair])
    show ?thesis by (simp only: if_P[OF member] transported encoded)
  qed
  have equal: "Lambda ?D (\<lambda>z. if Elem z ?D then ?T (Fst z,Snd z) else undefined) =
    Lambda ?D (\<lambda>z. app ?F (Opair (compose (Fst z) f) (Snd z)))"
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI, rule bodies, assumption)
  show ?thesis using equal
    by (simp only: paper_ZF_encode_exponential_graph paper_ZF_exponential_transport_code_def)
qed

context paper_ZF_action_pair
begin

lemma paper_ZF_transport_as_encoded:
  assumes arrow: "f \<in> explode A"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  shows "paper_ZF_exponential_transport_code A source target compose X f F =
    paper_ZF_encode_exponential A source target X (target f)
      (exponential_transport f (paper_ZF_decode_exponential A source target X (source f) F))"
proof -
  have category: "paper_category objects (explode A) source target compose identity" by unfold_locales
  have encoded: "paper_ZF_encode_exponential A source target X (target f)
      (exponential_transport f (paper_ZF_decode_exponential A source target X (source f) F)) =
    paper_ZF_exponential_transport_code A source target compose X f
      (paper_ZF_encode_exponential A source target X (source f)
        (paper_ZF_decode_exponential A source target X (source f) F))"
    by (rule paper_ZF_encode_exponential_transport[OF category arrow])
  show ?thesis using encoded
    by (simp only: paper_ZF_encode_decode_exponential[OF member]; rule sym)
qed

theorem paper_ZF_exponential_transport_code_type:
  assumes arrow: "f \<in> explode A"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  shows "paper_ZF_exponential_transport_code A source target compose X f F \<in>
    explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (target f))"
proof -
  have decoded: "paper_ZF_decode_exponential A source target X (source f) F \<in> exponential_fiber (source f)"
    by (rule paper_ZF_decode_exponential_type[OF member])
  have transported: "exponential_transport f (paper_ZF_decode_exponential A source target X (source f) F)
      \<in> exponential_fiber (target f)"
    by (rule paper_exponential_transport_type[OF arrow decoded])
  show ?thesis
    by (simp only: paper_ZF_transport_as_encoded[OF arrow member],
      rule paper_ZF_encode_exponential_type[OF transported])
qed

theorem paper_ZF_decode_exponential_transport:
  assumes arrow: "f \<in> explode A"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  shows "paper_ZF_decode_exponential A source target X (target f)
      (paper_ZF_exponential_transport_code A source target compose X f F) =
    exponential_transport f (paper_ZF_decode_exponential A source target X (source f) F)"
proof -
  have decoded: "paper_ZF_decode_exponential A source target X (source f) F \<in> exponential_fiber (source f)"
    by (rule paper_ZF_decode_exponential_type[OF member])
  have transported: "exponential_transport f (paper_ZF_decode_exponential A source target X (source f) F)
      \<in> exponential_fiber (target f)"
    by (rule paper_exponential_transport_type[OF arrow decoded])
  show ?thesis by (simp only: paper_ZF_transport_as_encoded[OF arrow member],
    rule paper_ZF_decode_encode_exponential[OF transported])
qed

end

end
