theory Bacon_Source_ZF_Exponential_Action
  imports Bacon_Source_ZF_Exponential_Transport
begin

section \<open>The graph-valued exponential transport is an actual action\<close>

text \<open>
  The concrete function graphs satisfy 1W(F)=F and
  (g∘f)(F)=g(f(F)). Source: Example 3.16 and Definition 3.13,
  pp.53–54. The result follows from the generic exponential laws
  and the proved coding inverses, not from an assumed coded action.

  Representation: fibers are explode(paper_ZF_exponential_code … W),
  and transport is the actual Lambda precomposition graph. All equalities
  are guarded by legitimate arrows and coded source-fiber membership.
  Status: one concrete coded exponential action, relative to standard
  HOL-ZF; not a simultaneous all-type family or an action model.
\<close>

context paper_ZF_action_pair
begin

theorem paper_ZF_exponential_transport_identity:
  assumes object: "W \<in> objects"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  shows "paper_ZF_exponential_transport_code A source target compose X (identity W) F = F"
proof -
  have arrow: "identity W \<in> explode A" by (rule X.identity_arrow[OF object])
  have src: "source (identity W) = W" by (rule X.identity_source[OF object])
  have tgt: "target (identity W) = W" by (rule X.identity_target[OF object])
  have source_member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source (identity W)))"
    using member by (simp only: src)
  have decoded: "paper_ZF_decode_exponential A source target X W F \<in> exponential_fiber W"
    by (rule paper_ZF_decode_exponential_type[OF member])
  have generic_identity: "exponential_transport (identity W) (paper_ZF_decode_exponential A source target X W F) =
      paper_ZF_decode_exponential A source target X W F"
    by (rule paper_exponential_transport_identity[OF object decoded])
  have encoded: "paper_ZF_exponential_transport_code A source target compose X (identity W) F =
      paper_ZF_encode_exponential A source target X (target (identity W))
        (exponential_transport (identity W) (paper_ZF_decode_exponential A source target X (source (identity W)) F))"
    by (rule paper_ZF_transport_as_encoded[OF arrow source_member])
  show ?thesis using encoded
    by (simp only: src tgt generic_identity paper_ZF_encode_decode_exponential[OF member])
qed

theorem paper_ZF_exponential_transport_compose:
  assumes fa: "f \<in> explode A" and ga: "g \<in> explode A" and meeting: "target f = source g"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  shows "paper_ZF_exponential_transport_code A source target compose X (compose g f) F =
    paper_ZF_exponential_transport_code A source target compose X g
      (paper_ZF_exponential_transport_code A source target compose X f F)"
proof -
  let ?T = "paper_ZF_exponential_transport_code A source target compose X"
  let ?b = "paper_ZF_decode_exponential A source target X (source f) F"
  have ca: "compose g f \<in> explode A" by (rule X.compose_arrow[OF fa ga meeting])
  have src: "source (compose g f) = source f" by (rule X.compose_source[OF fa ga meeting])
  have tgt: "target (compose g f) = target g" by (rule X.compose_target[OF fa ga meeting])
  have composite_member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source (compose g f)))"
    using member by (simp only: src)
  have intermediate_member: "?T f F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source g))"
    using paper_ZF_exponential_transport_code_type[OF fa member] by (simp only: meeting)
  have decoded: "?b \<in> exponential_fiber (source f)" by (rule paper_ZF_decode_exponential_type[OF member])
  have generic_composition: "exponential_transport (compose g f) ?b = exponential_transport g (exponential_transport f ?b)"
    by (rule paper_exponential_transport_compose[OF fa ga meeting decoded])
  have intermediate_decoded: "paper_ZF_decode_exponential A source target X (source g) (?T f F) =
      exponential_transport f ?b"
    using paper_ZF_decode_exponential_transport[OF fa member] by (simp only: meeting)
  have left_encoded: "?T (compose g f) F =
      paper_ZF_encode_exponential A source target X (target g)
        (exponential_transport g (exponential_transport f ?b))"
    using paper_ZF_transport_as_encoded[OF ca composite_member]
    by (simp only: src tgt generic_composition)
  have right_encoded: "?T g (?T f F) =
      paper_ZF_encode_exponential A source target X (target g)
        (exponential_transport g (exponential_transport f ?b))"
    using paper_ZF_transport_as_encoded[OF ga intermediate_member]
    by (simp only: intermediate_decoded)
  show ?thesis by (simp only: left_encoded right_encoded)
qed

theorem paper_ZF_exponential_action:
  "paper_action objects (explode A) source target compose identity
    (\<lambda>W. explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W))
    (paper_ZF_exponential_transport_code A source target compose X)"
proof unfold_locales
  fix f F
  assume arrow: "f \<in> explode A"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  show "paper_ZF_exponential_transport_code A source target compose X f F \<in>
      explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (target f))"
    by (rule paper_ZF_exponential_transport_code_type[OF arrow member])
next
  fix W F
  assume object: "W \<in> objects"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  show "paper_ZF_exponential_transport_code A source target compose X (identity W) F = F"
    by (rule paper_ZF_exponential_transport_identity[OF object member])
next
  fix f g F
  assume fa: "f \<in> explode A" and ga: "g \<in> explode A" and meeting: "target f = source g"
    and member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap (source f))"
  show "paper_ZF_exponential_transport_code A source target compose X (compose g f) F =
      paper_ZF_exponential_transport_code A source target compose X g
        (paper_ZF_exponential_transport_code A source target compose X f F)"
    by (rule paper_ZF_exponential_transport_compose[OF fa ga meeting member])
qed

end

end
