theory Bacon_Source_ZF_Exponential_Codec
  imports Bacon_Source_ZF_Exponential_Code
begin

section \<open>The concrete graph code matches the generic exponential fiber\<close>

text \<open>
  Encoding β as its graph preserves typing and coherence. Decoding a
  coherent graph returns a normalized member of the generic exponential
  fiber. Both inverse laws follow from the bounded pair-function codec.
  Source role: the exact functions of Example 3.16, p.54.

  The advanced-pair proof is essential: graph application is used only
  on pairs in its specified domain. Empty fibers and domains are allowed.
  Status: a concrete bijection for one pair of actual coded actions,
  not a uniform all-R decoding locale or an action-premodel construction.
\<close>

context paper_ZF_action_pair
begin

theorem paper_ZF_encode_exponential_type:
  assumes member: "b \<in> exponential_fiber W"
  shows "paper_ZF_encode_exponential A source target X W b \<in>
    explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
proof (simp only: paper_ZF_exponential_code_member, rule conjI)
  have pair_member: "b \<in> paper_ZF_pair_functions (paper_ZF_outgoing_code A source W)
      (\<lambda>h. X (target h)) (\<lambda>h. Y (target h))"
    by (rule paper_ZF_exponential_pair_function[OF member])
  have graph: "paper_ZF_encode_pair_function (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)) b \<in>
      explode (paper_ZF_Pi (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))
        (\<lambda>z. Y (target (Fst z))))"
    by (rule paper_ZF_encode_pair_function_type[OF pair_member])
  show "paper_ZF_encode_exponential A source target X W b \<in>
      explode (paper_ZF_Pi (paper_ZF_pair_code A source target X W) (\<lambda>z. Y (target (Fst z))))"
    using graph by (simp only: paper_ZF_encode_exponential_def paper_ZF_pair_code_def)
next
  show "\<forall>h i x. h \<in> explode A \<longrightarrow> source h = W \<longrightarrow> i \<in> explode A \<longrightarrow>
      target h = source i \<longrightarrow> x \<in> explode (X (target h)) \<longrightarrow>
      ymap i (app (paper_ZF_encode_exponential A source target X W b) (Opair h x)) =
      app (paper_ZF_encode_exponential A source target X W b) (Opair (compose i h) (xmap i x))"
  proof (intro allI impI)
    fix h i x
    assume ha: "h \<in> explode A" and sh: "source h = W" and ia: "i \<in> explode A"
      and meeting: "target h = source i" and xt: "x \<in> explode (X (target h))"
    have first_pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
      using ha sh xt by (simp only: paper_ZF_pair_code_member; blast)
    have second_pair: "Elem (Opair (compose i h) (xmap i x)) (paper_ZF_pair_code A source target X W)"
      by (rule paper_ZF_exponential_advanced_pair[OF ha sh ia meeting xt])
    have coherent: "ymap i (b (h,x)) = b (compose i h,xmap i x)"
      by (rule paper_exponential_fiber_coherent[OF member ha sh ia meeting xt])
    show "ymap i (app (paper_ZF_encode_exponential A source target X W b) (Opair h x)) =
        app (paper_ZF_encode_exponential A source target X W b) (Opair (compose i h) (xmap i x))"
      by (simp only: paper_ZF_encode_exponential_value[OF first_pair]
        paper_ZF_encode_exponential_value[OF second_pair]; rule coherent)
  qed
qed

theorem paper_ZF_decode_exponential_type:
  assumes member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  shows "paper_ZF_decode_exponential A source target X W F \<in> exponential_fiber W"
proof -
  have graph: "F \<in> explode (paper_ZF_Pi
      (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))
      (\<lambda>z. Y (target (Fst z))))"
    using paper_ZF_exponential_code_graph[OF member] by (simp only: paper_ZF_pair_code_def)
  have pair_member: "paper_ZF_decode_exponential A source target X W F \<in>
      paper_ZF_pair_functions (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)) (\<lambda>h. Y (target h))"
    unfolding paper_ZF_decode_exponential_def by (rule paper_ZF_decode_pair_function_type[OF graph])
  show ?thesis
  proof (rule paper_exponential_fiberI)
    fix p
    assume outside: "p \<notin> exponential_pairs W"
    have outside_pair: "p \<notin> Sigma (explode (paper_ZF_outgoing_code A source W)) (\<lambda>h. explode (X (target h)))"
      using outside by (simp add: paper_ZF_exponential_pairs_as_sigma)
    show "paper_ZF_decode_exponential A source target X W F p = undefined"
      by (rule paper_ZF_pair_function_normal[OF pair_member outside_pair])
  next
    fix h x
    assume ha: "h \<in> explode A" and sh: "source h = W" and xt: "x \<in> explode (X (target h))"
    have hc: "Elem h (paper_ZF_outgoing_code A source W)"
      using ha sh by (simp only: paper_ZF_outgoing_code_member; blast)
    have xc: "Elem x (X (target h))" using xt by (simp only: explode_Elem)
    have returned: "Elem (paper_ZF_decode_exponential A source target X W F (h,x)) (Y (target h))"
      by (rule paper_ZF_pair_function_value[OF pair_member hc xc])
    show "paper_ZF_decode_exponential A source target X W F (h,x) \<in> explode (Y (target h))"
      using returned by (simp only: explode_Elem)
  next
    fix h i x
    assume ha: "h \<in> explode A" and sh: "source h = W" and ia: "i \<in> explode A"
      and meeting: "target h = source i" and xt: "x \<in> explode (X (target h))"
    have first_pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
      using ha sh xt by (simp only: paper_ZF_pair_code_member; blast)
    have second_pair: "Elem (Opair (compose i h) (xmap i x)) (paper_ZF_pair_code A source target X W)"
      by (rule paper_ZF_exponential_advanced_pair[OF ha sh ia meeting xt])
    have coherent: "ymap i (app F (Opair h x)) = app F (Opair (compose i h) (xmap i x))"
      by (rule paper_ZF_exponential_code_coherent[OF member ha sh ia meeting xt])
    show "ymap i (paper_ZF_decode_exponential A source target X W F (h,x)) =
        paper_ZF_decode_exponential A source target X W F (compose i h,xmap i x)"
      by (simp only: paper_ZF_decode_exponential_value[OF first_pair]
        paper_ZF_decode_exponential_value[OF second_pair]; rule coherent)
  qed
qed

theorem paper_ZF_decode_encode_exponential:
  assumes member: "b \<in> exponential_fiber W"
  shows "paper_ZF_decode_exponential A source target X W
    (paper_ZF_encode_exponential A source target X W b) = b"
  unfolding paper_ZF_decode_exponential_def paper_ZF_encode_exponential_def
  by (rule paper_ZF_decode_encode_pair_function[OF paper_ZF_exponential_pair_function[OF member]])

theorem paper_ZF_encode_decode_exponential:
  assumes member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  shows "paper_ZF_encode_exponential A source target X W
    (paper_ZF_decode_exponential A source target X W F) = F"
proof -
  have graph: "F \<in> explode (paper_ZF_Pi
      (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))
      (\<lambda>z. Y (target (Fst z))))"
    using paper_ZF_exponential_code_graph[OF member] by (simp only: paper_ZF_pair_code_def)
  show ?thesis unfolding paper_ZF_encode_exponential_def paper_ZF_decode_exponential_def
    by (rule paper_ZF_encode_decode_pair_function[OF graph])
qed

theorem paper_ZF_exponential_code_bijection:
  "bij_betw (paper_ZF_encode_exponential A source target X W) (exponential_fiber W)
    (explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W))"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (paper_ZF_encode_exponential A source target X W) (exponential_fiber W)"
  proof (rule inj_onI)
    fix b c
    assume bm: "b \<in> exponential_fiber W" and cm: "c \<in> exponential_fiber W"
      and equal: "paper_ZF_encode_exponential A source target X W b = paper_ZF_encode_exponential A source target X W c"
    have decoded: "paper_ZF_decode_exponential A source target X W (paper_ZF_encode_exponential A source target X W b) =
        paper_ZF_decode_exponential A source target X W (paper_ZF_encode_exponential A source target X W c)"
      by (simp only: equal)
    show "b = c" using decoded by (simp only: paper_ZF_decode_encode_exponential[OF bm] paper_ZF_decode_encode_exponential[OF cm])
  qed
next
  show "image (paper_ZF_encode_exponential A source target X W) (exponential_fiber W) =
      explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  proof
    show "image (paper_ZF_encode_exponential A source target X W) (exponential_fiber W) \<subseteq>
        explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
      using paper_ZF_encode_exponential_type by blast
    show "explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W) \<subseteq>
        image (paper_ZF_encode_exponential A source target X W) (exponential_fiber W)"
    proof
      fix F
      assume member: "F \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
      have decoded: "paper_ZF_decode_exponential A source target X W F \<in> exponential_fiber W"
        by (rule paper_ZF_decode_exponential_type[OF member])
      have encoded: "paper_ZF_encode_exponential A source target X W (paper_ZF_decode_exponential A source target X W F) \<in>
          image (paper_ZF_encode_exponential A source target X W) (exponential_fiber W)"
        by (rule imageI[OF decoded])
      show "F \<in> image (paper_ZF_encode_exponential A source target X W) (exponential_fiber W)"
        using encoded by (simp only: paper_ZF_encode_decode_exponential[OF member])
    qed
  qed
qed

end

end
