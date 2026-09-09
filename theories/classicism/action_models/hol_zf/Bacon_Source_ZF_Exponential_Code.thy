theory Bacon_Source_ZF_Exponential_Code
  imports Bacon_Source_ZF_Outgoing_Pairs Bacon_Source_ZF_Pair_Function_Graphs
    Bacon_Classicism_Action_Development.Bacon_Source_Exponential_Action
begin

section \<open>The exponential fiber as a separated set of function graphs\<close>

text \<open>
  At W, β has domain {⟨h,x⟩ | h:W→V, x∈XV}, values in YV,
  and satisfies iY(β⟨h,x⟩)=β⟨i∘h,iX(x)⟩.
  Source: Example 3.16, p.54, and Definition 3.18, p.55.

  Representation: the arrow carrier is explode(A), and X,Y assign
  actual HOL-ZF set codes. paper_ZF_exponential_code uses separation
  from the dependent function set on the concrete pair code. Coherence
  is stated with actual graph application, not an assumed decoder.
  Only one pair of coded actions is treated, not an all-type universe.
  These results are relative to standard HOL-ZF, with no new local axiom.
\<close>

definition paper_ZF_exponential_code ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    ('o \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    ('o \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_exponential_code A source target compose X xmap Y ymap W =
    Sep (paper_ZF_Pi (paper_ZF_pair_code A source target X W) (\<lambda>z. Y (target (Fst z))))
      (\<lambda>b. \<forall>h i x. h \<in> explode A \<longrightarrow> source h = W \<longrightarrow> i \<in> explode A \<longrightarrow>
        target h = source i \<longrightarrow> x \<in> explode (X (target h)) \<longrightarrow>
        ymap i (app b (Opair h x)) = app b (Opair (compose i h) (xmap i x)))"

definition paper_ZF_encode_exponential ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    'o \<Rightarrow> ((ZF \<times> ZF) \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "paper_ZF_encode_exponential A source target X W b =
    paper_ZF_encode_pair_function (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)) b"

definition paper_ZF_decode_exponential ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    'o \<Rightarrow> ZF \<Rightarrow> (ZF \<times> ZF) \<Rightarrow> ZF" where
  "paper_ZF_decode_exponential A source target X W b =
    paper_ZF_decode_pair_function (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)) b"

lemma paper_ZF_exponential_code_member:
  "b \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W) \<longleftrightarrow>
    b \<in> explode (paper_ZF_Pi (paper_ZF_pair_code A source target X W) (\<lambda>z. Y (target (Fst z)))) \<and>
    (\<forall>h i x. h \<in> explode A \<longrightarrow> source h = W \<longrightarrow> i \<in> explode A \<longrightarrow>
      target h = source i \<longrightarrow> x \<in> explode (X (target h)) \<longrightarrow>
      ymap i (app b (Opair h x)) = app b (Opair (compose i h) (xmap i x)))"
  by (simp only: paper_ZF_exponential_code_def explode_Elem Sep)

lemma paper_ZF_exponential_code_graph:
  assumes member: "b \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
  shows "b \<in> explode (paper_ZF_Pi (paper_ZF_pair_code A source target X W) (\<lambda>z. Y (target (Fst z))))"
  using member by (simp only: paper_ZF_exponential_code_member; blast)

lemma paper_ZF_exponential_code_coherent:
  assumes member: "b \<in> explode (paper_ZF_exponential_code A source target compose X xmap Y ymap W)"
    and ha: "h \<in> explode A" and sh: "source h = W" and ia: "i \<in> explode A"
    and meeting: "target h = source i" and xt: "x \<in> explode (X (target h))"
  shows "ymap i (app b (Opair h x)) = app b (Opair (compose i h) (xmap i x))"
  using assms by (simp only: paper_ZF_exponential_code_member; blast)

lemma paper_ZF_encode_exponential_value:
  assumes pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
  shows "app (paper_ZF_encode_exponential A source target X W b) (Opair h x) = b (h,x)"
proof -
  have coded: "Elem (Opair h x) (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))"
    using pair unfolding paper_ZF_pair_code_def by assumption
  show ?thesis by (simp only: paper_ZF_encode_exponential_def paper_ZF_encode_pair_function_def
    Lambda_app[OF coded] paper_ZF_flatten_pair_function_def if_P[OF coded] Fst Snd)
qed

lemma paper_ZF_decode_exponential_value:
  assumes pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
  shows "paper_ZF_decode_exponential A source target X W b (h,x) = app b (Opair h x)"
proof -
  have coded: "Elem (Opair h x) (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))"
    using pair unfolding paper_ZF_pair_code_def by assumption
  show ?thesis by (simp only: paper_ZF_decode_exponential_def paper_ZF_decode_pair_function_def prod.case
    paper_ZF_decode_function_def if_P[OF coded])
qed

lemma paper_ZF_exponential_pair_function:
  assumes member: "b \<in> paper_exponential_fiber (explode A) source target compose
    (\<lambda>V. explode (X V)) xmap (\<lambda>V. explode (Y V)) ymap W"
  shows "b \<in> paper_ZF_pair_functions (paper_ZF_outgoing_code A source W)
    (\<lambda>h. X (target h)) (\<lambda>h. Y (target h))"
  using member unfolding paper_exponential_fiber_def paper_ZF_pair_functions_def
  by (auto simp: paper_ZF_exponential_pairs_as_sigma paper_ZF_outgoing_code_member explode_Elem)

locale paper_ZF_action_pair =
  paper_exponential_actions objects "explode A" source target compose identity
    "\<lambda>W. explode (X W)" xmap "\<lambda>W. explode (Y W)" ymap
  for objects :: "'o set" and A :: ZF
    and source :: "ZF \<Rightarrow> 'o" and target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and X :: "'o \<Rightarrow> ZF" and xmap :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
    and Y :: "'o \<Rightarrow> ZF" and ymap :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
begin

lemma paper_ZF_exponential_advanced_pair:
  assumes ha: "h \<in> explode A" and sh: "source h = W" and ia: "i \<in> explode A"
    and meeting: "target h = source i" and xt: "x \<in> explode (X (target h))"
  shows "Elem (Opair (compose i h) (xmap i x)) (paper_ZF_pair_code A source target X W)"
proof -
  have pair: "(h,x) \<in> exponential_pairs W" using ha sh xt by (simp add: paper_exponential_pairs_iff)
  have advanced: "(compose i h,xmap i x) \<in> exponential_pairs W"
    by (rule paper_exponential_advance_pair[OF pair ia meeting])
  show ?thesis using advanced by (simp only: paper_ZF_pair_code_iff_exponential)
qed

end

end
