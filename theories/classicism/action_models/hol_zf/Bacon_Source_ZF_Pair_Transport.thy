theory Bacon_Source_ZF_Pair_Transport
  imports Bacon_Source_ZF_Outgoing_Pairs
begin

section \<open>Precomposition leaves the target argument unchanged\<close>

text \<open>
  If f:W→V and (i,x) is an exponential input at V, then
  (i∘f,x) is an input at W. Source: Example 3.16(ii), p.54.
  The value x already lies in X(target(i)); it is NOT transported
  along f. This pair-domain fact uses category laws alone, not an
  action on X or any result action Y.

  Arrows and values are explicit HOL-ZF codes. All uses of composition
  and pair projections retain their domain guards. This leaf adds
  neither an exponential coherence assumption nor an all-type decoder.
\<close>

lemma paper_ZF_pair_precompose:
  fixes Obj :: "'o set" and A :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and X :: "'o \<Rightarrow> ZF" and f i x :: ZF
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and arrow: "f \<in> explode A"
    and pair: "Elem (Opair i x) (paper_ZF_pair_code A source target X (target f))"
  shows "Elem (Opair (compose i f) x) (paper_ZF_pair_code A source target X (source f))"
proof -
  interpret C: paper_category Obj "explode A" source target compose identity by (rule category)
  have ia: "i \<in> explode A" and origin: "source i = target f"
    and argument: "x \<in> explode (X (target i))"
    using pair by (auto simp only: paper_ZF_pair_code_member)
  have meeting: "target f = source i" by (rule origin[symmetric])
  have composite: "compose i f \<in> explode A" by (rule C.compose_arrow[OF arrow ia meeting])
  have composite_source: "source (compose i f) = source f" by (rule C.compose_source[OF arrow ia meeting])
  have composite_target: "target (compose i f) = target i" by (rule C.compose_target[OF arrow ia meeting])
  have target_argument: "x \<in> explode (X (target (compose i f)))"
    by (simp only: composite_target; rule argument)
  show ?thesis by (rule iffD2[OF paper_ZF_pair_code_member[
    where A=A and source=source and target=target and X=X and W="source f" and h="compose i f" and x=x]
    conjI[OF composite conjI[OF composite_source target_argument]]])
qed

corollary paper_ZF_pair_precompose_code:
  fixes Obj :: "'o set" and A :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and X :: "'o \<Rightarrow> ZF" and f z :: ZF
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and arrow: "f \<in> explode A"
    and member: "Elem z (paper_ZF_pair_code A source target X (target f))"
  shows "Elem (Opair (compose (Fst z) f) (Snd z)) (paper_ZF_pair_code A source target X (source f))"
proof -
  have rebuilt: "Opair (Fst z) (Snd z) = z" by (rule paper_ZF_pair_code_reconstruct[OF member])
  have pair: "Elem (Opair (Fst z) (Snd z)) (paper_ZF_pair_code A source target X (target f))"
    by (simp only: rebuilt; rule member)
  show ?thesis by (rule paper_ZF_pair_precompose[OF category arrow pair])
qed

section \<open>Advancing a pair transports its argument\<close>

text \<open>
  If h:W→V, x∈X(V), and i:V→U, then
  (i∘h,iˣ(x)) is again an exponential input at W.
  Source: the coherence condition in Example 3.16(i), p.54.
  Unlike precomposition, this operation changes the argument's object
  and therefore requires the actual X action. No Y action is needed.
\<close>

lemma paper_ZF_pair_advance:
  fixes Obj :: "'o set" and A :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and X :: "'o \<Rightarrow> ZF" and xmap :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
    and W :: 'o and h i x :: ZF
  assumes action: "paper_action Obj (explode A) source target compose identity (\<lambda>V. explode (X V)) xmap"
    and pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
    and arrow: "i \<in> explode A" and meeting: "target h = source i"
  shows "Elem (Opair (compose i h) (xmap i x)) (paper_ZF_pair_code A source target X W)"
proof -
  interpret X: paper_action Obj "explode A" source target compose identity "\<lambda>V. explode (X V)" xmap
    by (rule action)
  have ha: "h \<in> explode A" and origin: "source h = W"
    and argument: "x \<in> explode (X (target h))"
    using pair by (auto simp only: paper_ZF_pair_code_member)
  have source_argument: "x \<in> explode (X (source i))" using argument by (simp only: meeting)
  have moved: "xmap i x \<in> explode (X (target i))"
    by (rule X.transport_type[OF arrow source_argument])
  have composite: "compose i h \<in> explode A" by (rule X.compose_arrow[OF ha arrow meeting])
  have composite_source: "source (compose i h) = W"
    by (simp only: X.compose_source[OF ha arrow meeting] origin)
  have composite_target: "target (compose i h) = target i" by (rule X.compose_target[OF ha arrow meeting])
  have target_argument: "xmap i x \<in> explode (X (target (compose i h)))"
    by (simp only: composite_target; rule moved)
  show ?thesis by (rule iffD2[OF paper_ZF_pair_code_member[
    where A=A and source=source and target=target and X=X and W=W and h="compose i h" and x="xmap i x"]
    conjI[OF composite conjI[OF composite_source target_argument]]])
qed

corollary paper_ZF_pair_advance_code:
  fixes Obj :: "'o set" and A :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and X :: "'o \<Rightarrow> ZF" and xmap :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
    and W :: 'o and i z :: ZF
  assumes action: "paper_action Obj (explode A) source target compose identity (\<lambda>V. explode (X V)) xmap"
    and member: "Elem z (paper_ZF_pair_code A source target X W)"
    and arrow: "i \<in> explode A" and meeting: "target (Fst z) = source i"
  shows "Elem (Opair (compose i (Fst z)) (xmap i (Snd z))) (paper_ZF_pair_code A source target X W)"
proof -
  have rebuilt: "Opair (Fst z) (Snd z) = z" by (rule paper_ZF_pair_code_reconstruct[OF member])
  have pair: "Elem (Opair (Fst z) (Snd z)) (paper_ZF_pair_code A source target X W)"
    by (simp only: rebuilt; rule member)
  show ?thesis by (rule paper_ZF_pair_advance[OF action pair arrow meeting])
qed

end
