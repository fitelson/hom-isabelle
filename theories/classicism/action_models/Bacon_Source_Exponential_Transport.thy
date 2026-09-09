theory Bacon_Source_Exponential_Transport
  imports Bacon_Source_Exponential_Domain
begin

section \<open>Precomposition preserves the exponential fiber\<close>

text \<open>
  For f:A→B, exponential transport is (fβ)⟨i,x⟩=β⟨i∘f,x⟩.
  Associativity gives its coherence equation; the X-action supplies the
  type of iX(x). Source: Example 3.16(ii), p.54.

  Representation: the locale below fixes two actions over one small
  category, with independent carriers 'x and 'y. No injectivity or
  surjectivity of either action is assumed. Status: transport closure.
\<close>

locale paper_exponential_actions =
  X: paper_action objects arrows source target compose identity X xmap +
  Y: paper_action objects arrows source target compose identity Y ymap
  for objects :: "'o set" and arrows :: "'a set"
    and source :: "'a \<Rightarrow> 'o" and target :: "'a \<Rightarrow> 'o"
    and compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and identity :: "'o \<Rightarrow> 'a"
    and X :: "'o \<Rightarrow> 'x set" and xmap :: "'a \<Rightarrow> 'x \<Rightarrow> 'x"
    and Y :: "'o \<Rightarrow> 'y set" and ymap :: "'a \<Rightarrow> 'y \<Rightarrow> 'y"
begin

abbreviation exponential_pairs where
  "exponential_pairs \<equiv> paper_exponential_pairs arrows source target X"

abbreviation exponential_fiber where
  "exponential_fiber \<equiv> paper_exponential_fiber arrows source target compose X xmap Y ymap"

abbreviation exponential_transport where
  "exponential_transport \<equiv> paper_exponential_transport arrows source target compose X"

lemma paper_exponential_precompose_pair:
  assumes fa: "f \<in> arrows" and pair: "(i,x) \<in> exponential_pairs (target f)"
  shows "(compose i f,x) \<in> exponential_pairs (source f)"
proof -
  have ia: "i \<in> arrows" and si: "source i = target f" and xt: "x \<in> X (target i)"
    using pair by (auto simp: paper_exponential_pairs_iff)
  have meeting: "target f = source i" by (rule si[symmetric])
  show ?thesis using X.compose_arrow[OF fa ia meeting]
    X.compose_source[OF fa ia meeting] X.compose_target[OF fa ia meeting] xt
    by (simp add: paper_exponential_pairs_iff)
qed

lemma paper_exponential_advance_pair:
  assumes pair: "(h,x) \<in> exponential_pairs A" and ia: "i \<in> arrows"
    and meeting: "target h = source i"
  shows "(compose i h,xmap i x) \<in> exponential_pairs A"
proof -
  have ha: "h \<in> arrows" and sh: "source h = A" and xt: "x \<in> X (target h)"
    using pair by (auto simp: paper_exponential_pairs_iff)
  have xs: "x \<in> X (source i)" using xt by (simp only: meeting)
  have moved: "xmap i x \<in> X (target i)" by (rule X.transport_type[OF ia xs])
  show ?thesis using X.compose_arrow[OF ha ia meeting]
    X.compose_source[OF ha ia meeting] X.compose_target[OF ha ia meeting] sh moved
    by (simp add: paper_exponential_pairs_iff)
qed

lemma paper_exponential_transport_type:
  assumes fa: "f \<in> arrows" and member: "b \<in> exponential_fiber (source f)"
  shows "exponential_transport f b \<in> exponential_fiber (target f)"
proof (rule paper_exponential_fiberI)
  fix p
  assume outside: "p \<notin> exponential_pairs (target f)"
  show "exponential_transport f b p = undefined"
    by (rule paper_exponential_transport_off[OF outside])
next
  fix h x
  assume ha: "h \<in> arrows" and sh: "source h = target f" and xt: "x \<in> X (target h)"
  have pair: "(h,x) \<in> exponential_pairs (target f)"
    using ha sh xt by (simp add: paper_exponential_pairs_iff)
  have meeting: "target f = source h" by (rule sh[symmetric])
  have ca: "compose h f \<in> arrows" by (rule X.compose_arrow[OF fa ha meeting])
  have cs: "source (compose h f) = source f" by (rule X.compose_source[OF fa ha meeting])
  have ct: "target (compose h f) = target h" by (rule X.compose_target[OF fa ha meeting])
  have xc: "x \<in> X (target (compose h f))" using xt by (simp only: ct)
  have bt: "b (compose h f,x) \<in> Y (target (compose h f))"
    by (rule paper_exponential_fiber_type[OF member ca cs xc])
  show "exponential_transport f b (h,x) \<in> Y (target h)"
    using bt by (simp only: paper_exponential_transport_on[OF pair] ct)
next
  fix h i x
  assume ha: "h \<in> arrows" and sh: "source h = target f" and ia: "i \<in> arrows"
    and hi: "target h = source i" and xt: "x \<in> X (target h)"
  have pair: "(h,x) \<in> exponential_pairs (target f)"
    using ha sh xt by (simp add: paper_exponential_pairs_iff)
  have advanced: "(compose i h,xmap i x) \<in> exponential_pairs (target f)"
    by (rule paper_exponential_advance_pair[OF pair ia hi])
  have fh: "target f = source h" by (rule sh[symmetric])
  have ca: "compose h f \<in> arrows" by (rule X.compose_arrow[OF fa ha fh])
  have cs: "source (compose h f) = source f" by (rule X.compose_source[OF fa ha fh])
  have ct: "target (compose h f) = target h" by (rule X.compose_target[OF fa ha fh])
  have ci: "target (compose h f) = source i" by (simp only: ct hi)
  have xc: "x \<in> X (target (compose h f))" using xt by (simp only: ct)
  have coherent: "ymap i (b (compose h f,x)) = b (compose i (compose h f),xmap i x)"
    by (rule paper_exponential_fiber_coherent[OF member ca cs ia ci xc])
  have assoc: "compose i (compose h f) = compose (compose i h) f"
    by (rule X.compose_assoc[OF fa ha ia fh hi])
  show "ymap i (exponential_transport f b (h,x)) =
      exponential_transport f b (compose i h,xmap i x)"
    by (simp only: paper_exponential_transport_on[OF pair]
      paper_exponential_transport_on[OF advanced] coherent assoc)
qed

end

end
