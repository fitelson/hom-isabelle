theory Bacon_Source_ZF_Outgoing_Pairs
  imports Bacon_Source_ZF_Dependent_Pairs
    Bacon_Classicism_Action_Development.Bacon_Source_Exponential_Domain
begin

section \<open>Internal codes for outgoing-arrow and argument domains\<close>

text \<open>
  At an object W the exponential's input domain consists of pairs
  ⟨h,x⟩ with h:W→V and x∈X(V) (Example 3.16, p.54).
  Given an actual arrow set code A and actual fiber codes X(V),
  separation constructs Out(W), and dependent sum constructs
  Σh∈Out(W).X(target(h)).

  Arrows and values are HOL-ZF elements; objects may have a different
  HOL type. No object-set code, actual action, coherence premise or
  all-type decoder is required for these bounded set constructions.
  Opair is the internal pair, distinct from the HOL pair (h,x).
  The correspondence below is an actual bijection on the displayed
  domains, not an assertion that every HOL set is representable.
  These results are relative to the standard HOL-ZF set axioms.
\<close>

definition paper_ZF_outgoing_code :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_outgoing_code A source W = Sep A (\<lambda>h. source h = W)"

definition paper_ZF_pair_code ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_pair_code A source target X W =
    paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h))"

lemma paper_ZF_outgoing_code_member:
  "Elem h (paper_ZF_outgoing_code A source W) \<longleftrightarrow> h \<in> explode A \<and> source h = W"
  by (simp only: paper_ZF_outgoing_code_def Sep explode_Elem)

lemma paper_ZF_pair_code_member:
  "Elem (Opair h x) (paper_ZF_pair_code A source target X W) \<longleftrightarrow>
    h \<in> explode A \<and> source h = W \<and> x \<in> explode (X (target h))"
  by (simp only: paper_ZF_pair_code_def paper_ZF_sigma_pair_member
    paper_ZF_outgoing_code_member explode_Elem; blast)

lemma paper_ZF_pair_codeE:
  assumes member: "Elem z (paper_ZF_pair_code A source target X W)"
  obtains h x where "h \<in> explode A" "source h = W" "x \<in> explode (X (target h))" "z = Opair h x"
proof -
  have coded: "Elem z (paper_ZF_sigma (paper_ZF_outgoing_code A source W) (\<lambda>h. X (target h)))"
    using member unfolding paper_ZF_pair_code_def by assumption
  obtain h x where hm: "Elem h (paper_ZF_outgoing_code A source W)"
    and xm: "Elem x (X (target h))" and shape: "z = Opair h x"
    by (rule paper_ZF_sigmaE[OF coded])
  have arrow: "h \<in> explode A" and src: "source h = W"
    using hm by (auto simp only: paper_ZF_outgoing_code_member)
  have argument: "x \<in> explode (X (target h))" using xm by (simp only: explode_Elem)
  show thesis by (rule that[OF arrow src argument shape])
qed

theorem paper_ZF_pair_code_projections:
  assumes member: "Elem z (paper_ZF_pair_code A source target X W)"
  shows "Fst z \<in> explode A \<and> source (Fst z) = W \<and>
    Snd z \<in> explode (X (target (Fst z))) \<and> Opair (Fst z) (Snd z) = z"
proof -
  obtain h x where arrow: "h \<in> explode A" and src: "source h = W"
    and argument: "x \<in> explode (X (target h))" and shape: "z = Opair h x"
    by (rule paper_ZF_pair_codeE[OF member])
  show ?thesis by (simp only: shape Fst Snd; rule conjI[OF arrow conjI[OF src conjI[OF argument refl]]])
qed

lemma paper_ZF_pair_code_reconstruct:
  assumes member: "Elem z (paper_ZF_pair_code A source target X W)"
  shows "Opair (Fst z) (Snd z) = z"
  using paper_ZF_pair_code_projections[OF member] by blast

section \<open>Exact correspondence with the generic exponential pair domain\<close>

lemma paper_ZF_pair_code_iff_exponential:
  "Elem (Opair h x) (paper_ZF_pair_code A source target X W) \<longleftrightarrow>
    (h,x) \<in> paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W"
  by (simp only: paper_ZF_pair_code_member paper_exponential_pairs_iff)

lemma paper_ZF_pair_code_decode_into:
  assumes member: "Elem z (paper_ZF_pair_code A source target X W)"
  shows "(Fst z,Snd z) \<in> paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W"
  using paper_ZF_pair_code_projections[OF member]
  by (simp only: paper_exponential_pairs_iff; blast)

lemma paper_ZF_exponential_pairs_as_sigma:
  "paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W =
    Sigma (explode (paper_ZF_outgoing_code A source W)) (\<lambda>h. explode (X (target h)))"
proof (rule set_eqI)
  fix z :: "ZF \<times> ZF"
  obtain h x where pair: "z = (h,x)" by (cases z) auto
  show "(z \<in> paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W) =
      (z \<in> Sigma (explode (paper_ZF_outgoing_code A source W)) (\<lambda>h. explode (X (target h))))"
    by (simp add: pair paper_exponential_pairs_iff explode_Elem paper_ZF_outgoing_code_member)
qed

theorem paper_ZF_pair_code_bijection:
  "bij_betw (\<lambda>(h,x). Opair h x)
    (paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W)
    (explode (paper_ZF_pair_code A source target X W))"
  by (simp only: paper_ZF_pair_code_def paper_ZF_exponential_pairs_as_sigma;
    rule paper_ZF_sigma_bijection)

corollary paper_ZF_pair_code_image:
  "image (\<lambda>(h,x). Opair h x)
    (paper_exponential_pairs (explode A) source target (\<lambda>V. explode (X V)) W) =
    explode (paper_ZF_pair_code A source target X W)"
  using paper_ZF_pair_code_bijection[where A=A and source=source and target=target and X=X and W=W]
  unfolding bij_betw_def by (rule conjunct2)

end
