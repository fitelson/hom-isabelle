theory Bacon_Source_ZF_Dependent_Pairs
  imports Bacon_Source_ZF_Function_Graphs
begin

section \<open>Dependent pair domains are actual internal sets\<close>

text \<open>
  Σa∈A.B(a) consists of ordered pairs ⟨a,b⟩ with a∈A and
  b∈B(a). Here A and each B(a) are explicit HOL-ZF sets.
  Replacement followed by union constructs this pair domain.
  Source role: the outgoing-arrow/argument pairs in Example 3.16,
  p.54, where the argument domain depends on the target of the arrow.

  This is a concrete bijection between the HOL dependent sum and
  the internal ordered-pair set. It uses standard HOL-ZF, not a
  universal representability assumption or a new local axiom.
\<close>

definition paper_ZF_sigma :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "paper_ZF_sigma A B = Sum (Repl A (\<lambda>a. Repl (B a) (Opair a)))"

lemma paper_ZF_sigma_membership:
  "Elem p (paper_ZF_sigma A B) \<longleftrightarrow>
    (\<exists>a b. Elem a A \<and> Elem b (B a) \<and> p = Opair a b)"
proof
  assume member: "Elem p (paper_ZF_sigma A B)"
  show "\<exists>a b. Elem a A \<and> Elem b (B a) \<and> p = Opair a b"
    using member by (auto simp: paper_ZF_sigma_def Sum Repl)
next
  assume pair_member: "\<exists>a b. Elem a A \<and> Elem b (B a) \<and> p = Opair a b"
  obtain a b where am: "Elem a A" and bm: "Elem b (B a)" and shape: "p = Opair a b"
    using pair_member by blast
  have inner: "Elem p (Repl (B a) (Opair a))"
    unfolding Repl by (rule exI[where x=b], rule conjI[OF bm shape])
  have outer: "Elem (Repl (B a) (Opair a)) (Repl A (\<lambda>a. Repl (B a) (Opair a)))"
    unfolding Repl by (rule exI[where x=a], rule conjI[OF am refl])
  show "Elem p (paper_ZF_sigma A B)"
    unfolding paper_ZF_sigma_def Sum
    by (rule exI[where x="Repl (B a) (Opair a)"], rule conjI[OF inner outer])
qed

lemma paper_ZF_sigma_pair_member:
  "Elem (Opair a b) (paper_ZF_sigma A B) \<longleftrightarrow>
    Elem a A \<and> Elem b (B a)"
  by (auto simp: paper_ZF_sigma_membership Opair)

lemma paper_ZF_sigmaE:
  assumes member: "Elem p (paper_ZF_sigma A B)"
  obtains a b where "Elem a A" "Elem b (B a)" "p = Opair a b"
  using member that by (auto simp only: paper_ZF_sigma_membership)

theorem paper_ZF_sigma_projections:
  assumes member: "Elem p (paper_ZF_sigma A B)"
  shows "Elem (Fst p) A \<and> Elem (Snd p) (B (Fst p)) \<and>
    Opair (Fst p) (Snd p) = p"
proof -
  obtain a b where am: "Elem a A" and bm: "Elem b (B a)" and shape: "p = Opair a b"
    by (rule paper_ZF_sigmaE[OF member])
  show ?thesis by (simp only: shape Fst Snd; rule conjI[OF am conjI[OF bm refl]])
qed

lemma paper_ZF_pair_encoding_injective:
  "inj (\<lambda>(a,b). Opair a b)"
  by (auto simp: inj_on_def Opair split: prod.splits)

theorem paper_ZF_sigma_bijection:
  "bij_betw (\<lambda>(a,b). Opair a b)
    (Sigma (explode A) (\<lambda>a. explode (B a))) (explode (paper_ZF_sigma A B))"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a)))"
    by (rule inj_on_subset[OF paper_ZF_pair_encoding_injective subset_UNIV])
next
  show "image (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a))) =
    explode (paper_ZF_sigma A B)"
  proof
    show "image (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a))) \<subseteq>
      explode (paper_ZF_sigma A B)"
      by (auto simp: explode_Elem paper_ZF_sigma_pair_member)
    show "explode (paper_ZF_sigma A B) \<subseteq>
      image (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a)))"
    proof
      fix p
      assume member: "p \<in> explode (paper_ZF_sigma A B)"
      have coded: "Elem p (paper_ZF_sigma A B)" using member by (simp only: explode_Elem)
      obtain a b where am: "Elem a A" and bm: "Elem b (B a)" and shape: "p = Opair a b"
        by (rule paper_ZF_sigmaE[OF coded])
      have pair_member: "(a,b) \<in> Sigma (explode A) (\<lambda>a. explode (B a))"
        using am bm by (simp add: explode_Elem)
      have in_image: "(\<lambda>(a,b). Opair a b) (a,b) \<in>
        image (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a)))"
        by (rule imageI[OF pair_member])
      show "p \<in> image (\<lambda>(a,b). Opair a b) (Sigma (explode A) (\<lambda>a. explode (B a)))"
        using in_image by (simp only: prod.case shape)
    qed
  qed
qed

end
