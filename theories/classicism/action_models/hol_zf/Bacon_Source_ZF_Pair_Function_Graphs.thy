theory Bacon_Source_ZF_Pair_Function_Graphs
  imports Bacon_Source_ZF_Dependent_Pairs Bacon_Source_ZF_Dependent_Function_Graphs
begin

section \<open>Flattening functions on a dependent pair domain\<close>

text \<open>
  A function β on pairs ⟨h,x⟩, h∈A and x∈X(h), with
  β⟨h,x⟩∈Y(h), is encoded over the internal pair set
  Σh∈A.X(h). Its dependent result set at z is Y(Fst(z)).
  Source role: Example 3.16 and Definition 3.18, pp.54–55.

  Both total HOL function representations are normalized outside their
  actual domains. Ordered-pair coding and its projections are concrete.
  All bounds are explicit HOL-ZF sets; no arbitrary-set representability,
  assumed decoder, coherence law, category or logical model is used.
  The results are relative to standard HOL-ZF, with no new local axiom.
\<close>

definition paper_ZF_pair_functions ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ((ZF \<times> ZF) \<Rightarrow> ZF) set" where
  "paper_ZF_pair_functions A X Y = {b.
    (\<forall>p. p \<notin> Sigma (explode A) (\<lambda>h. explode (X h)) \<longrightarrow> b p = undefined) \<and>
    (\<forall>h x. Elem h A \<longrightarrow> Elem x (X h) \<longrightarrow> Elem (b (h,x)) (Y h))}"

definition paper_ZF_flatten_pair_function ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ((ZF \<times> ZF) \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_flatten_pair_function A X b z =
    (if Elem z (paper_ZF_sigma A X) then b (Fst z,Snd z) else undefined)"

definition paper_ZF_encode_pair_function ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ((ZF \<times> ZF) \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "paper_ZF_encode_pair_function A X b = Lambda (paper_ZF_sigma A X) (paper_ZF_flatten_pair_function A X b)"

definition paper_ZF_decode_pair_function ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> (ZF \<times> ZF) \<Rightarrow> ZF" where
  "paper_ZF_decode_pair_function A X F p =
    (case p of (h,x) \<Rightarrow> paper_ZF_decode_function (paper_ZF_sigma A X) F (Opair h x))"

lemma paper_ZF_pair_domain_iff:
  "(h,x) \<in> Sigma (explode A) (\<lambda>h. explode (X h)) \<longleftrightarrow> Elem h A \<and> Elem x (X h)"
  by (simp add: explode_Elem)

lemma paper_ZF_pair_function_normal:
  assumes member: "b \<in> paper_ZF_pair_functions A X Y"
    and outside: "p \<notin> Sigma (explode A) (\<lambda>h. explode (X h))"
  shows "b p = undefined"
  using member outside unfolding paper_ZF_pair_functions_def by blast

lemma paper_ZF_pair_function_value:
  assumes member: "b \<in> paper_ZF_pair_functions A X Y" and index: "Elem h A" and argument: "Elem x (X h)"
  shows "Elem (b (h,x)) (Y h)"
  using member index argument unfolding paper_ZF_pair_functions_def by blast

lemma paper_ZF_flatten_pair_function_type:
  assumes member: "b \<in> paper_ZF_pair_functions A X Y"
  shows "paper_ZF_flatten_pair_function A X b \<in>
    paper_ZF_dependent_functions (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z))"
proof (unfold paper_ZF_dependent_functions_def, rule CollectI, rule conjI)
  show "\<forall>z. \<not> Elem z (paper_ZF_sigma A X) \<longrightarrow> paper_ZF_flatten_pair_function A X b z = undefined"
    by (simp add: paper_ZF_flatten_pair_function_def)
next
  show "\<forall>z. Elem z (paper_ZF_sigma A X) \<longrightarrow>
    Elem (paper_ZF_flatten_pair_function A X b z) (Y (Fst z))"
  proof (intro allI impI)
    fix z
    assume zm: "Elem z (paper_ZF_sigma A X)"
    have projections: "Elem (Fst z) A \<and> Elem (Snd z) (X (Fst z)) \<and> Opair (Fst z) (Snd z) = z"
      by (rule paper_ZF_sigma_projections[OF zm])
    have result: "Elem (b (Fst z,Snd z)) (Y (Fst z))"
      by (rule paper_ZF_pair_function_value[OF member conjunct1[OF projections] conjunct1[OF conjunct2[OF projections]]])
    show "Elem (paper_ZF_flatten_pair_function A X b z) (Y (Fst z))"
      by (simp only: paper_ZF_flatten_pair_function_def if_P[OF zm]; rule result)
  qed
qed

lemma paper_ZF_encode_pair_function_type:
  assumes member: "b \<in> paper_ZF_pair_functions A X Y"
  shows "paper_ZF_encode_pair_function A X b \<in>
    explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
  unfolding paper_ZF_encode_pair_function_def
  by (rule paper_ZF_encode_dependent_function_type[OF paper_ZF_flatten_pair_function_type[OF member]])

lemma paper_ZF_decode_pair_function_type:
  assumes graph: "F \<in> explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
  shows "paper_ZF_decode_pair_function A X F \<in> paper_ZF_pair_functions A X Y"
proof (unfold paper_ZF_pair_functions_def, rule CollectI, rule conjI)
  show "\<forall>p. p \<notin> Sigma (explode A) (\<lambda>h. explode (X h)) \<longrightarrow>
    paper_ZF_decode_pair_function A X F p = undefined"
  proof (intro allI impI)
    fix p :: "ZF \<times> ZF"
    assume outside: "p \<notin> Sigma (explode A) (\<lambda>h. explode (X h))"
    obtain h x where shape: "p = (h,x)" by (cases p) auto
    have absent: "\<not> Elem (Opair h x) (paper_ZF_sigma A X)"
      using outside by (simp add: shape paper_ZF_pair_domain_iff paper_ZF_sigma_pair_member explode_Elem)
    show "paper_ZF_decode_pair_function A X F p = undefined"
      by (simp only: shape paper_ZF_decode_pair_function_def prod.case paper_ZF_decode_function_def if_not_P[OF absent])
  qed
next
  show "\<forall>h x. Elem h A \<longrightarrow> Elem x (X h) \<longrightarrow>
    Elem (paper_ZF_decode_pair_function A X F (h,x)) (Y h)"
  proof (intro allI impI)
    fix h x
    assume hm: "Elem h A" and xm: "Elem x (X h)"
    have coded: "Elem (Opair h x) (paper_ZF_sigma A X)"
      by (rule iffD2[OF paper_ZF_sigma_pair_member[where A=A and B=X and a=h and b=x]
        conjI[OF hm xm]])
    have result: "Elem (app F (Opair h x)) (Y (Fst (Opair h x)))"
      by (rule paper_ZF_Pi_value[OF graph coded])
    show "Elem (paper_ZF_decode_pair_function A X F (h,x)) (Y h)"
      using result by (simp only: paper_ZF_decode_pair_function_def prod.case
        paper_ZF_decode_function_def if_P[OF coded] Fst)
  qed
qed

section \<open>Both inverse laws hold on the actual bounded carriers\<close>

theorem paper_ZF_decode_encode_pair_function:
  assumes member: "b \<in> paper_ZF_pair_functions A X Y"
  shows "paper_ZF_decode_pair_function A X (paper_ZF_encode_pair_function A X b) = b"
proof (rule ext)
  fix p :: "ZF \<times> ZF"
  obtain h x where shape: "p = (h,x)" by (cases p) auto
  show "paper_ZF_decode_pair_function A X (paper_ZF_encode_pair_function A X b) p = b p"
  proof (cases "Elem (Opair h x) (paper_ZF_sigma A X)")
    case True
    show ?thesis by (simp only: shape paper_ZF_decode_pair_function_def prod.case
      paper_ZF_encode_pair_function_def paper_ZF_decode_function_def if_P[OF True]
      Lambda_app[OF True] paper_ZF_flatten_pair_function_def Fst Snd)
  next
    case False
    have outside: "(h,x) \<notin> Sigma (explode A) (\<lambda>h. explode (X h))"
      using False by (simp add: paper_ZF_sigma_pair_member paper_ZF_pair_domain_iff explode_Elem)
    show ?thesis by (simp only: shape paper_ZF_decode_pair_function_def prod.case paper_ZF_decode_function_def
      if_not_P[OF False] paper_ZF_pair_function_normal[OF member outside])
  qed
qed

lemma paper_ZF_flatten_decode_pair_function:
  "paper_ZF_flatten_pair_function A X (paper_ZF_decode_pair_function A X F) =
    paper_ZF_decode_function (paper_ZF_sigma A X) F"
proof (rule ext)
  fix z
  show "paper_ZF_flatten_pair_function A X (paper_ZF_decode_pair_function A X F) z =
    paper_ZF_decode_function (paper_ZF_sigma A X) F z"
  proof (cases "Elem z (paper_ZF_sigma A X)")
    case True
    have rebuild: "Opair (Fst z) (Snd z) = z"
      by (rule conjunct2[OF conjunct2[OF paper_ZF_sigma_projections[OF True]]])
    show ?thesis by (simp only: paper_ZF_flatten_pair_function_def if_P[OF True]
      paper_ZF_decode_pair_function_def prod.case rebuild)
  next
    case False
    show ?thesis by (simp only: paper_ZF_flatten_pair_function_def paper_ZF_decode_function_def if_not_P[OF False])
  qed
qed

theorem paper_ZF_encode_decode_pair_function:
  assumes graph: "F \<in> explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
  shows "paper_ZF_encode_pair_function A X (paper_ZF_decode_pair_function A X F) = F"
  by (simp only: paper_ZF_encode_pair_function_def paper_ZF_flatten_decode_pair_function;
    rule paper_ZF_encode_decode_dependent_function[OF graph])

lemma paper_ZF_pair_function_graph_injective:
  "inj_on (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y)"
proof (rule inj_onI)
  fix b c
  assume bm: "b \<in> paper_ZF_pair_functions A X Y" and cm: "c \<in> paper_ZF_pair_functions A X Y"
    and same: "paper_ZF_encode_pair_function A X b = paper_ZF_encode_pair_function A X c"
  have equal: "paper_ZF_decode_pair_function A X (paper_ZF_encode_pair_function A X b) =
    paper_ZF_decode_pair_function A X (paper_ZF_encode_pair_function A X c)" by (simp only: same)
  show "b = c" using equal by (simp only: paper_ZF_decode_encode_pair_function[OF bm] paper_ZF_decode_encode_pair_function[OF cm])
qed

theorem paper_ZF_pair_function_graph_bijection:
  "bij_betw (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y)
    (explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z))))"
proof (unfold bij_betw_def, rule conjI[OF paper_ZF_pair_function_graph_injective])
  show "image (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y) =
    explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
  proof
    show "image (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y) \<subseteq>
      explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
      using paper_ZF_encode_pair_function_type by blast
  next
    show "explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z))) \<subseteq>
      image (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y)"
    proof
      fix F
      assume graph: "F \<in> explode (paper_ZF_Pi (paper_ZF_sigma A X) (\<lambda>z. Y (Fst z)))"
      have decoded: "paper_ZF_decode_pair_function A X F \<in> paper_ZF_pair_functions A X Y"
        by (rule paper_ZF_decode_pair_function_type[OF graph])
      have member: "paper_ZF_encode_pair_function A X (paper_ZF_decode_pair_function A X F) \<in>
        image (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y)"
        by (rule imageI[OF decoded])
      show "F \<in> image (paper_ZF_encode_pair_function A X) (paper_ZF_pair_functions A X Y)"
        using member by (simp only: paper_ZF_encode_decode_pair_function[OF graph])
    qed
  qed
qed

end
