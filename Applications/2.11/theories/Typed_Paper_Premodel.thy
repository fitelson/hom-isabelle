theory Typed_Paper_Premodel
  imports Typed_Paper_Encoding
begin

lemma paper_function_type:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and fm: "Elem F (paper_D (Arr a b) w)" and xm: "Elem x (paper_D a v)"
  shows "Elem (app F (Opair (Opair w v) x)) (paper_D b v)"
proof -
  obtain f where ft: "Elem f (src_D (Arr a b) w)" and fe: "F=paper_enc (Arr a b) w f"
    using fm by (auto simp only: paper_D_member)
  have val: "Elem (app f (Opair v (paper_dec a v x))) (src_D b v)"
    by (rule src_function_type[OF ww vw wv ft paper_dec_type[OF xm]])
  show ?thesis
    by (simp only: fe paper_enc_app_dec[OF ww vw wv xm]) (rule paper_enc_type[OF val])
qed

lemma paper_function_graph:
  assumes "Elem F (paper_D (Arr a b) w)"
  shows "F=Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w) (app F)"
  using assms paper_enc_graph by (auto simp only: paper_D_member)

lemma paper_function_natural_pair:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and uw: "Elem u raw_W"
    and wv: "raw_rel w v" and vu: "raw_rel v u"
    and fm: "Elem F (src_D (Arr a b) w)" and xm: "Elem x (src_D a v)"
  shows "paper_T b (Opair v u)
      (app (paper_enc (Arr a b) w F) (Opair (Opair w v) (paper_enc a v x))) =
    app (paper_enc (Arr a b) w F)
      (Opair (Opair w u) (paper_T a (Opair v u) (paper_enc a v x)))"
proof -
  have wu: "raw_rel w u" by (rule raw_rel_trans[OF wv vu])
  have ax: "Elem (app F (Opair v x)) (src_D b v)"
    by (rule src_function_type[OF ww vw wv fm xm])
  have tx: "Elem (src_T a v u x) (src_D a u)" by (rule src_T_type[OF vw uw vu xm])
  show ?thesis
    by (simp only: paper_enc_app[OF ww vw wv xm] paper_T_enc[OF vw ax]
      paper_T_enc[OF vw xm] paper_enc_app[OF ww uw wu tx]
      src_function_natural[OF ww vw uw wv vu fm xm])
qed

lemma paper_function_natural:
  assumes fm: "Elem F (paper_D (Arr a b) w)" and ha: "Elem h pa_Ar" and hw: "Fst h=w"
    and ia: "Elem i pa_Ar" and meet: "Snd h=Fst i" and xm: "Elem x (paper_D a (Snd h))"
  shows "paper_T b i (app F (Opair h x)) =
    app F (Opair (pa_compose i h) (paper_T a i x))"
proof -
  define v where "v=Snd h"
  define u where "u=Snd i"
  have ww: "Elem w raw_W" using pa_arrow_data(1)[OF ha] by (simp only: hw)
  have vw: "Elem v raw_W" using pa_arrow_data(2)[OF ha] by (simp only: v_def)
  have wv: "raw_rel w v" using pa_arrow_data(3)[OF ha] by (simp only: hw v_def)
  have h: "h=Opair w v"
    using sym[OF pa_arrow_data(4)[OF ha]] by (simp only: hw v_def)
  have iv: "Fst i=v" unfolding v_def by (rule sym[OF meet])
  have uw: "Elem u raw_W" using pa_arrow_data(2)[OF ia] by (simp only: u_def)
  have vu: "raw_rel v u" using pa_arrow_data(3)[OF ia] by (simp only: iv u_def)
  have i: "i=Opair v u"
    using sym[OF pa_arrow_data(4)[OF ia]] by (simp only: iv u_def)
  obtain f where ft: "Elem f (src_D (Arr a b) w)" and fe: "F=paper_enc (Arr a b) w f"
    using fm by (auto simp only: paper_D_member)
  obtain y where yt: "Elem y (src_D a v)" and ye: "x=paper_enc a v y"
    using xm by (auto simp only: h Snd paper_D_member)
  show ?thesis
    by (simp only: h i fe ye pa_compose_def Fst Snd)
      (rule paper_function_natural_pair[OF ww vw uw wv vu ft yt])
qed

lemma paper_graph_Pi:
  assumes graph: "F=Lambda A (app F)" and value_type: "\<And>x. Elem x A \<Longrightarrow> Elem (app F x) (B x)"
  shows "Elem F (paper_ZF_Pi A B)"
proof -
  have bounded: "Elem (app F x) (Sum (Repl A B))" if "Elem x A" for x
    by (rule paper_ZF_dependent_bound_member[where A=A and B=B and x=x and y="app F x",
      OF that value_type[OF that]])
  have "Elem (Lambda A (app F)) (Fun A (Sum (Repl A B)))"
    using bounded by (simp only: Elem_Lambda_Fun; blast)
  then have function_member: "Elem F (Fun A (Sum (Repl A B)))" by (simp only: graph[symmetric])
  show ?thesis using function_member value_type by (simp only: paper_ZF_Pi_def Sep; blast)
qed

theorem paper_exponential_member:
  assumes ww: "Elem w raw_W" and fm: "Elem F (paper_D (Arr a b) w)"
  shows "Elem F (paper_ZF_exponential_code pa_Ar Fst Snd pa_compose
    (paper_D a) (paper_T a) (paper_D b) (paper_T b) w)"
proof -
  have value_type: "Elem (app F z) (paper_D b (Snd (Fst z)))"
    if zm: "Elem z (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)" for z
  proof -
    obtain v x where vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (paper_D a v)"
      and z: "z=Opair (Opair w v) x" using pa_pairE[OF zm] by blast
    show ?thesis by (simp only: z Fst Snd; rule paper_function_type[OF ww vw wv fm xm])
  qed
  have pi: "Elem F (paper_ZF_Pi (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)
      (\<lambda>z. paper_D b (Snd (Fst z))))"
    by (rule paper_graph_Pi[OF paper_function_graph[OF fm] value_type])
  show ?thesis
    unfolding paper_ZF_exponential_code_def
    by (simp only: Sep pi explode_Elem; intro conjI allI impI)
      (auto intro: paper_function_natural[OF fm])
qed

lemma paper_enc_prop_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and pm: "Elem p (src_D Prop w)"
  shows "paper_enc Prop v (src_T Prop w v p) =
    paper_ZF_powerset_transport_code pa_Ar Fst Snd pa_compose (Opair w v) (paper_enc Prop w p)"
proof (rule iffD2[OF Ext], intro allI)
  fix h
  show "Elem h (paper_enc Prop v (src_T Prop w v p)) =
    Elem h (paper_ZF_powerset_transport_code pa_Ar Fst Snd pa_compose
      (Opair w v) (paper_enc Prop w p))"
    using src_propositions_member[OF pm] ww vw wv
    by (auto simp: paper_enc.simps src_proposition_restriction[OF ww vw wv pm]
        paper_ZF_powerset_transport_code_def paper_ZF_outgoing_code_member
        Sep Repl pa_arrow_iff pa_compose_def Fst Snd Opair explode_Elem book_ZF_future_member)
qed

theorem paper_proposition_member:
  assumes ww: "Elem w raw_W" and pm: "Elem p (paper_D Prop w)"
  shows "Elem p (paper_ZF_powerset_code pa_Ar Fst w)"
proof -
  obtain q where qm: "Elem q (src_D Prop w)" and p: "p=paper_enc Prop w q"
    using pm by (auto simp only: paper_D_member)
  show ?thesis using src_propositions_member[OF qm] ww
    by (auto simp: p paper_enc.simps paper_ZF_powerset_code_def Power subset_def
        Repl paper_ZF_outgoing_code_member explode_Elem Fst Snd book_ZF_future_member)
qed

theorem paper_proposition_transport:
  assumes ha: "Elem h pa_Ar" and pm: "Elem p (paper_D Prop (Fst h))"
  shows "paper_T Prop h p = paper_ZF_powerset_transport_code pa_Ar Fst Snd pa_compose h p"
proof -
  obtain w v where ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and h: "h=Opair w v" using pa_arrowE[OF ha] by blast
  obtain q where qm: "Elem q (src_D Prop w)" and p: "p=paper_enc Prop w q"
    using pm by (auto simp only: h Fst paper_D_member)
  show ?thesis
    by (simp only: h p paper_T_enc[OF ww qm] paper_enc_prop_restriction[OF ww vw wv qm])
qed

lemma paper_enc_arrow_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and fm: "Elem F (src_D (Arr a b) w)"
  shows "paper_enc (Arr a b) v (src_T (Arr a b) w v F) =
    paper_ZF_exponential_transport_code pa_Ar Fst Snd pa_compose (paper_D a)
      (Opair w v) (paper_enc (Arr a b) w F)"
  unfolding paper_ZF_exponential_transport_code_def Snd
proof (rule paper_enc_Lambda_characterization[OF vw])
  fix u x assume uw: "Elem u raw_W" and vu: "raw_rel v u" and xm: "Elem x (src_D a u)"
  have wu: "raw_rel w u" by (rule raw_rel_trans[OF wv vu])
  have pair: "Elem (Opair u x) (book_ZF_pairs raw_W raw_rel (src_D a) v)"
    using uw vu xm by (simp only: book_ZF_pairs_member)
  have val: "app (src_T (Arr a b) w v F) (Opair u x)=app F (Opair u x)"
    by (simp only: src_function_restriction[OF ww vw wv fm]
      book_ZF_restrict_def Lambda_app[OF pair])
  show "app (paper_enc (Arr a b) w F)
      (Opair (pa_compose (Fst (Opair (Opair v u) (paper_enc a u x))) (Opair w v))
        (Snd (Opair (Opair v u) (paper_enc a u x)))) =
    paper_enc b u (app (src_T (Arr a b) w v F) (Opair u x))"
    by (simp only: Fst Snd pa_compose_def paper_enc_app[OF ww uw wu xm] val)
qed

theorem paper_function_transport:
  assumes ha: "Elem h pa_Ar" and fm: "Elem F (paper_D (Arr a b) (Fst h))"
  shows "paper_T (Arr a b) h F =
    paper_ZF_exponential_transport_code pa_Ar Fst Snd pa_compose (paper_D a) h F"
proof -
  obtain w v where ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and h: "h=Opair w v" using pa_arrowE[OF ha] by blast
  obtain f where ft: "Elem f (src_D (Arr a b) w)" and F: "F=paper_enc (Arr a b) w f"
    using fm by (auto simp only: h Fst paper_D_member)
  show ?thesis
    by (simp only: h F paper_T_enc[OF ww ft] paper_enc_arrow_restriction[OF ww vw wv ft])
qed

theorem paper_proposition_subaction:
  "paper_subaction (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D Prop w)) (paper_T Prop)
    (\<lambda>w. explode (paper_ZF_powerset_code pa_Ar Fst w))
    (paper_ZF_powerset_transport_code pa_Ar Fst Snd pa_compose)"
  by (rule paper_subactionI[OF paper_actions paper_ZF_powerset_action[OF pa_category]])
    (auto simp only: explode_Elem intro: paper_proposition_member paper_proposition_transport)

theorem paper_function_subaction:
  "paper_subaction (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D (Arr a b) w)) (paper_T (Arr a b))
    (\<lambda>w. explode (paper_ZF_exponential_code pa_Ar Fst Snd pa_compose
      (paper_D a) (paper_T a) (paper_D b) (paper_T b) w))
    (paper_ZF_exponential_transport_code pa_Ar Fst Snd pa_compose (paper_D a))"
proof -
  interpret X: paper_action "explode raw_W" "explode pa_Ar" Fst Snd pa_compose pa_id
    "\<lambda>w. explode (paper_D a w)" "paper_T a" by (rule paper_actions)
  interpret Y: paper_action "explode raw_W" "explode pa_Ar" Fst Snd pa_compose pa_id
    "\<lambda>w. explode (paper_D b w)" "paper_T b" by (rule paper_actions)
  interpret E: paper_ZF_action_pair "explode raw_W" pa_Ar Fst Snd pa_compose pa_id
    "paper_D a" "paper_T a" "paper_D b" "paper_T b" by unfold_locales
  show ?thesis
    by (rule paper_subactionI[OF paper_actions E.paper_ZF_exponential_action])
      (auto simp only: explode_Elem intro: paper_exponential_member paper_function_transport)
qed

definition paper_I :: "otype \<Rightarrow> 'c \<Rightarrow> ZF" where
  "paper_I a c=paper_enc a raw_root (src_I c a)"

lemma paper_I_type: "Elem (paper_I a c) (paper_D a raw_root)"
  unfolding paper_I_def by (rule paper_enc_type[OF src_I_type])

theorem paper_premodel:
  "paper_ZF_action_premodel \<Sigma> (explode raw_W) pa_Ar Fst Snd pa_compose pa_id raw_root
    paper_D paper_T paper_I"
proof (rule paper_ZF_action_premodelI[OF pa_rooted_category])
  fix a assume "paper_R_type a"
  show "paper_action (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D a w)) (paper_T a)" by (rule paper_actions)
next
  fix w assume "w \<in> explode raw_W"
  show "explode (paper_D Ind w) \<noteq> {}" by (rule paper_D_nonempty)
next
  show "paper_subaction (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D Prop w)) (paper_T Prop)
    (\<lambda>w. explode (paper_ZF_powerset_code pa_Ar Fst w))
    (paper_ZF_powerset_transport_code pa_Ar Fst Snd pa_compose)"
    by (rule paper_proposition_subaction)
next
  fix a b assume "paper_R_type (Arr a b)"
  show "paper_subaction (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D (Arr a b) w)) (paper_T (Arr a b))
    (\<lambda>w. explode (paper_ZF_exponential_code pa_Ar Fst Snd pa_compose
      (paper_D a) (paper_T a) (paper_D b) (paper_T b) w))
    (paper_ZF_exponential_transport_code pa_Ar Fst Snd pa_compose (paper_D a))"
    by (rule paper_function_subaction)
next
  fix a c assume "paper_R_type a" "c \<in> \<Sigma> a"
  show "paper_I a c \<in> explode (paper_D a raw_root)"
    by (simp only: explode_Elem, rule paper_I_type)
qed

end
