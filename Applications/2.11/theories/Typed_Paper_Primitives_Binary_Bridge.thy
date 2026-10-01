theory Typed_Paper_Primitives_Binary_Bridge
  imports Typed_Paper_Primitives
begin

section \<open>Two-argument operators in the literal paper graph format\<close>

lemma pc_binary_graph:
  assumes ww: "Elem w raw_W"
    and typed_O: "\<And>v. Elem (op_family v) (raw_D (Arr a (Arr b Prop)) v)"
    and nat: "\<And>v u. Elem v raw_W \<Longrightarrow> Elem u raw_W \<Longrightarrow> raw_rel v u \<Longrightarrow>
      raw_T (Arr a (Arr b Prop)) v u (op_family v) = op_family u"
    and val: "\<And>v x y. Elem v raw_W \<Longrightarrow> Elem x (raw_D a v) \<Longrightarrow>
      Elem y (raw_D b v) \<Longrightarrow>
      pc_enc Prop v (raw_app b Prop v (raw_app a (Arr b Prop) v (op_family v) x) y) =
      V v (pc_enc a v x) (pc_enc b v y)"
  shows "pc_enc (Arr a (Arr b Prop)) w (op_family w) =
    paper_ZF_pair_lambda pa_Ar Fst Snd (paper_D a) w
      (\<lambda>i x. paper_ZF_pair_lambda pa_Ar Fst Snd (paper_D b) (Snd i)
        (\<lambda>j y. V (Snd j) (paper_T a j x) y))"
proof -
  have partial: "pc_enc (Arr b Prop) v (raw_app a (Arr b Prop) v (op_family v) x) =
    paper_ZF_pair_lambda pa_Ar Fst Snd (paper_D b) v
      (\<lambda>j y. V (Snd j) (paper_T a j (pc_enc a v x)) y)"
    if vw: "Elem v raw_W" and xm: "Elem x (raw_D a v)" for v x
  proof (unfold paper_ZF_pair_lambda_def, rule pc_enc_Lambda_characterization[OF vw])
    fix u y assume uw: "Elem u raw_W" and vu: "raw_rel v u"
      and ym: "Elem y (raw_D b u)"
    have xu: "Elem (raw_T a v u x) (raw_D a u)"
      by (rule raw_T_type[OF vw uw vu xm])
    have natural: "raw_T (Arr b Prop) v u (raw_app a (Arr b Prop) v (op_family v) x) =
      raw_app a (Arr b Prop) u (op_family u) (raw_T a v u x)"
      using raw_app_natural[where a=a and b="Arr b Prop" and F="op_family v" and x=x,
        OF vw uw vu typed_O xm] nat[OF vw uw vu] by simp
    show "V (Snd (Fst (Opair (Opair v u) (pc_enc b u y))))
        (paper_T a (Fst (Opair (Opair v u) (pc_enc b u y))) (pc_enc a v x))
        (Snd (Opair (Opair v u) (pc_enc b u y))) =
      pc_enc Prop u (raw_app b Prop u
        (raw_T (Arr b Prop) v u (raw_app a (Arr b Prop) v (op_family v) x)) y)"
      by (simp only: Fst Snd pc_T_enc[OF vw xm] natural val[OF uw xu ym])
  qed
  show ?thesis
    unfolding paper_ZF_pair_lambda_def
  proof (rule pc_enc_Lambda_characterization[OF ww])
    fix v x assume vw: "Elem v raw_W" and wv: "raw_rel w v"
      and xm: "Elem x (raw_D a v)"
    show "Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D b)
          (Snd (Fst (Opair (Opair w v) (pc_enc a v x)))))
        (\<lambda>z. V (Snd (Fst z))
          (paper_T a (Fst z) (Snd (Opair (Opair w v) (pc_enc a v x)))) (Snd z)) =
      pc_enc (Arr b Prop) v
        (raw_app a (Arr b Prop) v (raw_T (Arr a (Arr b Prop)) w v (op_family w)) x)"
      using partial[OF vw xm]
      by (simp only: Fst Snd nat[OF ww vw wv] paper_ZF_pair_lambda_def)
  qed
qed

lemma pc_eq_value:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)" and ym: "Elem y (raw_D a w)"
  shows "pc_enc Prop w (raw_app a Prop w (raw_app a (Arr a Prop) w (raw_eq a w) x) y) =
    Sep (paper_ZF_outgoing_code pa_Ar Fst w)
      (\<lambda>h. paper_T a h (pc_enc a w x) = paper_T a h (pc_enc a w y))"
proof (rule iffD2[OF Ext], intro allI)
  fix h
  show "Elem h (pc_enc Prop w (raw_app a Prop w (raw_app a (Arr a Prop) w (raw_eq a w) x) y)) =
    Elem h (Sep (paper_ZF_outgoing_code pa_Ar Fst w)
      (\<lambda>h. paper_T a h (pc_enc a w x) = paper_T a h (pc_enc a w y)))"
  proof (cases "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)")
    case True
    then obtain v where h: "h=Opair w v" and vw: "Elem v raw_W" and wv: "raw_rel w v"
      by (auto simp only: pc_outgoing_member)
    have outgoing: "Elem (Opair w v) (paper_ZF_outgoing_code pa_Ar Fst w)"
      using True by (simp only: h)
    have xv: "Elem (raw_T a w v x) (raw_D a v)" and yv: "Elem (raw_T a w v y) (raw_D a v)"
      by (rule raw_T_type[OF ww vw wv xm], rule raw_T_type[OF ww vw wv ym])
    have natural: "raw_T Prop w v (raw_app a Prop w (raw_app a (Arr a Prop) w (raw_eq a w) x) y) =
      raw_app a Prop v (raw_app a (Arr a Prop) v (raw_eq a v) (raw_T a w v x)) (raw_T a w v y)"
      using raw_app2_natural[where a=a and b=a and c=Prop and F="raw_eq a w",
        OF ww vw wv raw_eq_type xm ym] raw_eq_natural[OF ww vw wv] by simp
    have eq: "(pc_enc a v (raw_T a w v x) = pc_enc a v (raw_T a w v y)) =
      (raw_T a w v x = raw_T a w v y)"
      by (rule iffI, rule pc_enc_injective[OF vw xv yv], assumption, simp)
    show ?thesis
      by (simp only: h pc_prop_pair vw wv natural raw_eq_truth[OF xv yv]
        Sep outgoing pc_T_enc[OF ww xm] pc_T_enc[OF ww ym] eq simp_thms)
  next
    case False
    then show ?thesis using ww
      by (auto simp only: Sep pc_prop_member pc_outgoing_member)
  qed
qed

theorem pc_primitive_Eq:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (paper_logical_type (SEq a)) w (raw_primitive (SEq a) w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w (SEq a)"
  unfolding paper_logical_type.simps raw_primitive.simps paper_ZF_logical_value.simps
  by (rule pc_binary_graph[where a=a and b=a and op_family="raw_eq a",
        OF ww raw_eq_type raw_eq_natural pc_eq_value])

lemma pc_bool_value:
  assumes ww: "Elem w raw_W" and pm: "Elem p (raw_D Prop w)" and qm: "Elem q (raw_D Prop w)"
    and zero: "\<not> B False False"
    and mem: "\<And>h P Q. Elem h (V P Q) = B (Elem h P) (Elem h Q)"
  shows "pc_enc Prop w (raw_app Prop Prop w (raw_app Prop (Arr Prop Prop) w (raw_bool B w) p) q) =
    V (pc_enc Prop w p) (pc_enc Prop w q)"
proof (rule iffD2[OF Ext], intro allI)
  fix h
  show "Elem h (pc_enc Prop w (raw_app Prop Prop w (raw_app Prop (Arr Prop Prop) w (raw_bool B w) p) q)) =
    Elem h (V (pc_enc Prop w p) (pc_enc Prop w q))"
  proof (cases "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)")
    case True
    then obtain v where h: "h=Opair w v" and vw: "Elem v raw_W" and wv: "raw_rel w v"
      by (auto simp only: pc_outgoing_member)
    have pv: "Elem (raw_T Prop w v p) (raw_D Prop v)" and qv: "Elem (raw_T Prop w v q) (raw_D Prop v)"
      by (rule raw_T_type[OF ww vw wv pm], rule raw_T_type[OF ww vw wv qm])
    have natural: "raw_T Prop w v (raw_app Prop Prop w
        (raw_app Prop (Arr Prop Prop) w (raw_bool B w) p) q) =
      raw_app Prop Prop v (raw_app Prop (Arr Prop Prop) v (raw_bool B v)
        (raw_T Prop w v p)) (raw_T Prop w v q)"
      using raw_app2_natural[where a=Prop and b=Prop and c=Prop and F="raw_bool B w",
        OF ww vw wv raw_bool_type pm qm] raw_bool_natural[where B=B, OF ww vw wv] by simp
    show ?thesis
      by (simp only: h pc_prop_pair vw wv natural raw_bool_truth[where B=B, OF pv qv] mem simp_thms)
  next
    case False
    have ph: "\<not> Elem h (pc_enc Prop w p)" and qh: "\<not> Elem h (pc_enc Prop w q)"
      using False ww by (auto simp only: pc_prop_member pc_outgoing_member)
    have lh: "\<not> Elem h (pc_enc Prop w
      (raw_app Prop Prop w (raw_app Prop (Arr Prop Prop) w (raw_bool B w) p) q))"
      using False ww by (auto simp only: pc_prop_member pc_outgoing_member)
    show ?thesis by (simp only: mem ph qh lh zero)
  qed
qed

theorem pc_primitive_And:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (paper_logical_type SAnd) w (raw_primitive SAnd w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w SAnd"
  unfolding paper_logical_type.simps raw_primitive.simps paper_ZF_logical_value.simps
  apply (rule pc_binary_graph[where a=Prop and b=Prop and op_family="raw_bool (\<lambda>p q. p \<and> q)"
    and V="\<lambda>v P Q. Sep P (\<lambda>k. Elem k Q)"])
  subgoal by (rule ww)
  subgoal by (rule raw_bool_type)
  subgoal by (rule raw_bool_natural; assumption)
  subgoal for v x y
    by (rule pc_bool_value[where B="\<lambda>p q. p \<and> q"])
      (assumption, assumption, assumption, simp, simp only: Sep)
  done

theorem pc_primitive_Or:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (paper_logical_type SOr) w (raw_primitive SOr w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w SOr"
  unfolding paper_logical_type.simps raw_primitive.simps paper_ZF_logical_value.simps
  apply (rule pc_binary_graph[where a=Prop and b=Prop and op_family="raw_bool (\<lambda>p q. p \<or> q)"
    and V="\<lambda>v P Q. union P Q"])
  subgoal by (rule ww)
  subgoal by (rule raw_bool_type)
  subgoal by (rule raw_bool_natural; assumption)
  subgoal for v x y
    by (rule pc_bool_value[where B="\<lambda>p q. p \<or> q"])
      (assumption, assumption, assumption, simp, simp only: union)
  done

end
