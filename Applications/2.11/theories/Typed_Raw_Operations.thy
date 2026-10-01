theory Typed_Raw_Operations
  imports Typed_Source_Frame
begin

definition raw_K :: "otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_K a b w = (if Nat2nat w=0 then tc_rK a b else
    if Nat2nat w=1 then tc_sK a b else tc_mK a b)"

definition raw_S :: "otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_S a b c w = (if Nat2nat w=0 then tc_rS a b c else
    if Nat2nat w=1 then tc_sS a b c else tc_mS a b c)"

definition raw_if :: "ZF \<Rightarrow> ZF" where
  "raw_if w = (if Nat2nat w=0 then ti_r else if Nat2nat w=1 then ti_s else ti_m)"

definition raw_all :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_all a w = (if Nat2nat w=0 then typed_rall a else
    if Nat2nat w=1 then typed_sall a else typed_mall a)"

definition raw_eq :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_eq a w = (if Nat2nat w=0 then typed_req a else
    if Nat2nat w=1 then typed_seqeq a else typed_meq a)"

lemma raw_K_type: "Elem (raw_K a b w) (raw_D (Arr a (Arr b a)) w)"
  using tc_rK_type[of a b] tc_sK_type[of a b] tc_mK_type[of a b]
  by (simp add: raw_K_def raw_D_def)

lemma raw_S_type:
  "Elem (raw_S a b c w) (raw_D (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) w)"
  using tc_rS_type[of a b c] tc_sS_type[of a b c] tc_mS_type[of a b c]
  by (simp add: raw_S_def raw_D_def)

lemma raw_if_type: "Elem (raw_if w) (raw_D (Arr Prop (Arr Prop Prop)) w)"
  using ti_r_type ti_s_type ti_m_type by (simp add: raw_if_def raw_D_def)

lemma raw_all_type: "Elem (raw_all a w) (raw_D (Arr (Arr a Prop) Prop) w)"
  using typed_rall_type[of a] typed_sall_type[of a] typed_mall_type[of a]
  by (simp add: raw_all_def raw_D_def)

lemma raw_eq_type: "Elem (raw_eq a w) (raw_D (Arr a (Arr a Prop)) w)"
  using typed_req_type[of a] typed_seqeq_type[of a] typed_meq_type[of a]
  by (simp add: raw_eq_def raw_D_def)

lemma raw_K_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr a (Arr b a)) v w (raw_K a b v) = raw_K a b w"
  using rel
  by (auto simp: raw_T_def raw_K_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      tc_rK_def tc_sK_def tc_rabs_def tc_sabs_def Fst Snd split: if_splits)

lemma raw_S_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) v w
    (raw_S a b c v) = raw_S a b c w"
  using rel
  by (auto simp: raw_T_def raw_S_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      tc_rS_def tc_sS_def tc_rabs_def tc_sabs_def Fst Snd split: if_splits)

lemma raw_if_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr Prop (Arr Prop Prop)) v w (raw_if v) = raw_if w"
  using rel
  by (auto simp: raw_T_def raw_if_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      ti_r_def ti_s_def tc_rabs_def tc_sabs_def Fst Snd split: if_splits)

lemma raw_all_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr (Arr a Prop) Prop) v w (raw_all a v) = raw_all a w"
  using rel
  by (auto simp: raw_T_def raw_all_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      typed_rall_def typed_sall_def Fst Snd split: if_splits)

lemma raw_eq_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr a (Arr a Prop)) v w (raw_eq a v) = raw_eq a w"
  using rel
  by (auto simp: raw_T_def raw_eq_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      typed_req_def typed_seqeq_def Fst Snd split: if_splits)

lemma raw_K_apply:
  assumes xm: "Elem x (raw_D a w)" and ym: "Elem y (raw_D b w)"
  shows "raw_app b a w (raw_app a (Arr b a) w (raw_K a b w) x) y = x"
  using xm ym
  by (auto simp: raw_app_def raw_D_def raw_K_def tc_rK_def tc_sK_def tc_mK_def
      Lambda_app split: if_splits)

lemma raw_S_apply:
  assumes fm: "Elem f (raw_D (Arr a (Arr b c)) w)"
    and gm: "Elem g (raw_D (Arr a b) w)" and xm: "Elem x (raw_D a w)"
  shows "raw_app a c w
    (raw_app (Arr a b) (Arr a c) w
      (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) w (raw_S a b c w) f) g) x =
    raw_app b c w (raw_app a (Arr b c) w f x) (raw_app a b w g x)"
  using fm gm xm
  by (auto simp: raw_app_def raw_D_def raw_S_def tc_rS_def tc_sS_def tc_mS_def
      Lambda_app split: if_splits)

lemma raw_all_truth:
  assumes pm: "Elem P (raw_D (Arr a Prop) w)"
  shows "raw_truth w (raw_app (Arr a Prop) Prop w (raw_all a w) P) =
    (\<forall>x. Elem x (raw_D a w) \<longrightarrow> raw_truth w (raw_app a Prop w P x))"
  using pm typed_rall_truth[where a=a and P=P] typed_sall_truth[where a=a and P=P]
    typed_mall_truth[where a=a and P=P]
  by (auto simp: raw_all_def raw_app_def raw_D_def raw_truth_def split: if_splits)

lemma raw_if_truth:
  assumes pm: "Elem p (raw_D Prop w)" and qm: "Elem q (raw_D Prop w)"
  shows "raw_truth w (raw_app Prop Prop w
    (raw_app Prop (Arr Prop Prop) w (raw_if w) p) q) =
    (\<not> raw_truth w p \<or> raw_truth w q)"
  using pm qm
  by (auto simp: raw_if_def raw_app_def raw_D_def raw_truth_def bit_dec_def
      ti_r_apply ti_rval_def ti_s_def ti_sval_def ti_m_def ti_m1_def ti_mval_def
      Lambda_app Fst Snd split: if_splits)

lemma raw_eq_truth:
  assumes xm: "Elem x (raw_D a w)" and ym: "Elem y (raw_D a w)"
  shows "raw_truth w (raw_app a Prop w
    (raw_app a (Arr a Prop) w (raw_eq a w) x) y) = (x=y)"
  using xm ym
  by (auto simp: raw_eq_def raw_app_def raw_D_def raw_truth_def bit_dec_def
      typed_req_apply typed_reqval_def typed_seqeq_apply typed_seqval_def
      typed_meq_apply Fst split: if_splits)

lemma raw_app2_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
    and fm: "Elem F (raw_D (Arr a (Arr b c)) v)"
    and xm: "Elem x (raw_D a v)" and ym: "Elem y (raw_D b v)"
  shows "raw_T c v w (raw_app b c v (raw_app a (Arr b c) v F x) y) =
    raw_app b c w (raw_app a (Arr b c) w (raw_T (Arr a (Arr b c)) v w F)
      (raw_T a v w x)) (raw_T b v w y)"
proof -
  have first: "Elem (raw_app a (Arr b c) v F x) (raw_D (Arr b c) v)"
    by (rule raw_app_type[OF fm xm])
  show ?thesis
    using raw_app_natural[where a=b and b=c and v=v and w=w
      and F="raw_app a (Arr b c) v F x" and x=y, OF vw ww rel first ym]
      raw_app_natural[where a=a and b="Arr b c" and v=v and w=w
      and F=F and x=x, OF vw ww rel fm xm]
    by simp
qed

end
