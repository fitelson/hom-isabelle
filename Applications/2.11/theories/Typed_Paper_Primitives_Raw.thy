theory Typed_Paper_Primitives_Raw
  imports Typed_Paper_Primitives_Binary Typed_Paper_Primitives_Existential Typed_Source_Model
begin

definition raw_bool :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_bool B w = (if Nat2nat w=0 then ppb_r B else if Nat2nat w=1 then ppb_s B else ppb_m B)"

lemma raw_bool_type:
  "Elem (raw_bool B w) (raw_D (Arr Prop (Arr Prop Prop)) w)"
  using ppb_r_type[where B=B] ppb_s_type[where B=B] ppb_m_type[where B=B]
  by (simp add: raw_bool_def raw_D_def)

lemma raw_bool_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr Prop (Arr Prop Prop)) v w (raw_bool B v) = raw_bool B w"
  using rel
  by (auto simp: raw_T_def raw_bool_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      ppb_r_def ppb_s_def tc_rabs_def tc_sabs_def Fst Snd split: if_splits)

lemma raw_bool_truth:
  assumes pm: "Elem p (raw_D Prop w)" and qm: "Elem q (raw_D Prop w)"
  shows "raw_truth w (raw_app Prop Prop w
    (raw_app Prop (Arr Prop Prop) w (raw_bool B w) p) q) =
    B (raw_truth w p) (raw_truth w q)"
  using pm qm
  by (auto simp: raw_bool_def raw_app_def raw_D_def raw_truth_def bit_dec_def
      ppb_r_apply ppb_rval_def ppb_s_def ppb_sval_def ppb_m_def ppb_m1_def ppb_mval_def
      Lambda_app Fst Snd split: if_splits)

lemma raw_false_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T Prop v w (raw_false v) = raw_false w"
  using rel
  by (auto simp: raw_T_def raw_false_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      zprop_def zmiddle_def Fst Snd split: if_splits)

definition raw_not :: "ZF \<Rightarrow> ZF" where
  "raw_not w = raw_app Prop (Arr Prop Prop) w (raw_bool (\<lambda>p q. \<not> q) w) (raw_false w)"

lemma raw_not_type: "Elem (raw_not w) (raw_D (Arr Prop Prop) w)"
  unfolding raw_not_def by (rule raw_app_type[OF raw_bool_type raw_false_type])

lemma raw_not_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr Prop Prop) v w (raw_not v) = raw_not w"
  unfolding raw_not_def
  using raw_app_natural[where a=Prop and b="Arr Prop Prop" and v=v and w=w
    and F="raw_bool (\<lambda>p q. \<not> q) v" and x="raw_false v",
    OF vw ww rel raw_bool_type raw_false_type]
    raw_bool_natural[where B="\<lambda>p q. \<not> q", OF vw ww rel]
    raw_false_natural[OF vw ww rel]
  by simp

lemma raw_not_truth:
  assumes "Elem p (raw_D Prop w)"
  shows "raw_truth w (raw_app Prop Prop w (raw_not w) p) = (\<not> raw_truth w p)"
  unfolding raw_not_def
  by (rule raw_bool_truth[where B="\<lambda>p q. \<not> q", OF raw_false_type assms])

definition raw_ex :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_ex a w = (if Nat2nat w=0 then typed_rex a else
    if Nat2nat w=1 then typed_sex a else typed_mex a)"

lemma raw_ex_type: "Elem (raw_ex a w) (raw_D (Arr (Arr a Prop) Prop) w)"
  using typed_rex_type[of a] typed_sex_type[of a] typed_mex_type[of a]
  by (simp add: raw_ex_def raw_D_def)

lemma raw_ex_natural:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and rel: "raw_rel v w"
  shows "raw_T (Arr (Arr a Prop) Prop) v w (raw_ex a v) = raw_ex a w"
  using rel
  by (auto simp: raw_T_def raw_ex_def raw_world_eq[OF vw ww] raw_rel_codes[OF vw ww]
      typed_rex_def typed_sex_def Fst Snd split: if_splits)

lemma raw_ex_truth:
  assumes pm: "Elem P (raw_D (Arr a Prop) w)"
  shows "raw_truth w (raw_app (Arr a Prop) Prop w (raw_ex a w) P) =
    (\<exists>x. Elem x (raw_D a w) \<and> raw_truth w (raw_app a Prop w P x))"
  using pm typed_rex_truth[where a=a and P=P] typed_sex_truth[where a=a and P=P]
    typed_mex_truth[where a=a and P=P]
  by (auto simp: raw_ex_def raw_app_def raw_D_def raw_truth_def split: if_splits)

fun raw_primitive :: "paper_logical \<Rightarrow> ZF \<Rightarrow> ZF" where
  "raw_primitive SNot = raw_not"
| "raw_primitive SAnd = raw_bool (\<lambda>p q. p \<and> q)"
| "raw_primitive SOr = raw_bool (\<lambda>p q. p \<or> q)"
| "raw_primitive (SAll a) = raw_all a"
| "raw_primitive (SEx a) = raw_ex a"
| "raw_primitive (SEq a) = raw_eq a"

theorem raw_primitive_type:
  "Elem (raw_primitive l w) (raw_D (paper_logical_type l) w)"
  by (cases l; simp only: raw_primitive.simps paper_logical_type.simps;
      rule raw_not_type raw_bool_type raw_all_type raw_ex_type raw_eq_type)

theorem raw_primitive_natural:
  assumes "Elem v raw_W" "Elem w raw_W" "raw_rel v w"
  shows "raw_T (paper_logical_type l) v w (raw_primitive l v) = raw_primitive l w"
  by (cases l; simp only: raw_primitive.simps paper_logical_type.simps;
      rule raw_not_natural raw_bool_natural raw_all_natural raw_ex_natural raw_eq_natural;
      rule assms)

definition src_primitive :: "paper_logical \<Rightarrow> ZF" where
  "src_primitive l = src_enc (paper_logical_type l) raw_root (raw_primitive l raw_root)"

theorem src_primitive_type:
  "Elem (src_primitive l) (src_D (paper_logical_type l) raw_root)"
  unfolding src_primitive_def by (rule src_enc_type, rule raw_primitive_type)

lemma src_primitive_future:
  assumes ww: "Elem w raw_W"
  shows "src_T (paper_logical_type l) raw_root w (src_primitive l) =
    src_enc (paper_logical_type l) w (raw_primitive l w)"
proof -
  have rel: "raw_rel raw_root w" by (simp add: raw_rel_def)
  show ?thesis unfolding src_primitive_def
    by (simp only: src_T_enc[OF raw_worlds(1) raw_primitive_type]
        raw_primitive_natural[OF raw_worlds(1) ww rel])
qed

end
