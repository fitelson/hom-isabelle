theory Typed_Source_Binary
  imports Typed_Source_Encoding Typed_Raw_Operations
begin

section \<open>Equality and implication are the prescribed source graphs\<close>

lemma src_eq_value:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)" and ym: "Elem y (raw_D a w)"
  shows "src_enc Prop w (raw_app a Prop w
      (raw_app a (Arr a Prop) w (raw_eq a w) x) y) =
    book_ZF_collect raw_W raw_rel w (\<lambda>u.
      src_T a w u (src_enc a w x) = src_T a w u (src_enc a w y))"
proof (rule iffD2[OF Ext], intro allI)
  fix u
  have point: "raw_truth u (raw_T Prop w u
      (raw_app a Prop w (raw_app a (Arr a Prop) w (raw_eq a w) x) y)) =
    (src_T a w u (src_enc a w x) = src_T a w u (src_enc a w y))"
    if uw: "Elem u raw_W" and wu: "raw_rel w u"
  proof -
    have tx: "Elem (raw_T a w u x) (raw_D a u)" by (rule raw_T_type[OF ww uw wu xm])
    have ty: "Elem (raw_T a w u y) (raw_D a u)" by (rule raw_T_type[OF ww uw wu ym])
    have inject: "(src_enc a u (raw_T a w u x) = src_enc a u (raw_T a w u y)) =
      (raw_T a w u x = raw_T a w u y)"
    proof
      assume "src_enc a u (raw_T a w u x) = src_enc a u (raw_T a w u y)"
      then show "raw_T a w u x = raw_T a w u y"
        by (rule src_enc_injective[OF uw tx ty])
    next
      assume "raw_T a w u x = raw_T a w u y"
      then show "src_enc a u (raw_T a w u x) = src_enc a u (raw_T a w u y)"
        by simp
    qed
    have natural: "raw_T Prop w u
        (raw_app a Prop w (raw_app a (Arr a Prop) w (raw_eq a w) x) y) =
      raw_app a Prop u (raw_app a (Arr a Prop) u (raw_eq a u) (raw_T a w u x)) (raw_T a w u y)"
      using raw_app2_natural[where a=a and b=a and c=Prop and v=w and w=u
        and F="raw_eq a w" and x=x and y=y, OF ww uw wu raw_eq_type xm ym]
      by (simp only: raw_eq_natural[OF ww uw wu])
    show ?thesis
      by (simp only: natural raw_eq_truth[OF tx ty] src_T_enc[OF ww xm]
        src_T_enc[OF ww ym] inject)
  qed
  show "Elem u (src_enc Prop w (raw_app a Prop w
      (raw_app a (Arr a Prop) w (raw_eq a w) x) y)) =
    Elem u (book_ZF_collect raw_W raw_rel w (\<lambda>u.
      src_T a w u (src_enc a w x) = src_T a w u (src_enc a w y)))"
    using point by (auto simp only: src_enc_truth book_ZF_collect_member)
qed

lemma src_if_value:
  assumes ww: "Elem w raw_W" and pm: "Elem p (raw_D Prop w)" and qm: "Elem q (raw_D Prop w)"
  shows "src_enc Prop w (raw_app Prop Prop w
      (raw_app Prop (Arr Prop Prop) w (raw_if w) p) q) =
    book_ZF_collect raw_W raw_rel w (\<lambda>u.
      \<not> Elem u (src_enc Prop w p) \<or> Elem u (src_enc Prop w q))"
proof (rule iffD2[OF Ext], intro allI)
  fix u
  have point: "raw_truth u (raw_T Prop w u
      (raw_app Prop Prop w (raw_app Prop (Arr Prop Prop) w (raw_if w) p) q)) =
    (\<not> Elem u (src_enc Prop w p) \<or> Elem u (src_enc Prop w q))"
    if uw: "Elem u raw_W" and wu: "raw_rel w u"
  proof -
    have tp: "Elem (raw_T Prop w u p) (raw_D Prop u)" by (rule raw_T_type[OF ww uw wu pm])
    have tq: "Elem (raw_T Prop w u q) (raw_D Prop u)" by (rule raw_T_type[OF ww uw wu qm])
    have natural: "raw_T Prop w u
        (raw_app Prop Prop w (raw_app Prop (Arr Prop Prop) w (raw_if w) p) q) =
      raw_app Prop Prop u (raw_app Prop (Arr Prop Prop) u (raw_if u) (raw_T Prop w u p))
        (raw_T Prop w u q)"
      using raw_app2_natural[where a=Prop and b=Prop and c=Prop and v=w and w=u
        and F="raw_if w" and x=p and y=q, OF ww uw wu raw_if_type pm qm]
      by (simp only: raw_if_natural[OF ww uw wu])
    show ?thesis
      by (simp only: natural raw_if_truth[OF tp tq] src_enc_truth uw wu simp_thms)
  qed
  show "Elem u (src_enc Prop w (raw_app Prop Prop w
      (raw_app Prop (Arr Prop Prop) w (raw_if w) p) q)) =
    Elem u (book_ZF_collect raw_W raw_rel w (\<lambda>u.
      \<not> Elem u (src_enc Prop w p) \<or> Elem u (src_enc Prop w q)))"
    using point by (auto simp only: src_enc_truth book_ZF_collect_member)
qed

lemma src_eq_inner:
  assumes vw: "Elem v raw_W" and xm: "Elem x (raw_D a v)"
  shows "src_enc (Arr a Prop) v (raw_app a (Arr a Prop) v (raw_eq a v) x) =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D a) v)
      (\<lambda>q. book_ZF_collect raw_W raw_rel (Fst q) (\<lambda>z.
        src_T a v z (src_enc a v x) = src_T a (Fst q) z (Snd q)))"
proof (rule src_enc_Lambda_characterization)
  fix u y
  assume uw: "Elem u raw_W" and vu: "raw_rel v u" and ym: "Elem y (raw_D a u)"
  let ?tx = "raw_T a v u x"
  have tx: "Elem ?tx (raw_D a u)" by (rule raw_T_type[OF vw uw vu xm])
  have partial: "raw_T (Arr a Prop) v u (raw_app a (Arr a Prop) v (raw_eq a v) x) =
    raw_app a (Arr a Prop) u (raw_eq a u) ?tx"
    using raw_app_natural[where a=a and b="Arr a Prop" and v=v and w=u
      and F="raw_eq a v" and x=x, OF vw uw vu raw_eq_type xm]
    by (simp only: raw_eq_natural[OF vw uw vu])
  have transport: "src_T a v z (src_enc a v x) = src_T a u z (src_enc a u ?tx)"
    if zw: "Elem z raw_W" and uz: "raw_rel u z" for z
    using src_T_compose[OF vw uw zw vu uz src_enc_type[OF xm]]
    by (simp only: src_T_enc[OF vw xm])
  have collect: "book_ZF_collect raw_W raw_rel u (\<lambda>z.
      src_T a v z (src_enc a v x) = src_T a u z (src_enc a u y)) =
    book_ZF_collect raw_W raw_rel u (\<lambda>z.
      src_T a u z (src_enc a u ?tx) = src_T a u z (src_enc a u y))"
    by (rule iffD2[OF Ext], intro allI)
      (use transport in \<open>auto simp only: book_ZF_collect_member\<close>)
  show "book_ZF_collect raw_W raw_rel (Fst (Opair u (src_enc a u y))) (\<lambda>z.
      src_T a v z (src_enc a v x) = src_T a (Fst (Opair u (src_enc a u y))) z
        (Snd (Opair u (src_enc a u y)))) =
    src_enc Prop u (raw_app a Prop u
      (raw_T (Arr a Prop) v u (raw_app a (Arr a Prop) v (raw_eq a v) x)) y)"
    by (simp only: Fst Snd partial collect src_eq_value[OF uw tx ym])
qed

lemma src_if_inner:
  assumes vw: "Elem v raw_W" and pm: "Elem p (raw_D Prop v)"
  shows "src_enc (Arr Prop Prop) v (raw_app Prop (Arr Prop Prop) v (raw_if v) p) =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D Prop) v)
      (\<lambda>q. book_ZF_collect raw_W raw_rel (Fst q) (\<lambda>z.
        \<not> Elem z (src_T Prop v (Fst q) (src_enc Prop v p)) \<or> Elem z (Snd q)))"
proof (rule src_enc_Lambda_characterization)
  fix u q
  assume uw: "Elem u raw_W" and vu: "raw_rel v u" and qm: "Elem q (raw_D Prop u)"
  let ?tp = "raw_T Prop v u p"
  have tp: "Elem ?tp (raw_D Prop u)" by (rule raw_T_type[OF vw uw vu pm])
  have partial: "raw_T (Arr Prop Prop) v u (raw_app Prop (Arr Prop Prop) v (raw_if v) p) =
    raw_app Prop (Arr Prop Prop) u (raw_if u) ?tp"
    using raw_app_natural[where a=Prop and b="Arr Prop Prop" and v=v and w=u
      and F="raw_if v" and x=p, OF vw uw vu raw_if_type pm]
    by (simp only: raw_if_natural[OF vw uw vu])
  show "book_ZF_collect raw_W raw_rel (Fst (Opair u (src_enc Prop u q))) (\<lambda>z.
      \<not> Elem z (src_T Prop v (Fst (Opair u (src_enc Prop u q))) (src_enc Prop v p)) \<or>
        Elem z (Snd (Opair u (src_enc Prop u q)))) =
    src_enc Prop u (raw_app Prop Prop u
      (raw_T (Arr Prop Prop) v u (raw_app Prop (Arr Prop Prop) v (raw_if v) p)) q)"
    by (simp only: Fst Snd partial src_T_enc[OF vw pm] src_if_value[OF uw tp qm])
qed

theorem src_eq_graph:
  assumes ww: "Elem w raw_W"
  shows "src_enc (Arr a (Arr a Prop)) w (raw_eq a w) =
    book_ZF_eq raw_W raw_rel src_D src_T w a"
  unfolding book_ZF_eq_def
proof (rule src_enc_Lambda_characterization)
  fix v x
  assume vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (raw_D a v)"
  show "Lambda (book_ZF_pairs raw_W raw_rel (src_D a) (Fst (Opair v (src_enc a v x))))
      (\<lambda>q. book_ZF_collect raw_W raw_rel (Fst q) (\<lambda>u.
        src_T a (Fst (Opair v (src_enc a v x))) u (Snd (Opair v (src_enc a v x))) =
          src_T a (Fst q) u (Snd q))) =
    src_enc (Arr a Prop) v (raw_app a (Arr a Prop) v
      (raw_T (Arr a (Arr a Prop)) w v (raw_eq a w)) x)"
    by (simp only: Fst Snd raw_eq_natural[OF ww vw wv] src_eq_inner[OF vw xm])
qed

theorem src_if_graph:
  assumes ww: "Elem w raw_W"
  shows "src_enc (Arr Prop (Arr Prop Prop)) w (raw_if w) =
    book_ZF_if_future raw_W raw_rel src_D src_T w"
  unfolding book_ZF_if_future_def
proof (rule src_enc_Lambda_characterization)
  fix v p
  assume vw: "Elem v raw_W" and wv: "raw_rel w v" and pm: "Elem p (raw_D Prop v)"
  show "Lambda (book_ZF_pairs raw_W raw_rel (src_D Prop) (Fst (Opair v (src_enc Prop v p))))
      (\<lambda>q. book_ZF_collect raw_W raw_rel (Fst q) (\<lambda>u.
        \<not> Elem u (src_T Prop (Fst (Opair v (src_enc Prop v p))) (Fst q)
          (Snd (Opair v (src_enc Prop v p)))) \<or> Elem u (Snd q))) =
    src_enc (Arr Prop Prop) v (raw_app Prop (Arr Prop Prop) v
      (raw_T (Arr Prop (Arr Prop Prop)) w v (raw_if w)) p)"
    by (simp only: Fst Snd raw_if_natural[OF ww vw wv] src_if_inner[OF vw pm])
qed

theorem src_eq_member:
  assumes "Elem w raw_W"
  shows "Elem (book_ZF_eq raw_W raw_rel src_D src_T w a) (src_D (Arr a (Arr a Prop)) w)"
  using src_enc_type[OF raw_eq_type[of a w]]
  by (simp only: src_eq_graph[OF assms])

theorem src_if_member:
  assumes "Elem w raw_W"
  shows "Elem (book_ZF_if_future raw_W raw_rel src_D src_T w) (src_D (Arr Prop (Arr Prop Prop)) w)"
  using src_enc_type[OF raw_if_type[of w]]
  by (simp only: src_if_graph[OF assms])

end
