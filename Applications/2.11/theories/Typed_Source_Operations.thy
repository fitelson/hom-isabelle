theory Typed_Source_Operations
  imports Typed_Source_Encoding Typed_Raw_Operations
    "Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Operations"
begin

section \<open>The prescribed universal graph is an encoded carrier member\<close>

lemma src_future_predicate_all:
  assumes uw: "Elem u raw_W" and wu: "raw_rel w u"
  shows "(\<forall>y\<in>explode (src_D a u).
      Elem u (app (src_enc (Arr a Prop) w P) (Opair u y))) =
    (\<forall>x. Elem x (raw_D a u) \<longrightarrow>
      raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x))"
proof -
  have point: "Elem u (app (src_enc (Arr a Prop) w P) (Opair u (src_enc a u x))) =
    raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x)"
    if xm: "Elem x (raw_D a u)" for x
    using src_enc_app[where a=a and b=Prop and v=u and w=w and x=x and F=P,
      OF uw wu xm]
    by (simp only: src_enc_truth uw raw_rel_refl raw_T_id simp_thms)
  show ?thesis
  proof
    assume all: "\<forall>y\<in>explode (src_D a u).
      Elem u (app (src_enc (Arr a Prop) w P) (Opair u y))"
    show "\<forall>x. Elem x (raw_D a u) \<longrightarrow>
      raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x)"
    proof (intro allI impI)
      fix x assume xm: "Elem x (raw_D a u)"
      have enc: "src_enc a u x \<in> explode (src_D a u)"
        using src_enc_type[OF xm] by (simp only: explode_Elem)
      have "Elem u (app (src_enc (Arr a Prop) w P) (Opair u (src_enc a u x)))"
        by (rule bspec[OF all enc])
      then show "raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x)"
        by (simp only: point[OF xm])
    qed
  next
    assume all: "\<forall>x. Elem x (raw_D a u) \<longrightarrow>
      raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x)"
    show "\<forall>y\<in>explode (src_D a u).
      Elem u (app (src_enc (Arr a Prop) w P) (Opair u y))"
    proof (intro ballI)
      fix y assume ym: "y \<in> explode (src_D a u)"
      have "Elem y (src_D a u)" using ym by (simp only: explode_Elem)
      then obtain x where xm: "Elem x (raw_D a u)" and y: "y = src_enc a u x"
        unfolding src_D_member by blast
      have "raw_truth u (raw_app a Prop u (raw_T (Arr a Prop) w u P) x)"
        by (rule mp[OF spec[OF all, of x] xm])
      then show "Elem u (app (src_enc (Arr a Prop) w P) (Opair u y))"
        by (simp only: y point[OF xm])
    qed
  qed
qed

section \<open>The prescribed K graph\<close>

lemma src_K_partial:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)"
  shows "src_enc (Arr b a) w (raw_app a (Arr b a) w (raw_K a b w) x) =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D b) w)
      (\<lambda>q. src_T a w (Fst q) (src_enc a w x))"
proof (rule src_enc_Lambda_characterization)
  fix u y assume uw: "Elem u raw_W" and wu: "raw_rel w u"
    and ym: "Elem y (raw_D b u)"
  have tx: "Elem (raw_T a w u x) (raw_D a u)"
    by (rule raw_T_type[OF ww uw wu xm])
  have moved: "raw_T (Arr b a) w u (raw_app a (Arr b a) w (raw_K a b w) x) =
    raw_app a (Arr b a) u (raw_K a b u) (raw_T a w u x)"
    using raw_app_natural[where a=a and b="Arr b a" and v=w and w=u
      and F="raw_K a b w" and x=x, OF ww uw wu raw_K_type xm]
      raw_K_natural[where a=a and b=b, OF ww uw wu] by simp
  show "src_T a w (Fst (Opair u (src_enc b u y))) (src_enc a w x) =
    src_enc a u (raw_app b a u
      (raw_T (Arr b a) w u (raw_app a (Arr b a) w (raw_K a b w) x)) y)"
    by (simp only: Fst src_T_enc[OF ww xm] moved raw_K_apply[OF tx ym])
qed

theorem src_prescribed_K:
  assumes ww: "Elem w raw_W"
  shows "src_enc (Arr a (Arr b a)) w (raw_K a b w) =
    book_ZF_k raw_W raw_rel src_D src_T w a b"
  unfolding book_ZF_k_def
proof (rule src_enc_Lambda_characterization)
  fix v x assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and xm: "Elem x (raw_D a v)"
  show "Lambda (book_ZF_pairs raw_W raw_rel (src_D b) (Fst (Opair v (src_enc a v x))))
      (\<lambda>q. src_T a (Fst (Opair v (src_enc a v x))) (Fst q)
        (Snd (Opair v (src_enc a v x)))) =
    src_enc (Arr b a) v (raw_app a (Arr b a) v
      (raw_T (Arr a (Arr b a)) w v (raw_K a b w)) x)"
    using src_K_partial[where w=v and a=a and b=b and x=x, OF vw xm]
    by (simp only: Fst Snd raw_K_natural[OF ww vw wv])
qed

theorem src_K_member:
  assumes "Elem w raw_W"
  shows "Elem (book_ZF_k raw_W raw_rel src_D src_T w a b)
    (src_D (Arr a (Arr b a)) w)"
  using src_enc_type[OF raw_K_type[where a=a and b=b and w=w]]
  by (simp only: src_prescribed_K[OF assms])

section \<open>The prescribed S graph\<close>

lemma src_S_second_partial:
  assumes vw: "Elem v raw_W" and ww: "Elem w raw_W" and vwrel: "raw_rel v w"
    and fm: "Elem f (raw_D (Arr a (Arr b c)) v)"
    and gm: "Elem g (raw_D (Arr a b) w)"
  shows "src_enc (Arr a c) w
    (raw_app (Arr a b) (Arr a c) w
      (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) w
        (raw_S a b c w) (raw_T (Arr a (Arr b c)) v w f)) g) =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w)
      (\<lambda>r. app (app (src_enc (Arr a (Arr b c)) v f) (Opair (Fst r) (Snd r)))
        (Opair (Fst r) (app (src_enc (Arr a b) w g) (Opair (Fst r) (Snd r)))))"
proof (rule src_enc_Lambda_characterization)
  fix u x assume uw: "Elem u raw_W" and wu: "raw_rel w u"
    and xm: "Elem x (raw_D a u)"
  have vu: "raw_rel v u" by (rule raw_rel_trans[OF vwrel wu])
  have fw: "Elem (raw_T (Arr a (Arr b c)) v w f) (raw_D (Arr a (Arr b c)) w)"
    by (rule raw_T_type[OF vw ww vwrel fm])
  have fu: "Elem (raw_T (Arr a (Arr b c)) v u f) (raw_D (Arr a (Arr b c)) u)"
    by (rule raw_T_type[OF vw uw vu fm])
  have gu: "Elem (raw_T (Arr a b) w u g) (raw_D (Arr a b) u)"
    by (rule raw_T_type[OF ww uw wu gm])
  have gx: "Elem (raw_app a b u (raw_T (Arr a b) w u g) x) (raw_D b u)"
    by (rule raw_app_type[OF gu xm])
  have move:
    "raw_T (Arr a c) w u
      (raw_app (Arr a b) (Arr a c) w
        (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) w
          (raw_S a b c w) (raw_T (Arr a (Arr b c)) v w f)) g) =
      raw_app (Arr a b) (Arr a c) u
        (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) u
          (raw_S a b c u) (raw_T (Arr a (Arr b c)) v u f)) (raw_T (Arr a b) w u g)"
    using raw_app2_natural[where a="Arr a (Arr b c)" and b="Arr a b" and c="Arr a c"
      and v=w and w=u and F="raw_S a b c w" and x="raw_T (Arr a (Arr b c)) v w f" and y=g,
      OF ww uw wu raw_S_type fw gm]
      raw_S_natural[where a=a and b=b and c=c, OF ww uw wu]
      raw_T_compose[where a="Arr a (Arr b c)" and x=f, OF vw ww uw vwrel wu]
    by simp
  have ef:
    "app (src_enc (Arr a (Arr b c)) v f) (Opair u (src_enc a u x)) =
      src_enc (Arr b c) u (raw_app a (Arr b c) u (raw_T (Arr a (Arr b c)) v u f) x)"
    by (rule src_enc_app[OF uw vu xm])
  have eg:
    "app (src_enc (Arr a b) w g) (Opair u (src_enc a u x)) =
      src_enc b u (raw_app a b u (raw_T (Arr a b) w u g) x)"
    by (rule src_enc_app[OF uw wu xm])
  have last:
    "app (src_enc (Arr b c) u (raw_app a (Arr b c) u (raw_T (Arr a (Arr b c)) v u f) x))
      (Opair u (src_enc b u (raw_app a b u (raw_T (Arr a b) w u g) x))) =
      src_enc c u (raw_app b c u
        (raw_app a (Arr b c) u (raw_T (Arr a (Arr b c)) v u f) x)
        (raw_app a b u (raw_T (Arr a b) w u g) x))"
    using src_enc_app[where a=b and b=c and v=u and w=u
      and F="raw_app a (Arr b c) u (raw_T (Arr a (Arr b c)) v u f) x"
      and x="raw_app a b u (raw_T (Arr a b) w u g) x", OF uw raw_rel_refl gx]
    by (simp only: raw_T_id)
  show "app (app (src_enc (Arr a (Arr b c)) v f)
      (Opair (Fst (Opair u (src_enc a u x))) (Snd (Opair u (src_enc a u x)))))
      (Opair (Fst (Opair u (src_enc a u x)))
        (app (src_enc (Arr a b) w g)
          (Opair (Fst (Opair u (src_enc a u x))) (Snd (Opair u (src_enc a u x)))))) =
    src_enc c u (raw_app a c u
      (raw_T (Arr a c) w u
        (raw_app (Arr a b) (Arr a c) w
          (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) w
            (raw_S a b c w) (raw_T (Arr a (Arr b c)) v w f)) g)) x)"
    by (simp only: Fst Snd ef eg last move raw_S_apply[OF fu gu xm])
qed

lemma src_S_first_partial:
  assumes vw: "Elem v raw_W" and fm: "Elem f (raw_D (Arr a (Arr b c)) v)"
  shows "src_enc (Arr (Arr a b) (Arr a c)) v
    (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) v (raw_S a b c v) f) =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D (Arr a b)) v)
      (\<lambda>q. Lambda (book_ZF_pairs raw_W raw_rel (src_D a) (Fst q))
        (\<lambda>r. app (app (src_enc (Arr a (Arr b c)) v f) (Opair (Fst r) (Snd r)))
          (Opair (Fst r) (app (Snd q) (Opair (Fst r) (Snd r))))))"
proof (rule src_enc_Lambda_characterization)
  fix w g assume ww: "Elem w raw_W" and vwrel: "raw_rel v w"
    and gm: "Elem g (raw_D (Arr a b) w)"
  have move: "raw_T (Arr (Arr a b) (Arr a c)) v w
      (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) v (raw_S a b c v) f) =
    raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) w
      (raw_S a b c w) (raw_T (Arr a (Arr b c)) v w f)"
    using raw_app_natural[where a="Arr a (Arr b c)" and b="Arr (Arr a b) (Arr a c)"
      and v=v and w=w and F="raw_S a b c v" and x=f, OF vw ww vwrel raw_S_type fm]
      raw_S_natural[where a=a and b=b and c=c, OF vw ww vwrel] by simp
  show "Lambda (book_ZF_pairs raw_W raw_rel (src_D a) (Fst (Opair w (src_enc (Arr a b) w g))))
      (\<lambda>r. app (app (src_enc (Arr a (Arr b c)) v f) (Opair (Fst r) (Snd r)))
        (Opair (Fst r) (app (Snd (Opair w (src_enc (Arr a b) w g))) (Opair (Fst r) (Snd r))))) =
    src_enc (Arr a c) w (raw_app (Arr a b) (Arr a c) w
      (raw_T (Arr (Arr a b) (Arr a c)) v w
        (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) v (raw_S a b c v) f)) g)"
    using src_S_second_partial[where a=a and b=b and c=c and v=v and w=w and f=f and g=g,
      OF vw ww vwrel fm gm]
    by (simp only: Fst Snd move)
qed

theorem src_prescribed_S:
  assumes ww: "Elem w raw_W"
  shows "src_enc (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) w (raw_S a b c w) =
    book_ZF_s raw_W raw_rel src_D w a b c"
  unfolding book_ZF_s_def
proof (rule src_enc_Lambda_characterization)
  fix v f assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and fm: "Elem f (raw_D (Arr a (Arr b c)) v)"
  show "Lambda (book_ZF_pairs raw_W raw_rel (src_D (Arr a b))
      (Fst (Opair v (src_enc (Arr a (Arr b c)) v f))))
      (\<lambda>q. Lambda (book_ZF_pairs raw_W raw_rel (src_D a) (Fst q))
        (\<lambda>r. app (app (Snd (Opair v (src_enc (Arr a (Arr b c)) v f))) (Opair (Fst r) (Snd r)))
          (Opair (Fst r) (app (Snd q) (Opair (Fst r) (Snd r)))))) =
    src_enc (Arr (Arr a b) (Arr a c)) v
      (raw_app (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c)) v
        (raw_T (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) w v (raw_S a b c w)) f)"
    using src_S_first_partial[where a=a and b=b and c=c and v=v and f=f, OF vw fm]
    by (simp only: Fst Snd raw_S_natural[OF ww vw wv])
qed

theorem src_S_member:
  assumes "Elem w raw_W"
  shows "Elem (book_ZF_s raw_W raw_rel src_D w a b c)
    (src_D (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) w)"
  using src_enc_type[OF raw_S_type[where a=a and b=b and c=c and w=w]]
  by (simp only: src_prescribed_S[OF assms])

lemma src_all_value:
  assumes ww: "Elem w raw_W" and pm: "Elem P (raw_D (Arr a Prop) w)"
  shows "src_enc Prop w (raw_app (Arr a Prop) Prop w (raw_all a w) P) =
    book_ZF_collect raw_W raw_rel w
      (\<lambda>u. \<forall>y\<in>explode (src_D a u).
        Elem u (app (src_enc (Arr a Prop) w P) (Opair u y)))"
proof (rule iffD2[OF Ext], intro allI)
  fix u
  show "Elem u (src_enc Prop w (raw_app (Arr a Prop) Prop w (raw_all a w) P)) =
    Elem u (book_ZF_collect raw_W raw_rel w
      (\<lambda>u. \<forall>y\<in>explode (src_D a u).
        Elem u (app (src_enc (Arr a Prop) w P) (Opair u y))))"
  proof (cases "Elem u raw_W \<and> raw_rel w u")
    case True
    then have uw: "Elem u raw_W" and wu: "raw_rel w u" by auto
    have pmu: "Elem (raw_T (Arr a Prop) w u P) (raw_D (Arr a Prop) u)"
      by (rule raw_T_type[OF ww uw wu pm])
    have natural: "raw_T Prop w u (raw_app (Arr a Prop) Prop w (raw_all a w) P) =
      raw_app (Arr a Prop) Prop u (raw_all a u) (raw_T (Arr a Prop) w u P)"
      using raw_app_natural[where a="Arr a Prop" and b=Prop and v=w and w=u
        and F="raw_all a w" and x=P, OF ww uw wu raw_all_type pm]
        raw_all_natural[where a=a, OF ww uw wu] by simp
    show ?thesis
      by (simp only: src_enc_truth book_ZF_collect_member uw wu natural
          raw_all_truth[OF pmu] src_future_predicate_all[OF uw wu] simp_thms)
  next
    case False
    then show ?thesis by (simp only: src_enc_truth book_ZF_collect_member) auto
  qed
qed

theorem src_prescribed_all:
  assumes ww: "Elem w raw_W"
  shows "src_enc (Arr (Arr a Prop) Prop) w (raw_all a w) =
    book_ZF_all raw_W raw_rel src_D w a"
proof (unfold src_enc_arrow book_ZF_all_def,
    rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
  fix p
  assume pp: "Elem p (book_ZF_pairs raw_W raw_rel (src_D (Arr a Prop)) w)"
  have vw: "Elem (Fst p) raw_W" and wv: "raw_rel w (Fst p)"
    and pm: "Elem (Snd p) (src_D (Arr a Prop) (Fst p))"
    by (rule book_ZF_pairs_data[OF pp])+
  have dm: "Elem (src_dec (Arr a Prop) (Fst p) (Snd p)) (raw_D (Arr a Prop) (Fst p))"
    by (rule src_dec_type[OF pm])
  have inverse: "src_enc (Arr a Prop) (Fst p) (src_dec (Arr a Prop) (Fst p) (Snd p)) = Snd p"
    by (rule src_enc_dec[OF pm])
  have natural: "raw_T (Arr (Arr a Prop) Prop) w (Fst p) (raw_all a w) = raw_all a (Fst p)"
    by (rule raw_all_natural[OF ww vw wv])
  show "src_enc Prop (Fst p)
      (raw_app (Arr a Prop) Prop (Fst p)
        (raw_T (Arr (Arr a Prop) Prop) w (Fst p) (raw_all a w))
        (src_dec (Arr a Prop) (Fst p) (Snd p))) =
    book_ZF_collect raw_W raw_rel (Fst p)
      (\<lambda>v. \<forall>y\<in>explode (src_D a v). Elem v (app (Snd p) (Opair v y)))"
    using src_all_value[where w="Fst p" and a=a
      and P="src_dec (Arr a Prop) (Fst p) (Snd p)", OF vw dm]
    by (simp only: natural inverse)
qed

theorem src_all_member:
  assumes "Elem w raw_W"
  shows "Elem (book_ZF_all raw_W raw_rel src_D w a) (src_D (Arr (Arr a Prop) Prop) w)"
  using src_enc_type[OF raw_all_type[where a=a and w=w]]
  by (simp only: src_prescribed_all[OF assms])

text \<open>This endpoint identifies the prescribed book universal graph,
  not an arbitrary operator with assumed behavior. The equality was proved
  at every world by extensionality of actual function graphs and future
  subsets, using the concrete raw quantifier membership and naturality.
  The other prescribed operations and the complete model interpretation
  remain separate obligations.\<close>

end
