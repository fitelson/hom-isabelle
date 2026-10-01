theory Typed_Source_Encoding
  imports Typed_Source_Frame
    "Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Modal_Structure"
begin

section \<open>One recursive encoding into literal future subsets and graphs\<close>

primrec src_enc :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "src_enc Ind = (\<lambda>w x. x)"
| "src_enc Prop = (\<lambda>w p. book_ZF_collect raw_W raw_rel w
    (\<lambda>v. raw_truth v (raw_T Prop w v p)))"
| "src_enc (Arr a b) = (\<lambda>w F.
    Lambda (book_ZF_pairs raw_W raw_rel (\<lambda>v. Repl (raw_D a v) (src_enc a v)) w)
      (\<lambda>p. src_enc b (Fst p)
        (raw_app a b (Fst p) (raw_T (Arr a b) w (Fst p) F)
          (SOME x. Elem x (raw_D a (Fst p)) \<and> src_enc a (Fst p) x = Snd p))))"

definition src_D :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "src_D a w = Repl (raw_D a w) (src_enc a w)"

lemma src_D_function:
  "src_D a = (\<lambda>w. Repl (raw_D a w) (src_enc a w))"
  by (rule ext) (rule src_D_def)

definition src_dec :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "src_dec a w y = (SOME x. Elem x (raw_D a w) \<and> src_enc a w x = y)"

definition src_T :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "src_T a w v y = src_enc a v (raw_T a w v (src_dec a w y))"

lemma src_D_member:
  "Elem y (src_D a w) \<longleftrightarrow> (\<exists>x. Elem x (raw_D a w) \<and> y = src_enc a w x)"
  by (simp only: src_D_def Repl)

lemma src_enc_type:
  "Elem x (raw_D a w) \<Longrightarrow> Elem (src_enc a w x) (src_D a w)"
  by (auto simp only: src_D_member)

lemma src_dec_spec:
  assumes "Elem y (src_D a w)"
  shows "Elem (src_dec a w y) (raw_D a w) \<and> src_enc a w (src_dec a w y) = y"
proof -
  have "\<exists>x. Elem x (raw_D a w) \<and> src_enc a w x = y"
    using assms by (auto simp only: src_D_member)
  then show ?thesis unfolding src_dec_def by (rule someI_ex)
qed

lemma src_dec_type:
  "Elem y (src_D a w) \<Longrightarrow> Elem (src_dec a w y) (raw_D a w)"
  using src_dec_spec by blast

lemma src_enc_dec:
  "Elem y (src_D a w) \<Longrightarrow> src_enc a w (src_dec a w y) = y"
  using src_dec_spec by blast

lemma src_dec_enc_given_injective:
  assumes xm: "Elem x (raw_D a w)"
    and inj: "\<And>u v. Elem u (raw_D a w) \<Longrightarrow> Elem v (raw_D a w) \<Longrightarrow>
      src_enc a w u = src_enc a w v \<Longrightarrow> u = v"
  shows "src_dec a w (src_enc a w x) = x"
proof -
  have enc: "Elem (src_enc a w x) (src_D a w)" by (rule src_enc_type[OF xm])
  show ?thesis by (rule inj[OF src_dec_type[OF enc] xm src_enc_dec[OF enc]])
qed

lemma src_enc_arrow:
  "src_enc (Arr a b) w F = Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w)
    (\<lambda>p. src_enc b (Fst p)
      (raw_app a b (Fst p) (raw_T (Arr a b) w (Fst p) F) (src_dec a (Fst p) (Snd p))))"
  by (simp only: src_enc.simps src_D_function src_dec_def)

lemma src_enc_truth:
  "Elem v (src_enc Prop w p) \<longleftrightarrow>
    Elem v raw_W \<and> raw_rel w v \<and> raw_truth v (raw_T Prop w v p)"
  by (simp only: src_enc.simps book_ZF_collect_member)

lemma src_enc_future_apply_given_injective:
  assumes vw: "Elem v raw_W" and wv: "raw_rel w v" and xm: "Elem x (raw_D a v)"
    and inj: "\<And>u z. Elem u (raw_D a v) \<Longrightarrow> Elem z (raw_D a v) \<Longrightarrow>
      src_enc a v u = src_enc a v z \<Longrightarrow> u = z"
  shows "app (src_enc (Arr a b) w F) (Opair v (src_enc a v x)) =
    src_enc b v (raw_app a b v (raw_T (Arr a b) w v F) x)"
proof -
  have pair: "Elem (Opair v (src_enc a v x)) (book_ZF_pairs raw_W raw_rel (src_D a) w)"
    using vw wv src_enc_type[OF xm] by (simp only: book_ZF_pairs_member)
  have dec: "src_dec a v (src_enc a v x) = x"
    by (rule src_dec_enc_given_injective[OF xm inj])
  show ?thesis by (simp only: src_enc_arrow Lambda_app[OF pair] Fst Snd dec)
qed

text \<open>The inverse above is obtained by bounded choice on an actual
  domain set. The recursion contains the choice inline, so it does not
  assume a decoder before the recursively defined encoding exists.\<close>

theorem src_enc_injective:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)"
    and ym: "Elem y (raw_D a w)" and eq: "src_enc a w x = src_enc a w y"
  shows "x = y"
  using ww xm ym eq
proof (induction a arbitrary: w x y)
  case Ind
  then show ?case by (simp only: src_enc.simps)
next
  case Prop
  show ?case
  proof (rule raw_truth_separates)
    show "Elem w raw_W" by (rule Prop.prems(1))
    show "Elem x (raw_D Prop w)" by (rule Prop.prems(2))
    show "Elem y (raw_D Prop w)" by (rule Prop.prems(3))
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    have "Elem v (src_enc Prop w x) = Elem v (src_enc Prop w y)"
      by (simp only: Prop.prems(4))
    then show "raw_truth v (raw_T Prop w v x) = raw_truth v (raw_T Prop w v y)"
      by (simp only: src_enc_truth vw wv simp_thms)
  qed
next
  case (Arr a b)
  show ?case
  proof (rule raw_app_extensional[where a=a and b=b and w=w])
    show "Elem x (raw_D (Arr a b) w)" by (rule Arr.prems(2))
    show "Elem y (raw_D (Arr a b) w)" by (rule Arr.prems(3))
    fix z assume zm: "Elem z (raw_D a w)"
    have refl: "raw_rel w w" by (simp add: raw_rel_def)
    have lower: "u = v" if "Elem u (raw_D a w)" "Elem v (raw_D a w)"
      "src_enc a w u = src_enc a w v" for u v
      by (rule Arr.IH(1)[OF Arr.prems(1) that])
    have ix: "raw_T (Arr a b) w w x = x"
      using raw_T_id Arr.prems(1,2) by blast
    have iy: "raw_T (Arr a b) w w y = y"
      using raw_T_id Arr.prems(1,3) by blast
    have vx: "app (src_enc (Arr a b) w x) (Opair w (src_enc a w z)) =
      src_enc b w (raw_app a b w x z)"
      using src_enc_future_apply_given_injective[OF Arr.prems(1) refl zm lower, where b=b and F=x]
      by (simp only: ix)
    have vy: "app (src_enc (Arr a b) w y) (Opair w (src_enc a w z)) =
      src_enc b w (raw_app a b w y z)"
      using src_enc_future_apply_given_injective[OF Arr.prems(1) refl zm lower, where b=b and F=y]
      by (simp only: iy)
    have enc_eq: "src_enc b w (raw_app a b w x z) = src_enc b w (raw_app a b w y z)"
      using vx vy Arr.prems(4) by simp
    have ax: "Elem (raw_app a b w x z) (raw_D b w)"
      using raw_app_type Arr.prems(1,2) zm by blast
    have ay: "Elem (raw_app a b w y z) (raw_D b w)"
      using raw_app_type Arr.prems(1,3) zm by blast
    show "raw_app a b w x z = raw_app a b w y z"
      by (rule Arr.IH(2)[OF Arr.prems(1) ax ay enc_eq])
  qed
qed

theorem src_dec_enc:
  assumes "Elem w raw_W" "Elem x (raw_D a w)"
  shows "src_dec a w (src_enc a w x) = x"
  by (rule src_dec_enc_given_injective[OF assms(2)])
    (rule src_enc_injective[OF assms(1)], assumption+)

theorem src_enc_app:
  assumes "Elem v raw_W" "raw_rel w v" "Elem x (raw_D a v)"
  shows "app (src_enc (Arr a b) w F) (Opair v (src_enc a v x)) =
    src_enc b v (raw_app a b v (raw_T (Arr a b) w v F) x)"
  by (rule src_enc_future_apply_given_injective[OF assms])
    (rule src_enc_injective[OF assms(1)], assumption+)

theorem src_app_preserved:
  assumes ww: "Elem w raw_W" and fm: "Elem F (raw_D (Arr a b) w)"
    and xm: "Elem x (raw_D a w)"
  shows "app (src_enc (Arr a b) w F) (Opair w (src_enc a w x)) =
    src_enc b w (raw_app a b w F x)"
proof -
  have rr: "raw_rel w w" by (simp add: raw_rel_def)
  have id: "raw_T (Arr a b) w w F = F" using raw_T_id ww fm by blast
  show ?thesis using src_enc_app[OF ww rr xm, where b=b and F=F] by (simp only: id)
qed

lemma src_enc_graph_reconstruction:
  "src_enc (Arr a b) w F = Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w)
    (app (src_enc (Arr a b) w F))"
  by (simp only: src_enc_arrow book_ZF_graph_eta)

theorem src_enc_Lambda_characterization:
  assumes body: "\<And>v x. Elem v raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
    Elem x (raw_D a v) \<Longrightarrow>
    H (Opair v (src_enc a v x)) =
      src_enc b v (raw_app a b v (raw_T (Arr a b) w v F) x)"
  shows "src_enc (Arr a b) w F = Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) H"
proof -
  have point: "app (src_enc (Arr a b) w F) p = H p"
    if pm: "Elem p (book_ZF_pairs raw_W raw_rel (src_D a) w)" for p
  proof -
    have vw: "Elem (Fst p) raw_W" and wv: "raw_rel w (Fst p)"
      and ym: "Elem (Snd p) (src_D a (Fst p))"
      and pe: "Opair (Fst p) (Snd p) = p"
      using book_ZF_pairs_data[OF pm] by blast+
    obtain x where xm: "Elem x (raw_D a (Fst p))" and xe: "Snd p = src_enc a (Fst p) x"
      using ym by (auto simp only: src_D_member)
    have evaluated: "app (src_enc (Arr a b) w F) (Opair (Fst p) (src_enc a (Fst p) x)) =
      src_enc b (Fst p) (raw_app a b (Fst p) (raw_T (Arr a b) w (Fst p) F) x)"
      by (rule src_enc_app[OF vw wv xm])
    have rhs: "H (Opair (Fst p) (src_enc a (Fst p) x)) =
      src_enc b (Fst p) (raw_app a b (Fst p) (raw_T (Arr a b) w (Fst p) F) x)"
      by (rule body[OF vw wv xm])
    show ?thesis using evaluated rhs by (simp only: xe[symmetric] pe)
  qed
  have "src_enc (Arr a b) w F =
    Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) (app (src_enc (Arr a b) w F))"
    by (rule src_enc_graph_reconstruction)
  also have "... = Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) H"
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI, rule point, assumption)
  finally show ?thesis .
qed

lemma src_enc_app_dec:
  assumes vw: "Elem v raw_W" and wv: "raw_rel w v" and ym: "Elem y (src_D a v)"
  shows "app (src_enc (Arr a b) w F) (Opair v y) =
    src_enc b v (raw_app a b v (raw_T (Arr a b) w v F) (src_dec a v y))"
proof -
  have pair: "Elem (Opair v y) (book_ZF_pairs raw_W raw_rel (src_D a) w)"
    using vw wv ym by (simp only: book_ZF_pairs_member)
  show ?thesis by (simp only: src_enc_arrow Lambda_app[OF pair] Fst Snd)
qed

section \<open>Encoded counterparts form actual modalized domains\<close>

lemma src_T_enc:
  assumes "Elem w raw_W" "Elem x (raw_D a w)"
  shows "src_T a w v (src_enc a w x) = src_enc a v (raw_T a w v x)"
  by (simp only: src_T_def src_dec_enc[OF assms])

theorem src_T_type:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W"
    and wv: "raw_rel w v" and ym: "Elem y (src_D a w)"
  shows "Elem (src_T a w v y) (src_D a v)"
  unfolding src_T_def
  by (rule src_enc_type, rule raw_T_type[OF ww vw wv src_dec_type[OF ym]])

theorem src_T_id:
  assumes ww: "Elem w raw_W" and ym: "Elem y (src_D a w)"
  shows "src_T a w w y = y"
  by (simp only: src_T_def raw_T_id src_enc_dec[OF ym])

theorem src_T_compose:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and uw: "Elem u raw_W"
    and wv: "raw_rel w v" and vu: "raw_rel v u" and ym: "Elem y (src_D a w)"
  shows "src_T a w u y = src_T a v u (src_T a w v y)"
proof -
  have dm: "Elem (src_dec a w y) (raw_D a w)" by (rule src_dec_type[OF ym])
  have tm: "Elem (raw_T a w v (src_dec a w y)) (raw_D a v)"
    by (rule raw_T_type[OF ww vw wv dm])
  show ?thesis
    by (simp only: src_T_def src_dec_enc[OF vw tm]
      raw_T_compose[OF ww vw uw wv vu])
qed

theorem src_T_onto:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W"
    and wv: "raw_rel w v" and ym: "Elem y (src_D a v)"
  shows "\<exists>x. Elem x (src_D a w) \<and> src_T a w v x = y"
proof -
  obtain x where xm: "Elem x (raw_D a w)" and xy: "raw_T a w v x = src_dec a v y"
    using raw_T_onto[OF ww vw wv src_dec_type[OF ym]] by blast
  show ?thesis
    by (rule exI[of _ "src_enc a w x"])
      (simp only: src_enc_type[OF xm] src_T_enc[OF ww xm] xy src_enc_dec[OF ym] simp_thms)
qed

theorem src_domains:
  "book_modalized_set (explode raw_W) raw_rel (\<lambda>w. explode (src_D a w)) (src_T a)"
  by unfold_locales
    (auto simp only: explode_Elem intro: raw_rel_refl raw_rel_trans
      src_T_type src_T_id src_T_compose)

lemma src_D_nonempty: "explode (src_D a w) \<noteq> {}"
  using raw_D_nonempty[of a w] by (auto simp only: src_D_def explode_Repl_eq)

section \<open>Literal proposition restriction and future graph conditions\<close>

theorem src_propositions:
  assumes "Elem p (src_D Prop w)"
  shows "explode p \<subseteq> explode (book_ZF_future raw_W raw_rel w)"
  using assms
  by (auto simp only: src_D_member src_enc_truth explode_Elem book_ZF_future_member)

lemma src_propositions_member:
  assumes pm: "Elem p (src_D Prop w)" and xp: "Elem x p"
  shows "Elem x (book_ZF_future raw_W raw_rel w)"
  using src_propositions[OF pm] xp
  by (auto simp only: explode_Elem)

lemma src_enc_prop_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
  shows "src_enc Prop v (raw_T Prop w v p) = Sep (src_enc Prop w p) (raw_rel v)"
proof (rule iffD2[OF Ext], intro allI)
  fix u
  have comp: "raw_T Prop w u p = raw_T Prop v u (raw_T Prop w v p)"
    if "Elem u raw_W" "raw_rel v u"
    by (rule raw_T_compose[OF ww vw that(1) wv that(2)])
  show "Elem u (src_enc Prop v (raw_T Prop w v p)) =
    Elem u (Sep (src_enc Prop w p) (raw_rel v))"
    using comp raw_rel_trans[OF wv]
    by (auto simp only: src_enc_truth Sep)
qed

theorem src_proposition_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and pm: "Elem p (src_D Prop w)"
  shows "src_T Prop w v p = Sep p (raw_rel v)"
  by (simp only: src_T_def src_enc_prop_restriction[OF ww vw wv] src_enc_dec[OF pm])

theorem src_function_graph:
  assumes "Elem F (src_D (Arr a b) w)"
  shows "F = Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) (app F)"
  using assms src_enc_graph_reconstruction by (auto simp only: src_D_member)

theorem src_function_type:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and fm: "Elem F (src_D (Arr a b) w)" and xm: "Elem x (src_D a v)"
  shows "Elem (app F (Opair v x)) (src_D b v)"
proof -
  obtain f where fr: "Elem f (raw_D (Arr a b) w)" and fe: "F = src_enc (Arr a b) w f"
    using fm by (auto simp only: src_D_member)
  have tf: "Elem (raw_T (Arr a b) w v f) (raw_D (Arr a b) v)"
    by (rule raw_T_type[OF ww vw wv fr])
  have ax: "Elem (raw_app a b v (raw_T (Arr a b) w v f) (src_dec a v x)) (raw_D b v)"
    by (rule raw_app_type[OF tf src_dec_type[OF xm]])
  show ?thesis
    by (simp only: fe src_enc_app_dec[OF vw wv xm]) (rule src_enc_type[OF ax])
qed

theorem src_function_natural:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and uw: "Elem u raw_W"
    and wv: "raw_rel w v" and vu: "raw_rel v u"
    and fm: "Elem F (src_D (Arr a b) w)" and xm: "Elem x (src_D a v)"
  shows "src_T b v u (app F (Opair v x)) = app F (Opair u (src_T a v u x))"
proof -
  obtain f where fr: "Elem f (raw_D (Arr a b) w)" and fe: "F = src_enc (Arr a b) w f"
    using fm by (auto simp only: src_D_member)
  obtain z where zr: "Elem z (raw_D a v)" and ze: "x = src_enc a v z"
    using xm by (auto simp only: src_D_member)
  have wu: "raw_rel w u" by (rule raw_rel_trans[OF wv vu])
  have tf: "Elem (raw_T (Arr a b) w v f) (raw_D (Arr a b) v)"
    by (rule raw_T_type[OF ww vw wv fr])
  have tz: "Elem (raw_T a v u z) (raw_D a u)" by (rule raw_T_type[OF vw uw vu zr])
  have az: "Elem (raw_app a b v (raw_T (Arr a b) w v f) z) (raw_D b v)"
    by (rule raw_app_type[OF tf zr])
  have natural: "raw_T b v u (raw_app a b v (raw_T (Arr a b) w v f) z) =
    raw_app a b u (raw_T (Arr a b) w u f) (raw_T a v u z)"
    using raw_app_natural[OF vw uw vu tf zr]
    by (simp only: raw_T_compose[OF ww vw uw wv vu])
  show ?thesis
    by (simp only: fe ze src_enc_app[OF vw wv zr] src_T_enc[OF vw az]
      src_T_enc[OF vw zr] src_enc_app[OF uw wu tz] natural)
qed

lemma src_enc_arrow_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
  shows "src_enc (Arr a b) v (raw_T (Arr a b) w v f) =
    book_ZF_restrict raw_W raw_rel (src_D a) v (src_enc (Arr a b) w f)"
proof -
  have bodies: "src_enc b (Fst p)
    (raw_app a b (Fst p) (raw_T (Arr a b) v (Fst p) (raw_T (Arr a b) w v f))
      (src_dec a (Fst p) (Snd p))) = app (src_enc (Arr a b) w f) p"
    if pm: "Elem p (book_ZF_pairs raw_W raw_rel (src_D a) v)" for p
  proof -
    have uw: "Elem (Fst p) raw_W" and vu: "raw_rel v (Fst p)"
      and xm: "Elem (Snd p) (src_D a (Fst p))"
      and pe: "Opair (Fst p) (Snd p) = p"
      using book_ZF_pairs_data[OF pm] by blast+
    have wu: "raw_rel w (Fst p)" by (rule raw_rel_trans[OF wv vu])
    have comp: "raw_T (Arr a b) w (Fst p) f =
      raw_T (Arr a b) v (Fst p) (raw_T (Arr a b) w v f)"
      by (rule raw_T_compose[OF ww vw uw wv vu])
    show ?thesis using src_enc_app_dec[OF uw wu xm, where b=b and F=f]
      by (simp only: comp pe)
  qed
  show ?thesis
    unfolding book_ZF_restrict_def
    apply (subst src_enc_arrow)
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI, rule bodies, assumption)
qed

theorem src_function_restriction:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and fm: "Elem F (src_D (Arr a b) w)"
  shows "src_T (Arr a b) w v F = book_ZF_restrict raw_W raw_rel (src_D a) v F"
  by (simp only: src_T_def src_enc_arrow_restriction[OF ww vw wv] src_enc_dec[OF fm])

theorem src_modal_structure:
  "book_ZF_modal_structure raw_W raw_rel raw_root src_D src_T"
proof -
  interpret frame: book_ZF_frame raw_W raw_rel raw_root by (rule raw_frame)
  show ?thesis
    by unfold_locales
      (auto simp only: explode_Elem intro: src_T_type src_T_id src_T_compose src_propositions_member
        src_proposition_restriction src_function_graph src_function_type
        src_function_natural src_function_restriction)
qed

text \<open>This endpoint is the independently defined concrete modal
  structure predicate: actual future subsets, actual graphs on all future
  argument pairs, natural application, and literal restriction counterparts.
  It does not yet assert membership of the source logical operations or
  the subsequent interpretation and Classicism soundness predicates.\<close>

end
