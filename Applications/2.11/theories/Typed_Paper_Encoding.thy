theory Typed_Paper_Encoding
  imports Typed_Paper_Category
begin

primrec paper_enc :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_enc Ind = (\<lambda>w x. x)"
| "paper_enc Prop = (\<lambda>w p. Repl p (Opair w))"
| "paper_enc (Arr a b) = (\<lambda>w F.
    Lambda (paper_ZF_pair_code pa_Ar Fst Snd (\<lambda>v. Repl (src_D a v) (paper_enc a v)) w)
      (\<lambda>z. paper_enc b (Snd (Fst z))
        (app F (Opair (Snd (Fst z))
          (SOME x. Elem x (src_D a (Snd (Fst z))) \<and>
            paper_enc a (Snd (Fst z)) x = Snd z)))))"

definition paper_D :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_D a w = Repl (src_D a w) (paper_enc a w)"

definition paper_dec :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_dec a w y = (SOME x. Elem x (src_D a w) \<and> paper_enc a w x=y)"

definition paper_T :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_T a h y = paper_enc a (Snd h) (src_T a (Fst h) (Snd h) (paper_dec a (Fst h) y))"

lemma paper_D_function:
  "paper_D a = (\<lambda>w. Repl (src_D a w) (paper_enc a w))"
  by (rule ext) (rule paper_D_def)

lemma paper_D_member:
  "Elem y (paper_D a w) \<longleftrightarrow> (\<exists>x. Elem x (src_D a w) \<and> y=paper_enc a w x)"
  by (simp only: paper_D_def Repl)

lemma paper_enc_type:
  "Elem x (src_D a w) \<Longrightarrow> Elem (paper_enc a w x) (paper_D a w)"
  by (auto simp only: paper_D_member)

lemma paper_dec_spec:
  assumes "Elem y (paper_D a w)"
  shows "Elem (paper_dec a w y) (src_D a w) \<and> paper_enc a w (paper_dec a w y)=y"
proof -
  have "\<exists>x. Elem x (src_D a w) \<and> paper_enc a w x=y"
    using assms by (auto simp only: paper_D_member)
  then show ?thesis unfolding paper_dec_def by (rule someI_ex)
qed

lemma paper_dec_type:
  "Elem y (paper_D a w) \<Longrightarrow> Elem (paper_dec a w y) (src_D a w)"
  using paper_dec_spec by blast

lemma paper_enc_dec:
  "Elem y (paper_D a w) \<Longrightarrow> paper_enc a w (paper_dec a w y)=y"
  using paper_dec_spec by blast

lemma paper_dec_enc_given:
  assumes xm: "Elem x (src_D a w)"
    and inj: "\<And>y z. Elem y (src_D a w) \<Longrightarrow> Elem z (src_D a w) \<Longrightarrow>
      paper_enc a w y=paper_enc a w z \<Longrightarrow> y=z"
  shows "paper_dec a w (paper_enc a w x)=x"
  by (rule inj[OF paper_dec_type[OF paper_enc_type[OF xm]] xm
      paper_enc_dec[OF paper_enc_type[OF xm]]])

lemma paper_enc_arrow:
  "paper_enc (Arr a b) w F = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)
    (\<lambda>z. paper_enc b (Snd (Fst z))
      (app F (Opair (Snd (Fst z)) (paper_dec a (Snd (Fst z)) (Snd z)))))"
  by (simp only: paper_enc.simps paper_D_function paper_dec_def)

lemma paper_enc_prop_pair:
  "Elem (Opair w v) (paper_enc Prop w p) \<longleftrightarrow> Elem v p"
  by (simp add: paper_enc.simps Repl Opair)

lemma paper_enc_truth:
  "Elem (pa_id w) (paper_enc Prop w p) \<longleftrightarrow> Elem w p"
  by (simp only: pa_id_def paper_enc_prop_pair)

lemma paper_enc_app_given:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and xm: "Elem x (src_D a v)"
    and inj: "\<And>y z. Elem y (src_D a v) \<Longrightarrow> Elem z (src_D a v) \<Longrightarrow>
      paper_enc a v y=paper_enc a v z \<Longrightarrow> y=z"
  shows "app (paper_enc (Arr a b) w F) (Opair (Opair w v) (paper_enc a v x)) =
    paper_enc b v (app F (Opair v x))"
proof -
  have pair: "Elem (Opair (Opair w v) (paper_enc a v x))
    (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)"
    using ww vw wv paper_enc_type[OF xm] by (simp only: pa_pair_member)
  show ?thesis
    by (simp only: paper_enc_arrow Lambda_app[OF pair] Fst Snd paper_dec_enc_given[OF xm inj])
qed

theorem paper_enc_injective:
  assumes ww: "Elem w raw_W" and xm: "Elem x (src_D a w)" and ym: "Elem y (src_D a w)"
    and eq: "paper_enc a w x=paper_enc a w y"
  shows "x=y"
  using ww xm ym eq
proof (induction a arbitrary: w x y)
  case Ind
  then show ?case by (simp only: paper_enc.simps)
next
  case Prop
  show ?case
  proof (rule iffD2[OF Ext], intro allI)
    fix v
    have "Elem (Opair w v) (paper_enc Prop w x)=Elem (Opair w v) (paper_enc Prop w y)"
      by (simp only: Prop.prems(4))
    then show "Elem v x=Elem v y" by (simp only: paper_enc_prop_pair)
  qed
next
  case (Arr a b)
  have point: "app x z=app y z" if zm: "Elem z (book_ZF_pairs raw_W raw_rel (src_D a) w)" for z
  proof -
    have vw: "Elem (Fst z) raw_W" and wv: "raw_rel w (Fst z)"
      and am: "Elem (Snd z) (src_D a (Fst z))" and shape: "Opair (Fst z) (Snd z)=z"
      using book_ZF_pairs_data[OF zm] by blast+
    have inj: "u=v" if "Elem u (src_D a (Fst z))" "Elem v (src_D a (Fst z))"
      "paper_enc a (Fst z) u=paper_enc a (Fst z) v" for u v
      by (rule Arr.IH(1)[OF vw that])
    have ax: "Elem (app x z) (src_D b (Fst z))"
      using src_function_type[OF Arr.prems(1) vw wv Arr.prems(2) am]
      by (simp only: shape)
    have ay: "Elem (app y z) (src_D b (Fst z))"
      using src_function_type[OF Arr.prems(1) vw wv Arr.prems(3) am]
      by (simp only: shape)
    have vx: "app (paper_enc (Arr a b) w x)
      (Opair (Opair w (Fst z)) (paper_enc a (Fst z) (Snd z))) = paper_enc b (Fst z) (app x z)"
      using paper_enc_app_given[OF Arr.prems(1) vw wv am inj, where b=b and F=x]
      by (simp only: shape)
    have vy: "app (paper_enc (Arr a b) w y)
      (Opair (Opair w (Fst z)) (paper_enc a (Fst z) (Snd z))) = paper_enc b (Fst z) (app y z)"
      using paper_enc_app_given[OF Arr.prems(1) vw wv am inj, where b=b and F=y]
      by (simp only: shape)
    have equal: "paper_enc b (Fst z) (app x z)=paper_enc b (Fst z) (app y z)"
      using vx vy Arr.prems(4) by simp
    show ?thesis by (rule Arr.IH(2)[OF vw ax ay equal])
  qed
  have "x=Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) (app x)"
    by (rule src_function_graph[OF Arr.prems(2)])
  also have "...=Lambda (book_ZF_pairs raw_W raw_rel (src_D a) w) (app y)"
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI, rule point, assumption)
  also have "...=y" by (rule sym[OF src_function_graph[OF Arr.prems(3)]])
  finally show ?case .
qed

theorem paper_dec_enc:
  assumes "Elem w raw_W" "Elem x (src_D a w)"
  shows "paper_dec a w (paper_enc a w x)=x"
  by (rule paper_dec_enc_given[OF assms(2)])
    (rule paper_enc_injective[OF assms(1)], assumption+)

theorem paper_enc_app:
  assumes "Elem w raw_W" "Elem v raw_W" "raw_rel w v" "Elem x (src_D a v)"
  shows "app (paper_enc (Arr a b) w F) (Opair (Opair w v) (paper_enc a v x)) =
    paper_enc b v (app F (Opair v x))"
  by (rule paper_enc_app_given[OF assms])
    (rule paper_enc_injective[OF assms(2)], assumption+)

lemma paper_enc_app_dec:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and xm: "Elem x (paper_D a v)"
  shows "app (paper_enc (Arr a b) w F) (Opair (Opair w v) x) =
    paper_enc b v (app F (Opair v (paper_dec a v x)))"
  using paper_enc_app[OF ww vw wv paper_dec_type[OF xm], where b=b and F=F]
  by (simp only: paper_enc_dec[OF xm])

lemma paper_enc_graph:
  "paper_enc (Arr a b) w F = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)
    (app (paper_enc (Arr a b) w F))"
  by (simp only: paper_enc_arrow book_ZF_graph_eta)

theorem paper_enc_Lambda_characterization:
  assumes ww: "Elem w raw_W"
    and body: "\<And>v x. Elem v raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
      Elem x (src_D a v) \<Longrightarrow>
      H (Opair (Opair w v) (paper_enc a v x)) = paper_enc b v (app F (Opair v x))"
  shows "paper_enc (Arr a b) w F = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w) H"
proof -
  have point: "app (paper_enc (Arr a b) w F) z=H z"
    if zm: "Elem z (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)" for z
  proof -
    obtain v y where vw: "Elem v raw_W" and wv: "raw_rel w v"
      and ym: "Elem y (paper_D a v)" and z: "z=Opair (Opair w v) y"
      using pa_pairE[OF zm] by blast
    obtain x where xm: "Elem x (src_D a v)" and y: "y=paper_enc a v x"
      using ym by (auto simp only: paper_D_member)
    show ?thesis
      by (simp only: z y paper_enc_app[OF ww vw wv xm] body[OF vw wv xm])
  qed
  have "paper_enc (Arr a b) w F = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w)
      (app (paper_enc (Arr a b) w F))" by (rule paper_enc_graph)
  also have "...=Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w) H"
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI, rule point, assumption)
  finally show ?thesis .
qed

lemma paper_T_enc:
  assumes ww: "Elem w raw_W" and xm: "Elem x (src_D a w)"
  shows "paper_T a (Opair w v) (paper_enc a w x)=paper_enc a v (src_T a w v x)"
  by (simp only: paper_T_def Fst Snd paper_dec_enc[OF ww xm])

lemma paper_D_nonempty: "explode (paper_D a w) \<noteq> {}"
  using src_D_nonempty[of a w] by (auto simp only: paper_D_def explode_Repl_eq)

theorem paper_T_type:
  assumes ha: "Elem h pa_Ar" and ym: "Elem y (paper_D a (Fst h))"
  shows "Elem (paper_T a h y) (paper_D a (Snd h))"
  unfolding paper_T_def
  by (rule paper_enc_type, rule src_T_type[OF pa_arrow_data(1,2,3)[OF ha] paper_dec_type[OF ym]])

theorem paper_T_id:
  assumes ww: "Elem w raw_W" and ym: "Elem y (paper_D a w)"
  shows "paper_T a (pa_id w) y=y"
  by (simp only: paper_T_def pa_id_def Fst Snd src_T_id[OF ww paper_dec_type[OF ym]]
    paper_enc_dec[OF ym])

theorem paper_T_compose:
  assumes fa: "Elem f pa_Ar" and ga: "Elem g pa_Ar" and meet: "Snd f=Fst g"
    and ym: "Elem y (paper_D a (Fst f))"
  shows "paper_T a (pa_compose g f) y=paper_T a g (paper_T a f y)"
proof -
  have dm: "Elem (paper_dec a (Fst f) y) (src_D a (Fst f))"
    by (rule paper_dec_type[OF ym])
  have tm: "Elem (src_T a (Fst f) (Snd f) (paper_dec a (Fst f) y)) (src_D a (Snd f))"
    by (rule src_T_type[OF pa_arrow_data(1,2,3)[OF fa] dm])
  have comp: "src_T a (Fst f) (Snd g) (paper_dec a (Fst f) y) =
    src_T a (Snd f) (Snd g) (src_T a (Fst f) (Snd f) (paper_dec a (Fst f) y))"
    by (rule src_T_compose[OF pa_arrow_data(1,2)[OF fa] pa_arrow_data(2)[OF ga]
      pa_arrow_data(3)[OF fa] _ dm]) (use pa_arrow_data(3)[OF ga] in \<open>simp only: meet\<close>)
  show ?thesis
    by (simp only: paper_T_def pa_compose_def Fst Snd meet[symmetric]
      paper_dec_enc[OF pa_arrow_data(2)[OF fa] tm] comp)
qed

theorem paper_actions:
  "paper_action (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (paper_D a w)) (paper_T a)"
proof -
  interpret C: paper_category "explode raw_W" "explode pa_Ar" Fst Snd pa_compose pa_id
    by (rule pa_category)
  show ?thesis by unfold_locales
    (auto simp only: explode_Elem intro: paper_T_type paper_T_id paper_T_compose)
qed

end
