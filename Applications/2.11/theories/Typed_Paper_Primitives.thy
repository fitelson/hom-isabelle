theory Typed_Paper_Primitives
  imports Typed_Paper_Encoding Typed_Paper_Primitives_Raw
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Logical_Values"
begin

section \<open>The composite raw-to-paper encoding\<close>

definition pc_enc :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pc_enc a w x = paper_enc a w (src_enc a w x)"

lemma pc_enc_type:
  "Elem x (raw_D a w) \<Longrightarrow> Elem (pc_enc a w x) (paper_D a w)"
  unfolding pc_enc_def by (rule paper_enc_type, rule src_enc_type, assumption)

lemma pc_D_member:
  "Elem y (paper_D a w) \<longleftrightarrow> (\<exists>x. Elem x (raw_D a w) \<and> y=pc_enc a w x)"
  by (auto simp only: paper_D_member src_D_member pc_enc_def)

lemma pc_enc_injective:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)"
    and ym: "Elem y (raw_D a w)" and eq: "pc_enc a w x = pc_enc a w y"
  shows "x=y"
proof -
  have se: "src_enc a w x=src_enc a w y"
    by (rule paper_enc_injective[OF ww src_enc_type[OF xm] src_enc_type[OF ym]])
      (use eq in \<open>simp only: pc_enc_def\<close>)
  show ?thesis by (rule src_enc_injective[OF ww xm ym se])
qed

lemma pc_T_enc:
  assumes ww: "Elem w raw_W" and xm: "Elem x (raw_D a w)"
  shows "paper_T a (Opair w v) (pc_enc a w x) = pc_enc a v (raw_T a w v x)"
  by (simp only: pc_enc_def paper_T_enc[OF ww src_enc_type[OF xm]] src_T_enc[OF ww xm])

lemma pc_enc_app:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and xm: "Elem x (raw_D a v)"
  shows "app (pc_enc (Arr a b) w F) (Opair (Opair w v) (pc_enc a v x)) =
    pc_enc b v (raw_app a b v (raw_T (Arr a b) w v F) x)"
  by (simp only: pc_enc_def paper_enc_app[OF ww vw wv src_enc_type[OF xm]]
      src_enc_app[OF vw wv xm])

lemma pc_enc_Lambda_characterization:
  assumes ww: "Elem w raw_W"
    and body: "\<And>v x. Elem v raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
      Elem x (raw_D a v) \<Longrightarrow>
      H (Opair (Opair w v) (pc_enc a v x)) =
      pc_enc b v (raw_app a b v (raw_T (Arr a b) w v F) x)"
  shows "pc_enc (Arr a b) w F = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) w) H"
  unfolding pc_enc_def
proof (rule paper_enc_Lambda_characterization[OF ww])
  fix v y assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and ym: "Elem y (src_D a v)"
  obtain x where xm: "Elem x (raw_D a v)" and y: "y=src_enc a v x"
    using ym unfolding src_D_member by blast
  show "H (Opair (Opair w v) (paper_enc a v y)) =
    paper_enc b v (app (src_enc (Arr a b) w F) (Opair v y))"
    using body[OF vw wv xm]
    by (simp only: y pc_enc_def src_enc_app[OF vw wv xm])
qed

lemma pc_prop_member:
  "Elem h (pc_enc Prop w p) \<longleftrightarrow>
    (\<exists>v. h=Opair w v \<and> Elem v raw_W \<and> raw_rel w v \<and>
      raw_truth v (raw_T Prop w v p))"
  by (auto simp only: pc_enc_def paper_enc.simps Repl src_enc_truth)

lemma pc_prop_pair:
  "Elem (Opair w v) (pc_enc Prop w p) \<longleftrightarrow>
    Elem v raw_W \<and> raw_rel w v \<and> raw_truth v (raw_T Prop w v p)"
  by (simp only: pc_enc_def paper_enc_prop_pair src_enc_truth)

lemma pc_prop_truth:
  assumes ww: "Elem w raw_W"
  shows "Elem (pa_id w) (pc_enc Prop w p) \<longleftrightarrow> raw_truth w p"
  by (simp only: pa_id_def pc_prop_pair ww raw_rel_refl raw_T_id simp_thms)

lemma pc_outgoing_member:
  "Elem h (paper_ZF_outgoing_code pa_Ar Fst w) \<longleftrightarrow>
    (\<exists>v. h=Opair w v \<and> Elem w raw_W \<and> Elem v raw_W \<and> raw_rel w v)"
proof
  assume out: "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)"
  have both: "h \<in> explode pa_Ar \<and> Fst h=w"
    by (rule iffD1[OF paper_ZF_outgoing_code_member out])
  have ar0: "h \<in> explode pa_Ar" by (rule conjunct1[OF both])
  have ar: "Elem h pa_Ar" using ar0 by (simp only: explode_Elem)
  have src: "Fst h=w" by (rule conjunct2[OF both])
  have shape: "Opair (Fst h) (Snd h)=h" by (rule pa_arrow_data(4)[OF ar])
  have sw: "Elem (Fst h) raw_W" and tw: "Elem (Snd h) raw_W"
    and rel: "raw_rel (Fst h) (Snd h)" by (rule pa_arrow_data[OF ar])+
  show "\<exists>v. h=Opair w v \<and> Elem w raw_W \<and> Elem v raw_W \<and> raw_rel w v"
    by (rule exI[where x="Snd h"]) (use shape sw tw rel src in auto)
next
  assume "\<exists>v. h=Opair w v \<and> Elem w raw_W \<and> Elem v raw_W \<and> raw_rel w v"
  then obtain v where h: "h=Opair w v" and ww: "Elem w raw_W"
    and vw: "Elem v raw_W" and wv: "raw_rel w v" by blast
  show "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)"
    by (simp only: paper_ZF_outgoing_code_member explode_Elem h pa_arrow_pair
        Fst ww vw wv simp_thms)
qed

lemma pc_prop_asSep:
  assumes ww: "Elem w raw_W"
    and point: "\<And>v. Elem v raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
      raw_truth v (raw_T Prop w v p) = H (Opair w v)"
  shows "pc_enc Prop w p = Sep (paper_ZF_outgoing_code pa_Ar Fst w) H"
proof (rule iffD2[OF Ext], intro allI)
  fix h
  show "Elem h (pc_enc Prop w p) = Elem h (Sep (paper_ZF_outgoing_code pa_Ar Fst w) H)"
  proof (cases "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)")
    case True
    then obtain v where h: "h=Opair w v" and vw: "Elem v raw_W"
      and wv: "raw_rel w v" using pc_outgoing_member[of h w] by blast
    have out_pair: "Elem (Opair w v) (paper_ZF_outgoing_code pa_Ar Fst w)"
      using True by (simp only: h)
    show ?thesis
      by (simp only: Sep h out_pair pc_prop_pair vw wv point[OF vw wv] simp_thms)
  next
    case False
    have notin: "\<not> Elem h (pc_enc Prop w p)"
    proof
      assume "Elem h (pc_enc Prop w p)"
      then obtain v where h: "h=Opair w v" and vw: "Elem v raw_W"
        and wv: "raw_rel w v" using pc_prop_member[of h w p] by blast
      have out: "Elem h (paper_ZF_outgoing_code pa_Ar Fst w)"
        unfolding pc_outgoing_member
        by (rule exI[where x=v]) (simp only: h ww vw wv simp_thms)
      from False out show False by contradiction
    qed
    show ?thesis by (simp only: Sep False notin simp_thms)
  qed
qed

section \<open>Literal negation\<close>

lemma pc_not_value:
  assumes ww: "Elem w raw_W" and pm: "Elem p (raw_D Prop w)"
  shows "pc_enc Prop w (raw_app Prop Prop w (raw_not w) p) =
    Sep (paper_ZF_outgoing_code pa_Ar Fst w) (\<lambda>h. \<not> Elem h (pc_enc Prop w p))"
proof -
  have point: "raw_truth v (raw_T Prop w v (raw_app Prop Prop w (raw_not w) p)) =
    (\<not> raw_truth v (raw_T Prop w v p))"
    if vw: "Elem v raw_W" and wv: "raw_rel w v" for v
  proof -
    have pv: "Elem (raw_T Prop w v p) (raw_D Prop v)"
      by (rule raw_T_type[OF ww vw wv pm])
    have moved: "raw_T Prop w v (raw_app Prop Prop w (raw_not w) p) =
      raw_app Prop Prop v (raw_not v) (raw_T Prop w v p)"
      using raw_app_natural[where a=Prop and b=Prop and v=w and w=v
        and F="raw_not w" and x=p, OF ww vw wv raw_not_type pm]
        raw_not_natural[OF ww vw wv] by simp
    show ?thesis by (simp only: moved raw_not_truth[OF pv])
  qed
  show ?thesis
  proof (rule pc_prop_asSep[OF ww])
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    show "raw_truth v (raw_T Prop w v (raw_app Prop Prop w (raw_not w) p)) =
      (\<not> Elem (Opair w v) (pc_enc Prop w p))"
      by (simp only: point[OF vw wv] pc_prop_pair vw wv simp_thms)
  qed
qed

theorem pc_primitive_Not:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (Arr Prop Prop) w (raw_primitive SNot w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w SNot"
  unfolding raw_primitive.simps paper_ZF_logical_value.simps paper_ZF_pair_lambda_def
proof (rule pc_enc_Lambda_characterization[OF ww])
  fix v p assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and pm: "Elem p (raw_D Prop v)"
  show "Sep (paper_ZF_outgoing_code pa_Ar Fst (Snd (Fst (Opair (Opair w v) (pc_enc Prop v p)))))
      (\<lambda>j. \<not> Elem j (Snd (Opair (Opair w v) (pc_enc Prop v p)))) =
    pc_enc Prop v (raw_app Prop Prop v (raw_T (Arr Prop Prop) w v (raw_not w)) p)"
    using pc_not_value[OF vw pm]
    by (simp only: Fst Snd raw_not_natural[OF ww vw wv])
qed

section \<open>Quantification over the whole recoded carrier\<close>

lemma pc_predicate_test:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and xm: "Elem x (raw_D a v)"
  shows "Elem (pa_id v) (app (pc_enc (Arr a Prop) w P)
      (Opair (Opair w v) (pc_enc a v x))) =
    raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
  by (simp only: pc_enc_app[OF ww vw wv xm] pc_prop_truth[OF vw])

lemma pc_predicate_all:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
  shows "(\<forall>y\<in>explode (paper_D a v). Elem (pa_id v)
      (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))) =
    (\<forall>x. Elem x (raw_D a v) \<longrightarrow>
      raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x))"
proof
  assume all: "\<forall>y\<in>explode (paper_D a v). Elem (pa_id v)
    (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
  show "\<forall>x. Elem x (raw_D a v) \<longrightarrow>
    raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
  proof (intro allI impI)
    fix x assume xm: "Elem x (raw_D a v)"
    have enc: "pc_enc a v x \<in> explode (paper_D a v)"
      using pc_enc_type[OF xm] by (simp only: explode_Elem)
    have "Elem (pa_id v) (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) (pc_enc a v x)))"
      by (rule bspec[OF all enc])
    then show "raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
      by (simp only: pc_predicate_test[OF ww vw wv xm])
  qed
next
  assume all: "\<forall>x. Elem x (raw_D a v) \<longrightarrow>
    raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
  show "\<forall>y\<in>explode (paper_D a v). Elem (pa_id v)
    (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
  proof (intro ballI)
    fix y assume ym: "y \<in> explode (paper_D a v)"
    obtain x where xm: "Elem x (raw_D a v)" and y: "y=pc_enc a v x"
      using ym by (auto simp only: explode_Elem pc_D_member)
    have "raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
      by (rule mp[OF spec[OF all, of x] xm])
    then show "Elem (pa_id v) (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
      by (simp only: y pc_predicate_test[OF ww vw wv xm])
  qed
qed

lemma pc_predicate_ex:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
  shows "(\<exists>y\<in>explode (paper_D a v). Elem (pa_id v)
      (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))) =
    (\<exists>x. Elem x (raw_D a v) \<and>
      raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x))"
proof
  assume "\<exists>y\<in>explode (paper_D a v). Elem (pa_id v)
    (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
  then obtain y where ym: "y \<in> explode (paper_D a v)"
    and yt: "Elem (pa_id v) (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
    by blast
  obtain x where xm: "Elem x (raw_D a v)" and y: "y=pc_enc a v x"
    using ym by (auto simp only: explode_Elem pc_D_member)
  have xt: "raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
    using yt by (simp only: y pc_predicate_test[OF ww vw wv xm])
  show "\<exists>x. Elem x (raw_D a v) \<and> raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
    by (rule exI[where x=x], rule conjI[OF xm xt])
next
  assume "\<exists>x. Elem x (raw_D a v) \<and> raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)"
  then obtain x where xm: "Elem x (raw_D a v)"
    and xt: "raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x)" by blast
  have enc: "pc_enc a v x \<in> explode (paper_D a v)"
    using pc_enc_type[OF xm] by (simp only: explode_Elem)
  have truth: "Elem (pa_id v) (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) (pc_enc a v x)))"
    using xt by (simp only: pc_predicate_test[OF ww vw wv xm])
  show "\<exists>y\<in>explode (paper_D a v). Elem (pa_id v)
    (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y))"
    by (rule bexI[where x="pc_enc a v x"], rule truth, rule enc)
qed

lemma pc_all_value:
  assumes ww: "Elem w raw_W" and pm: "Elem P (raw_D (Arr a Prop) w)"
  shows "pc_enc Prop w (raw_app (Arr a Prop) Prop w (raw_all a w) P) =
    Sep (paper_ZF_outgoing_code pa_Ar Fst w)
      (\<lambda>j. \<forall>y\<in>explode (paper_D a (Snd j)).
        Elem (pa_id (Snd j)) (app (pc_enc (Arr a Prop) w P) (Opair j y)))"
proof -
  have point: "raw_truth v (raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_all a w) P)) =
    (\<forall>x. Elem x (raw_D a v) \<longrightarrow>
      raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x))"
    if vw: "Elem v raw_W" and wv: "raw_rel w v" for v
  proof -
    have pv: "Elem (raw_T (Arr a Prop) w v P) (raw_D (Arr a Prop) v)"
      by (rule raw_T_type[OF ww vw wv pm])
    have moved: "raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_all a w) P) =
      raw_app (Arr a Prop) Prop v (raw_all a v) (raw_T (Arr a Prop) w v P)"
      using raw_app_natural[where a="Arr a Prop" and b=Prop and v=w and w=v
        and F="raw_all a w" and x=P, OF ww vw wv raw_all_type pm]
        raw_all_natural[where a=a, OF ww vw wv] by simp
    show ?thesis by (simp only: moved raw_all_truth[OF pv])
  qed
  show ?thesis
  proof (rule pc_prop_asSep[OF ww])
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    show "raw_truth v (raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_all a w) P)) =
      (\<forall>y\<in>explode (paper_D a (Snd (Opair w v))). Elem (pa_id (Snd (Opair w v)))
        (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y)))"
      by (simp only: Snd point[OF vw wv] pc_predicate_all[OF ww vw wv])
  qed
qed

lemma pc_ex_value:
  assumes ww: "Elem w raw_W" and pm: "Elem P (raw_D (Arr a Prop) w)"
  shows "pc_enc Prop w (raw_app (Arr a Prop) Prop w (raw_ex a w) P) =
    Sep (paper_ZF_outgoing_code pa_Ar Fst w)
      (\<lambda>j. \<exists>y\<in>explode (paper_D a (Snd j)).
        Elem (pa_id (Snd j)) (app (pc_enc (Arr a Prop) w P) (Opair j y)))"
proof -
  have point: "raw_truth v (raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_ex a w) P)) =
    (\<exists>x. Elem x (raw_D a v) \<and>
      raw_truth v (raw_app a Prop v (raw_T (Arr a Prop) w v P) x))"
    if vw: "Elem v raw_W" and wv: "raw_rel w v" for v
  proof -
    have pv: "Elem (raw_T (Arr a Prop) w v P) (raw_D (Arr a Prop) v)"
      by (rule raw_T_type[OF ww vw wv pm])
    have moved: "raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_ex a w) P) =
      raw_app (Arr a Prop) Prop v (raw_ex a v) (raw_T (Arr a Prop) w v P)"
      using raw_app_natural[where a="Arr a Prop" and b=Prop and v=w and w=v
        and F="raw_ex a w" and x=P, OF ww vw wv raw_ex_type pm]
        raw_ex_natural[where a=a, OF ww vw wv] by simp
    show ?thesis by (simp only: moved raw_ex_truth[OF pv])
  qed
  show ?thesis
  proof (rule pc_prop_asSep[OF ww])
    fix v assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    show "raw_truth v (raw_T Prop w v (raw_app (Arr a Prop) Prop w (raw_ex a w) P)) =
      (\<exists>y\<in>explode (paper_D a (Snd (Opair w v))). Elem (pa_id (Snd (Opair w v)))
        (app (pc_enc (Arr a Prop) w P) (Opair (Opair w v) y)))"
      by (simp only: Snd point[OF vw wv] pc_predicate_ex[OF ww vw wv])
  qed
qed

theorem pc_primitive_All:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (Arr (Arr a Prop) Prop) w (raw_primitive (SAll a) w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w (SAll a)"
  unfolding raw_primitive.simps paper_ZF_logical_value.simps paper_ZF_pair_lambda_def
proof (rule pc_enc_Lambda_characterization[OF ww])
  fix v P assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and pm: "Elem P (raw_D (Arr a Prop) v)"
  show "Sep (paper_ZF_outgoing_code pa_Ar Fst
      (Snd (Fst (Opair (Opair w v) (pc_enc (Arr a Prop) v P)))))
      (\<lambda>j. \<forall>y\<in>explode (paper_D a (Snd j)). Elem (pa_id (Snd j))
        (app (Snd (Opair (Opair w v) (pc_enc (Arr a Prop) v P))) (Opair j y))) =
    pc_enc Prop v (raw_app (Arr a Prop) Prop v
      (raw_T (Arr (Arr a Prop) Prop) w v (raw_all a w)) P)"
    using pc_all_value[OF vw pm]
    by (simp only: Fst Snd raw_all_natural[OF ww vw wv])
qed

theorem pc_primitive_Ex:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (Arr (Arr a Prop) Prop) w (raw_primitive (SEx a) w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w (SEx a)"
  unfolding raw_primitive.simps paper_ZF_logical_value.simps paper_ZF_pair_lambda_def
proof (rule pc_enc_Lambda_characterization[OF ww])
  fix v P assume vw: "Elem v raw_W" and wv: "raw_rel w v"
    and pm: "Elem P (raw_D (Arr a Prop) v)"
  show "Sep (paper_ZF_outgoing_code pa_Ar Fst
      (Snd (Fst (Opair (Opair w v) (pc_enc (Arr a Prop) v P)))))
      (\<lambda>j. \<exists>y\<in>explode (paper_D a (Snd j)). Elem (pa_id (Snd j))
        (app (Snd (Opair (Opair w v) (pc_enc (Arr a Prop) v P))) (Opair j y))) =
    pc_enc Prop v (raw_app (Arr a Prop) Prop v
      (raw_T (Arr (Arr a Prop) Prop) w v (raw_ex a w)) P)"
    using pc_ex_value[OF vw pm]
    by (simp only: Fst Snd raw_ex_natural[OF ww vw wv])
qed

end
