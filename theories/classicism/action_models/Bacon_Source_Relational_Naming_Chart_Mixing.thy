theory Bacon_Source_Relational_Naming_Chart_Mixing
  imports Bacon_Source_Relational_Naming_Assignments
begin

section \<open>Finite interpolation between disjoint chart images\<close>

definition paper_R_naming_mix ::
  "(otype \<times> 'v) set \<Rightarrow> ((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow>
    ((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow> (otype \<times> 'v) \<Rightarrow> nat" where
  "paper_R_naming_mix L x y k = (if k \<in> L then y k else x k)"

lemma paper_R_naming_mix_empty [simp]:
  "paper_R_naming_mix {} x y = x"
  by (rule ext) (simp add: paper_R_naming_mix_def)

lemma paper_R_naming_mix_chart:
  assumes first: "paper_R_naming_chart G K N x" and second: "paper_R_naming_chart G K N y"
    and disjoint: "x ` K \<inter> y ` K = {}"
  shows "paper_R_naming_chart G K N (paper_R_naming_mix L x y)"
proof -
  have xi: "inj_on x K" and yi: "inj_on y K"
    using first second unfolding paper_R_naming_chart_def by blast+
  have cross: "x a \<noteq> y b" if ak: "a \<in> K" and bk: "b \<in> K" for a b
  proof
    assume same: "x a = y b"
    have xa: "x a \<in> x ` K" by (rule imageI[OF ak])
    have yb: "y b \<in> y ` K" by (rule imageI[OF bk])
    have "x a \<in> x ` K \<inter> y ` K" using xa yb same by auto
    then show False using disjoint by simp
  qed
  have injective: "inj_on (paper_R_naming_mix L x y) K"
  proof (rule inj_onI)
    fix a b
    assume ak: "a \<in> K" and bk: "b \<in> K"
      and equal: "paper_R_naming_mix L x y a = paper_R_naming_mix L x y b"
    have xx: "x a = x b \<Longrightarrow> a = b" by (rule inj_onD[OF xi _ ak bk])
    have yy: "y a = y b \<Longrightarrow> a = b" by (rule inj_onD[OF yi _ ak bk])
    have xy: "x a \<noteq> y b" by (rule cross[OF ak bk])
    have yx: "y a \<noteq> x b" using cross[OF bk ak] by auto
    show "a = b" using equal xx yy xy yx
      by (cases "a \<in> L"; cases "b \<in> L"; auto simp: paper_R_naming_mix_def)
  qed
  have types: "\<forall>k\<in>K. G (paper_R_naming_mix L x y k) = fst k"
    using first second unfolding paper_R_naming_chart_def paper_R_naming_mix_def by auto
  have fresh: "paper_R_naming_mix L x y ` K \<inter> N = {}"
    using first second unfolding paper_R_naming_chart_def paper_R_naming_mix_def by auto
  show ?thesis unfolding paper_R_naming_chart_def
    by (rule conjI[OF injective], rule conjI[OF types fresh])
qed

lemma paper_R_naming_override_chart_agreement:
  assumes first: "inj_on x K" and second: "inj_on y K"
    and agree: "\<And>k. k \<in> K \<Longrightarrow> x k = y k"
  shows "paper_R_naming_override K x g = paper_R_naming_override K y g"
proof (rule ext)
  fix n
  have images: "x ` K = y ` K" by (rule image_cong[OF refl]; rule agree; assumption)
  show "paper_R_naming_override K x g n = paper_R_naming_override K y g n"
  proof (cases "n \<in> x ` K")
    case True
    obtain k where member: "k \<in> K" and shape: "n = x k" using True by blast
    have same: "x k = y k" by (rule agree[OF member])
    have left: "paper_R_naming_override K x g n = Some (snd k)"
      by (simp only: shape; rule paper_R_naming_override_lookup[OF first member])
    have right: "paper_R_naming_override K y g n = Some (snd k)"
      by (simp only: shape same; rule paper_R_naming_override_lookup[OF second member])
    show ?thesis by (simp only: left right)
  next
    case False
    have outside: "n \<notin> y ` K" by (simp only: images[symmetric]; rule False)
    show ?thesis by (simp only: paper_R_naming_override_outside[OF False]
      paper_R_naming_override_outside[OF outside])
  qed
qed

end
