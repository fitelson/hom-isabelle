theory Bacon_Source_Relational_Naming_Coordinate_Assignments
  imports Bacon_Source_Relational_Naming_Assignments
begin

section \<open>Assignment comparison after moving one marker\<close>

lemma paper_R_naming_coordinate_coverage:
  assumes adequate: "named_adequate g A"
    and agree: "\<And>j. j \<in> paper_R_naming_support A \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
  shows "named_fv (paper_R_naming_replace x A) - {x k} \<subseteq>
    dom (paper_R_naming_override (paper_R_naming_support A) y g)"
proof
  fix n
  assume member: "n \<in> named_fv (paper_R_naming_replace x A) - {x k}"
  have different: "n \<noteq> x k" using member by simp
  have alternatives: "n \<in> named_fv A \<or> n \<in> x ` paper_R_naming_support A"
    using paper_R_naming_replace_fv_bound[where x=x and A=A] member by blast
  then show "n \<in> dom (paper_R_naming_override (paper_R_naming_support A) y g)"
  proof
    assume free: "n \<in> named_fv A"
    have "n \<in> dom g" using adequate free unfolding named_adequate_def by blast
    then show ?thesis by (simp only: paper_R_naming_override_domain; blast)
  next
    assume image: "n \<in> x ` paper_R_naming_support A"
    obtain j where key: "j \<in> paper_R_naming_support A" and shape: "n = x j" using image by blast
    have distinct: "j \<noteq> k" using different shape by blast
    have same: "y j = x j" by (rule agree[OF key distinct])
    have representation: "n = y j" by (simp only: same; rule shape)
    have "n \<in> y ` paper_R_naming_support A"
      by (rule image_eqI[where f=y and x=j, OF representation key])
    then show ?thesis by (simp only: paper_R_naming_override_domain; blast)
  qed
qed

lemma paper_R_naming_coordinate_assignment_agrees:
  assumes first: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
    and key: "k \<in> paper_R_naming_support A"
    and agree: "\<And>j. j \<in> paper_R_naming_support A \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
    and free: "n \<in> named_fv (paper_R_naming_replace x A)"
  shows "((paper_R_naming_override (paper_R_naming_support A) y g)(x k := Some (snd k))) n =
    paper_R_naming_override (paper_R_naming_support A) x g n"
proof -
  let ?K = "paper_R_naming_support A"
  let ?gx = "paper_R_naming_override ?K x g"
  let ?gy = "paper_R_naming_override ?K y g"
  have xi: "inj_on x ?K" by (rule paper_R_naming_chart_injective[OF first])
  have yi: "inj_on y ?K" by (rule paper_R_naming_chart_injective[OF second])
  have alternatives: "n \<in> named_fv A \<or> n \<in> x ` ?K"
    using paper_R_naming_replace_fv_bound[where x=x and A=A] free by blast
  show ?thesis
  proof (cases "n \<in> named_fv A")
    case True
    have gx: "?gx n = g n" by (rule paper_R_naming_override_agrees[OF first subset_refl True])
    have gy: "?gy n = g n" by (rule paper_R_naming_override_agrees[OF second subset_refl True])
    have fresh: "x k \<notin> named_vars A" by (rule paper_R_naming_chart_fresh[OF first key])
    have different: "n \<noteq> x k" using True fresh named_fv_subset_vars by blast
    show ?thesis by (simp add: different gx gy)
  next
    case False
    obtain j where member: "j \<in> ?K" and shape: "n = x j" using alternatives False by blast
    have gx: "?gx (x j) = Some (snd j)" by (rule paper_R_naming_override_lookup[OF xi member])
    show ?thesis
    proof (cases "j = k")
      case True
      show ?thesis using shape True gx by auto
    next
      case False
      have same: "y j = x j" by (rule agree[OF member False])
      have different: "x j \<noteq> x k" using xi member key False unfolding inj_on_def by blast
      have gy: "?gy (x j) = Some (snd j)"
        using paper_R_naming_override_lookup[OF yi member] by (simp only: same)
      show ?thesis by (simp add: shape different gx gy)
    qed
  qed
qed

end
