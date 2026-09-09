theory Bacon_Book_Function_Representation_Inverse
  imports Bacon_Book_Function_Representation_Natural
begin

context book_function_representation
begin

theorem function_h_injective:
  assumes ww: "w \<in> W"
    and separates: "\<And>f g. f \<in> F w \<Longrightarrow> g \<in> F w \<Longrightarrow>
      (\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow>
        app v (iF w v f) a = app v (iF w v g) a) \<Longrightarrow> f = g"
  shows "inj_on (function_h w) (F w)"
proof (rule inj_onI)
  fix f g
  assume fm: "f \<in> F w" and gm: "g \<in> F w" and same: "function_h w f = function_h w g"
  show "f = g"
  proof (rule separates[OF fm gm])
    fix v a
    assume vw: "v \<in> W" and access: "le w v" and am: "a \<in> A v"
    have image_member: "hA v a \<in> DA v" by (rule Arg.h_type[OF vw am])
    have equal_values: "function_h w f (v,hA v a) = function_h w g (v,hA v a)"
      by (rule fun_cong[OF same])
    have represented: "hB v (app v (iF w v f) a) = hB v (app v (iF w v g) a)"
      using equal_values by (simp only: function_h_on[OF vw access image_member] Arg.jh[OF vw am])
    have fv: "iF w v f \<in> F v" by (rule Fun.counterpart_type[OF ww vw access fm])
    have gv: "iF w v g \<in> F v" by (rule Fun.counterpart_type[OF ww vw access gm])
    have left: "app v (iF w v f) a \<in> B v" by (rule app_type[OF vw fv am])
    have right: "app v (iF w v g) a \<in> B v" by (rule app_type[OF vw gv am])
    show "app v (iF w v f) a = app v (iF w v g) a"
      by (rule inj_onD[OF Res.h_injective[OF vw] represented left right])
  qed
qed

theorem function_h_bijection:
  assumes ww: "w \<in> W"
    and separates: "\<And>f g. f \<in> F w \<Longrightarrow> g \<in> F w \<Longrightarrow>
      (\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow>
        app v (iF w v f) a = app v (iF w v g) a) \<Longrightarrow> f = g"
  shows "bij_betw (function_h w) (F w) (function_domain w)"
  unfolding bij_betw_def function_domain_def by (rule conjI[OF function_h_injective[OF ww separates] refl])

lemma function_j_type:
  assumes member: "f \<in> function_domain w"
  shows "function_j w f \<in> F w"
proof -
  have image_member: "f \<in> function_h w ` F w" using member unfolding function_domain_def .
  show ?thesis unfolding function_j_def by (rule inv_into_into[OF image_member])
qed

theorem function_hj:
  assumes member: "f \<in> function_domain w"
  shows "function_h w (function_j w f) = f"
proof -
  have image_member: "f \<in> function_h w ` F w" using member unfolding function_domain_def .
  show ?thesis unfolding function_j_def by (rule f_inv_into_f[OF image_member])
qed

theorem function_jh:
  assumes ww: "w \<in> W" and fm: "f \<in> F w"
    and separates: "\<And>f g. f \<in> F w \<Longrightarrow> g \<in> F w \<Longrightarrow>
      (\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow>
        app v (iF w v f) a = app v (iF w v g) a) \<Longrightarrow> f = g"
  shows "function_j w (function_h w f) = f"
  unfolding function_j_def by (rule inv_into_f_f[OF function_h_injective[OF ww separates] fm])

end

text \<open>
  Quasi-functionality is used only for injectivity: equality of the two
  represented functions is tested at every pair (v,hA(v,a)), the output
  bijection reflects equality, and future applications separate the source
  values. The resulting h and j are proved inverse on the constructed
  domains. This is the generic one-function-type step; the hypotheses
  still need instantiation in the all-type canonical construction.
\<close>

end
