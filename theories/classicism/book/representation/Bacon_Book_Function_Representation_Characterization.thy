theory Bacon_Book_Function_Representation_Characterization
  imports Bacon_Book_Function_Representation_Transport
begin

context book_function_representation
begin

lemma function_h_source_argument:
  assumes vw: "v \<in> W" and access: "le w v" and am: "a \<in> A v"
  shows "function_h w f (v,hA v a) = hB v (app v (iF w v f) a)"
  by (simp only: function_h_on[OF vw access Arg.h_type[OF vw am]] Arg.jh[OF vw am])

theorem function_represents_iff:
  assumes ww: "w \<in> W" and fm: "f \<in> F w"
    and gm: "g \<in> book_modalized_exponential W le DA dA DB dB w"
  shows "g = function_h w f \<longleftrightarrow>
    (\<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a)))"
proof
  assume same: "g = function_h w f"
  show "\<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
    by (intro ballI impI; simp only: same; rule function_h_source_argument; assumption)
next
  assume behavior: "\<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
  show "g = function_h w f"
  proof (rule ext)
    fix p
    show "g p = function_h w f p"
    proof (cases "p \<in> book_modalized_exponential_pairs W le DA w")
      case True
      obtain v a where shape: "p = (v,a)" by (cases p) auto
      have vw: "v \<in> W" and access: "le w v" and am: "a \<in> DA v"
        using True by (simp_all add: shape book_modalized_exponential_pairs_iff)
      have inverse: "Arg.j v a \<in> A v" by (rule Arg.j_type[OF vw am])
      have given: "g (v,hA v (Arg.j v a)) = hB v (app v (iF w v f) (Arg.j v a))"
        using behavior vw access inverse by blast
      show ?thesis using given by (simp only: shape Arg.hj[OF vw am] function_h_on[OF vw access am])
    next
      case False
      have normal: "g p = undefined" by (rule book_modalized_exponential_normal[OF gm False])
      show ?thesis by (simp only: normal function_h_normal[OF False])
    qed
  qed
qed

theorem function_domain_characterization:
  assumes ww: "w \<in> W" and gm: "g \<in> book_modalized_exponential W le DA dA DB dB w"
  shows "g \<in> function_domain w \<longleftrightarrow>
    (\<exists>f\<in>F w. \<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a)))"
proof
  assume member: "g \<in> function_domain w"
  obtain f where fm: "f \<in> F w" and shape: "g = function_h w f" using member unfolding function_domain_def by blast
  have behavior: "\<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
    using shape by (simp only: function_represents_iff[OF ww fm gm])
  show "\<exists>f\<in>F w. \<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
    by (rule bexI[where x=f], rule behavior, rule fm)
next
  assume given: "\<exists>f\<in>F w. \<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
  obtain f where fm: "f \<in> F w" and behavior: "\<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A v. g (v,hA v a) = hB v (app v (iF w v f) a))"
    using given by blast
  have same: "g = function_h w f" using behavior by (simp only: function_represents_iff[OF ww fm gm])
  show "g \<in> function_domain w" by (simp only: same; unfold function_domain_def; rule imageI[OF fm])
qed

end

text \<open>
  The image-domain definition agrees with the source defining-behavior
  condition: a future homomorphism is represented exactly when some
  source value has all the displayed applications. Surjectivity of the
  lower argument map covers every valid input; off-domain normalization
  covers the rest. Source quasi-functionality then gives uniqueness, as
  separately proved by function_h_injective. Thus the domain is not
  merely an arbitrary subset chosen without the p.400 characterization.
\<close>

end
