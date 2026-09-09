theory Bacon_Book_Function_Representation_Natural
  imports Bacon_Book_Function_Representation
begin

context book_function_representation
begin

theorem function_h_natural:
  assumes ww: "w \<in> W" and fm: "f \<in> F w"
    and vw: "v \<in> W" and wv: "le w v" and uw: "u \<in> W" and vu: "le v u" and am: "a \<in> DA v"
  shows "dB v u (function_h w f (v,a)) = function_h w f (u,dA v u a)"
proof -
  have fv: "iF w v f \<in> F v" by (rule Fun.counterpart_type[OF ww vw wv fm])
  have inverse: "Arg.j v a \<in> A v" by (rule Arg.j_type[OF vw am])
  have applied: "app v (iF w v f) (Arg.j v a) \<in> B v" by (rule app_type[OF vw fv inverse])
  have moved_a: "dA v u a \<in> DA u" by (rule Arg.Target.counterpart_type[OF vw uw vu am])
  have order: "book_preorder W le" using Fun.book_modalized_set_axioms unfolding book_modalized_set_def by blast
  have wu: "le w u" by (rule book_preorder.transitive[OF order ww vw uw wv vu])
  have representation: "dB v u (hB v (app v (iF w v f) (Arg.j v a))) =
    hB u (iB v u (app v (iF w v f) (Arg.j v a)))"
    by (rule book_modalized_map_natural[OF Res.h_map vw uw vu applied, symmetric])
  have application: "iB v u (app v (iF w v f) (Arg.j v a)) =
    app u (iF v u (iF w v f)) (iA v u (Arg.j v a))"
    by (rule app_natural[OF vw uw vu fv inverse])
  have function_move: "iF v u (iF w v f) = iF w u f"
    by (rule Fun.counterpart_compose[OF ww vw uw wv vu fm, symmetric])
  have argument_move: "iA v u (Arg.j v a) = Arg.j u (dA v u a)"
    by (rule Arg.j_natural[OF vw uw vu am, symmetric])
  show ?thesis by (simp only: function_h_on[OF vw wv am] function_h_on[OF uw wu moved_a]
    representation application function_move argument_move)
qed

theorem function_h_homomorphism:
  assumes ww: "w \<in> W" and fm: "f \<in> F w"
  shows "function_h w f \<in> book_modalized_exponential W le DA dA DB dB w"
  by (rule book_modalized_exponentialI;
    (rule function_h_normal | rule function_h_type[OF ww fm] | rule function_h_natural[OF ww fm]); assumption)

theorem function_domain_homomorphisms:
  assumes ww: "w \<in> W"
  shows "function_domain w \<subseteq> book_modalized_exponential W le DA dA DB dB w"
  using function_h_homomorphism[OF ww] unfolding function_domain_def by blast

end

text \<open>
  The represented function is an actual future homomorphism. Its
  counterpart equation follows from the source application's naturality,
  the source function counterpart composition law, the lower inverse's
  naturality, and the lower output map's naturality. No injectivity or
  quasi-functionality of the source F domain is used for this membership
  result. Those conditions enter only when recovering a unique source.
\<close>

end
