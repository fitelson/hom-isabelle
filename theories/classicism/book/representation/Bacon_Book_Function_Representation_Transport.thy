theory Bacon_Book_Function_Representation_Transport
  imports Bacon_Book_Function_Representation_Inverse
    Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Exponential_Transport
begin

context book_function_representation
begin

lemma function_order: "book_preorder W le"
  using Fun.book_modalized_set_axioms unfolding book_modalized_set_def by blast

theorem function_h_counterpart:
  assumes ww: "w \<in> W" and vw: "v \<in> W" and access: "le w v" and fm: "f \<in> F w"
  shows "function_h v (iF w v f) = book_modalized_exponential_transport W le DA v (function_h w f)"
proof (rule ext)
  fix p
  show "function_h v (iF w v f) p = book_modalized_exponential_transport W le DA v (function_h w f) p"
  proof (cases "p \<in> book_modalized_exponential_pairs W le DA v")
    case True
    obtain u a where shape: "p = (u,a)" by (cases p) auto
    have uw: "u \<in> W" and vu: "le v u" and am: "a \<in> DA u"
      using True by (simp_all add: shape book_modalized_exponential_pairs_iff)
    have wu: "le w u" by (rule book_preorder.transitive[OF function_order ww vw uw access vu])
    have equation: "iF v u (iF w v f) = iF w u f" by (rule Fun.counterpart_compose[OF ww vw uw access vu fm, symmetric])
    have pair: "(u,a) \<in> book_modalized_exponential_pairs W le DA v" using True by (simp only: shape)
    have restriction: "book_modalized_exponential_transport W le DA v (function_h w f) (u,a) = function_h w f (u,a)"
      by (rule book_modalized_exponential_transport_on[OF pair])
    show ?thesis by (simp only: shape restriction function_h_on[OF uw vu am] function_h_on[OF uw wu am] equation)
  next
    case False
    show ?thesis by (simp only: function_h_normal[OF False] book_modalized_exponential_transport_def False if_False)
  qed
qed

theorem function_domain_counterpart:
  assumes ww: "w \<in> W" and vw: "v \<in> W" and access: "le w v" and member: "g \<in> function_domain w"
  shows "book_modalized_exponential_transport W le DA v g \<in> function_domain v"
proof -
  obtain f where fm: "f \<in> F w" and shape: "g = function_h w f" using member unfolding function_domain_def by blast
  have moved: "iF w v f \<in> F v" by (rule Fun.counterpart_type[OF ww vw access fm])
  have image: "function_h v (iF w v f) \<in> function_domain v" unfolding function_domain_def by (rule imageI[OF moved])
  show ?thesis by (simp only: shape function_h_counterpart[OF ww vw access fm, symmetric]; rule image)
qed

theorem function_domain_modalized:
  "book_modalized_set W le function_domain (\<lambda>w v g. book_modalized_exponential_transport W le DA v g)"
proof unfold_locales
  show "\<And>w v g. w \<in> W \<Longrightarrow> v \<in> W \<Longrightarrow> le w v \<Longrightarrow> g \<in> function_domain w \<Longrightarrow>
    book_modalized_exponential_transport W le DA v g \<in> function_domain v" by (rule function_domain_counterpart; assumption)
  show "\<And>w g. w \<in> W \<Longrightarrow> g \<in> function_domain w \<Longrightarrow> book_modalized_exponential_transport W le DA w g = g"
    by (rule book_modalized_exponential_transport_identity; rule subsetD[OF function_domain_homomorphisms]; assumption)
  fix w v u g
  assume ww: "w \<in> W" and vw: "v \<in> W" and uw: "u \<in> W" and wv: "le w v" and vu: "le v u" and member: "g \<in> function_domain w"
  show "book_modalized_exponential_transport W le DA u g =
    book_modalized_exponential_transport W le DA u (book_modalized_exponential_transport W le DA v g)"
    by (rule book_preorder.book_modalized_exponential_transport_compose[OF function_order vw uw vu, symmetric])
qed

theorem function_h_modalized_map:
  "book_modalized_map W le F iF function_domain (\<lambda>w v g. book_modalized_exponential_transport W le DA v g) function_h"
proof (rule book_modalized_mapI)
  fix w f
  assume "w \<in> W" and fm: "f \<in> F w"
  show "function_h w f \<in> function_domain w" unfolding function_domain_def by (rule imageI[OF fm])
next
  fix w v f
  assume ww: "w \<in> W" and vw: "v \<in> W" and access: "le w v" and fm: "f \<in> F w"
  show "function_h v (iF w v f) = book_modalized_exponential_transport W le DA v (function_h w f)"
    by (rule function_h_counterpart[OF ww vw access fm])
qed

theorem function_representation_bijection:
  assumes separates: "\<And>w f g. w \<in> W \<Longrightarrow> f \<in> F w \<Longrightarrow> g \<in> F w \<Longrightarrow>
    (\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow>
      app v (iF w v f) a = app v (iF w v g) a) \<Longrightarrow> f = g"
  shows "book_modalized_bijection W le F iF function_domain
    (\<lambda>w v g. book_modalized_exponential_transport W le DA v g) function_h"
proof -
  interpret Target: book_modalized_set W le function_domain "\<lambda>w v g. book_modalized_exponential_transport W le DA v g"
    by (rule function_domain_modalized)
  show ?thesis
  proof unfold_locales
    show "book_modalized_map W le F iF function_domain (\<lambda>w v g. book_modalized_exponential_transport W le DA v g) function_h"
      by (rule function_h_modalized_map)
    fix w
    assume ww: "w \<in> W"
    show "bij_betw (function_h w) (F w) (function_domain w)" by (rule function_h_bijection[OF ww separates[OF ww]])
  qed
qed

end

text \<open>
  Restriction of a represented function is the representation of its
  source counterpart. Consequently the constructed image domains form
  an actual modalized set. Under source quasi-functionality, the entire
  function-type representation is a modalized bijection. Its inverse
  counterpart law follows from the earlier inverse-map theorem.
  The all-type recursion and canonical instantiation remain separate.
\<close>

end
