theory Bacon_Book_Modalized_Evaluation
  imports Bacon_Book_Modalized_Product Bacon_Book_Modalized_Exponential_Transport
    Bacon_Book_Modalized_Map
begin

section \<open>Evaluation is a homomorphism of modalized sets\<close>

definition book_modalized_evaluate :: "'w \<Rightarrow> ((('w \<times> 'a) \<Rightarrow> 'b) \<times> 'a) \<Rightarrow> 'b" where
  "book_modalized_evaluate w p = (fst p) (w,snd p)"

theorem book_modalized_evaluation_source:
  assumes source: "book_modalized_set W le A iA" and target: "book_modalized_set W le B iB"
  shows "book_modalized_set W le
    (\<lambda>w. book_modalized_exponential W le A iA B iB w \<times> A w)
    (\<lambda>w v p. (book_modalized_exponential_transport W le A v (fst p), iA w v (snd p)))"
  by (rule book_modalized_product[OF book_modalized_exponential_is_modalized_set[OF source target] source])

theorem book_modalized_evaluation_map:
  assumes source: "book_modalized_set W le A iA" and target: "book_modalized_set W le B iB"
  shows "book_modalized_map W le
    (\<lambda>w. book_modalized_exponential W le A iA B iB w \<times> A w)
    (\<lambda>w v p. (book_modalized_exponential_transport W le A v (fst p), iA w v (snd p)))
    B iB book_modalized_evaluate"
proof -
  interpret X: book_modalized_set W le A iA by (rule source)
  show ?thesis
  proof (rule book_modalized_mapI)
    fix w p
    assume ww: "w \<in> W"
      and member: "p \<in> book_modalized_exponential W le A iA B iB w \<times> A w"
    have fp: "fst p \<in> book_modalized_exponential W le A iA B iB w" and ap: "snd p \<in> A w"
      using member by auto
    show "book_modalized_evaluate w p \<in> B w"
      unfolding book_modalized_evaluate_def
      by (rule book_modalized_exponential_type[OF fp ww X.reflexive[OF ww] ap])
  next
    fix w v p
    assume ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v"
      and member: "p \<in> book_modalized_exponential W le A iA B iB w \<times> A w"
    have fp: "fst p \<in> book_modalized_exponential W le A iA B iB w" and ap: "snd p \<in> A w"
      using member by auto
    have moved_argument: "iA w v (snd p) \<in> A v" by (rule X.counterpart_type[OF ww vw related ap])
    have pair: "(v,iA w v (snd p)) \<in> book_modalized_exponential_pairs W le A v"
      using vw X.reflexive[OF vw] moved_argument by (simp add: book_modalized_exponential_pairs_iff)
    have natural: "iB w v ((fst p) (w,snd p)) = (fst p) (v,iA w v (snd p))"
      by (rule book_modalized_exponential_natural[OF fp ww X.reflexive[OF ww] vw related ap])
    show "book_modalized_evaluate v
        (book_modalized_exponential_transport W le A v (fst p), iA w v (snd p)) =
      iB w v (book_modalized_evaluate w p)"
      by (simp only: book_modalized_evaluate_def fst_conv snd_conv
        book_modalized_exponential_transport_on[OF pair]; rule natural[symmetric])
  qed
qed

text \<open>
  Definition 17.6 and the concrete exponential interpretation use
  App(w,(f,a))=f(w,a). Its typing follows from the exponential
  fiber condition at the reflexive pair (w,a). Naturality is the
  defining homomorphism equation for f, with the transported argument
  proved to belong to the later fiber before evaluation.

  The source product and the evaluation map are proved separately.
  Together with the supplied target structure, they give an actual
  homomorphism of modalized sets. No λ interpretation, chosen proper
  function subdomain, combinator membership or logical model is assumed.
  The map equation itself needs only the source endpoint laws; the target
  endpoint is retained here to give the intended homomorphism setting.
\<close>

end
