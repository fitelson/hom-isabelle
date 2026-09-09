theory Bacon_Book_ZF_Modal_Structure
  imports Bacon_Book_ZF_Model_Operations
begin

section \<open>Independent concrete modalized structure and proposition domains\<close>

locale book_ZF_modal_structure = book_ZF_frame W R root
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF +
  fixes D :: book_ZF_domains and i :: book_ZF_counterparts
  assumes domains: "\<And>\<sigma>. book_modalized_set (explode W) R (\<lambda>w. explode (D \<sigma> w)) (i \<sigma>)"
    and propositions: "\<And>w p. w \<in> explode W \<Longrightarrow> p \<in> explode (D Prop w) \<Longrightarrow>
      explode p \<subseteq> explode (book_ZF_future W R w)"
    and proposition_restriction: "\<And>w v p. w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow>
      R w v \<Longrightarrow> p \<in> explode (D Prop w) \<Longrightarrow> i Prop w v p = Sep p (R v)"
    and function_graph: "\<And>w \<sigma> \<tau> F. w \<in> explode W \<Longrightarrow> F \<in> explode (D (Arr \<sigma> \<tau>) w) \<Longrightarrow>
      F = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)"
    and function_type: "\<And>w v \<sigma> \<tau> F a. w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow>
      F \<in> explode (D (Arr \<sigma> \<tau>) w) \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      app F (Opair v a) \<in> explode (D \<tau> v)"
    and function_natural: "\<And>w v u \<sigma> \<tau> F a. w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> u \<in> explode W \<Longrightarrow>
      R w v \<Longrightarrow> R v u \<Longrightarrow> F \<in> explode (D (Arr \<sigma> \<tau>) w) \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      i \<tau> v u (app F (Opair v a)) = app F (Opair u (i \<sigma> v u a))"
    and function_restriction: "\<And>w v \<sigma> \<tau> F. w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow>
      F \<in> explode (D (Arr \<sigma> \<tau>) w) \<Longrightarrow> i (Arr \<sigma> \<tau>) w v F = book_ZF_restrict W R (D \<sigma>) v F"
begin

lemma function_graph_domain:
  assumes ww: "w \<in> explode W" and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) w)"
  shows "isFun F \<and> Domain F = book_ZF_pairs W R (D \<sigma>) w"
proof -
  have equation: "F = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)" by (rule function_graph[OF ww fm])
  have graph: "isFun (Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)) \<and>
    Domain (Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)) = book_ZF_pairs W R (D \<sigma>) w"
    by (simp only: isFun_Lambda domain_Lambda; simp)
  show ?thesis using graph by (simp only: equation[symmetric])
qed

lemma transport_type:
  "w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow>
    a \<in> explode (D \<sigma> w) \<Longrightarrow> i \<sigma> w v a \<in> explode (D \<sigma> v)"
  by (rule book_modalized_set.counterpart_type[OF domains]; assumption)

lemma transport_identity:
  "w \<in> explode W \<Longrightarrow> a \<in> explode (D \<sigma> w) \<Longrightarrow> i \<sigma> w w a = a"
  by (rule book_modalized_set.counterpart_identity[OF domains]; assumption)

lemma transport_composition:
  "w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> u \<in> explode W \<Longrightarrow>
    R w v \<Longrightarrow> R v u \<Longrightarrow> a \<in> explode (D \<sigma> w) \<Longrightarrow>
    i \<sigma> w u a = i \<sigma> v u (i \<sigma> w v a)"
  by (rule book_modalized_set.counterpart_compose[OF domains]; assumption)

end

text \<open>
  These fields transcribe the concrete function-space and subdomain
  conditions of Definitions 17.9–17.11 and 18.1(1–2). Function values
  are actual Lambda graphs on all typed future pairs, with typed outputs and
  the homomorphism equation; their counterparts are restrictions.
  Propositions are actual future subsets with truncation counterparts.
  No full exponential, nonempty domain, false proposition, logical
  operation membership, interpreter or proof-theoretic premise is assumed.
  HOL–ZF isFun alone states only single-valuedness; exact Lambda
  reconstruction additionally excludes non-pair junk in a value.
\<close>

end
