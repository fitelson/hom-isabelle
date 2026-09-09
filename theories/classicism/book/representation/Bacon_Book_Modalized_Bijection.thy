theory Bacon_Book_Modalized_Bijection
  imports Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Map
begin

section \<open>Inverse maps between represented modalized sets\<close>

locale book_modalized_bijection =
  Source: book_modalized_set W le A iA +
  Target: book_modalized_set W le B iB
  for W :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool"
    and A :: "'w \<Rightarrow> 'a set" and iA :: "'w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a"
    and B :: "'w \<Rightarrow> 'b set" and iB :: "'w \<Rightarrow> 'w \<Rightarrow> 'b \<Rightarrow> 'b" +
  fixes h :: "'w \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes h_map: "book_modalized_map W le A iA B iB h"
    and h_bijection: "w \<in> W \<Longrightarrow> bij_betw (h w) (A w) (B w)"
begin

definition j where "j w = inv_into (A w) (h w)"

lemma h_injective: "w \<in> W \<Longrightarrow> inj_on (h w) (A w)"
  using h_bijection unfolding bij_betw_def by blast

lemma h_image: "w \<in> W \<Longrightarrow> h w ` A w = B w"
  using h_bijection unfolding bij_betw_def by blast

lemma h_type: "w \<in> W \<Longrightarrow> a \<in> A w \<Longrightarrow> h w a \<in> B w"
  by (rule book_modalized_map_type[OF h_map]; assumption)

lemma j_type:
  assumes ww: "w \<in> W" and bm: "b \<in> B w"
  shows "j w b \<in> A w"
proof -
  have member: "b \<in> h w ` A w" using bm by (simp only: h_image[OF ww])
  show ?thesis unfolding j_def by (rule inv_into_into[OF member])
qed

lemma jh:
  "w \<in> W \<Longrightarrow> a \<in> A w \<Longrightarrow> j w (h w a) = a"
  unfolding j_def by (rule inv_into_f_f[OF h_injective]; assumption)

lemma hj:
  assumes ww: "w \<in> W" and bm: "b \<in> B w"
  shows "h w (j w b) = b"
proof -
  have member: "b \<in> h w ` A w" using bm by (simp only: h_image[OF ww])
  show ?thesis unfolding j_def by (rule f_inv_into_f[OF member])
qed

theorem j_natural:
  assumes ww: "w \<in> W" and vw: "v \<in> W" and access: "le w v" and bm: "b \<in> B w"
  shows "j v (iB w v b) = iA w v (j w b)"
proof -
  have jm: "j w b \<in> A w" by (rule j_type[OF ww bm])
  have moved: "iA w v (j w b) \<in> A v" by (rule Source.counterpart_type[OF ww vw access jm])
  have image: "h v (iA w v (j w b)) = iB w v b"
    using book_modalized_map_natural[OF h_map ww vw access jm] by (simp only: hj[OF ww bm])
  show ?thesis by (simp only: image[symmetric]; rule jh[OF vw moved])
qed

theorem inverse_modalized_map:
  "book_modalized_map W le B iB A iA j"
  by (rule book_modalized_mapI; (rule j_type | rule j_natural); assumption)

end

text \<open>
  The forward map h and its fiberwise bijection are the lower-type
  induction hypotheses in Proposition 18.4. The inverse j is constructed
  with inv_into. Its type, two inverse equations and counterpart law
  are proved, not added as further hypotheses. Endpoints are the actual
  Definition 17.3 modalized-set interfaces; empty fibers remain allowed.
\<close>

end
