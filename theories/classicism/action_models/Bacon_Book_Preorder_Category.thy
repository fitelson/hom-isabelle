theory Bacon_Book_Preorder_Category
  imports Bacon_Source_Rooted_Category
begin

section \<open>The thin category associated with a preorder on a world set\<close>

definition book_preorder_arrows :: "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<times> 'w) set" where
  "book_preorder_arrows W le = {(w,v). w \<in> W \<and> v \<in> W \<and> le w v}"

definition book_preorder_identity :: "'w \<Rightarrow> 'w \<times> 'w" where
  "book_preorder_identity w = (w,w)"

definition book_preorder_compose :: "('w \<times> 'w) \<Rightarrow> ('w \<times> 'w) \<Rightarrow> 'w \<times> 'w" where
  "book_preorder_compose g f = (fst f, snd g)"

lemma book_preorder_arrow_pair [simp]:
  "(w,v) \<in> book_preorder_arrows W le \<longleftrightarrow> w \<in> W \<and> v \<in> W \<and> le w v"
  by (simp add: book_preorder_arrows_def)

lemma book_preorder_arrow_member:
  "f \<in> book_preorder_arrows W le \<longleftrightarrow> fst f \<in> W \<and> snd f \<in> W \<and> le (fst f) (snd f)"
  by (cases f) simp

lemma book_preorder_arrow_unique:
  assumes sources: "fst f = fst g" and targets: "snd f = snd g"
  shows "f = g"
  using sources targets by (cases f; cases g; simp)

locale book_preorder =
  fixes worlds :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool"
  assumes reflexive: "w \<in> worlds \<Longrightarrow> le w w"
    and transitive: "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> u \<in> worlds \<Longrightarrow>
      le w v \<Longrightarrow> le v u \<Longrightarrow> le w u"
begin

lemma book_preorder_compose_arrow:
  assumes first: "f \<in> book_preorder_arrows worlds le"
    and second: "g \<in> book_preorder_arrows worlds le" and meeting: "snd f = fst g"
  shows "book_preorder_compose g f \<in> book_preorder_arrows worlds le"
proof -
  have fw: "fst f \<in> worlds" and fv: "snd f \<in> worlds" and fr: "le (fst f) (snd f)"
    using first by (simp_all add: book_preorder_arrow_member)
  have gu: "snd g \<in> worlds" and gr: "le (fst g) (snd g)"
    using second by (simp_all add: book_preorder_arrow_member)
  have next_relation: "le (snd f) (snd g)" by (simp only: meeting; rule gr)
  have composite: "le (fst f) (snd g)" by (rule transitive[OF fw fv gu fr next_relation])
  show ?thesis by (simp only: book_preorder_compose_def book_preorder_arrow_pair; rule conjI[OF fw conjI[OF gu composite]])
qed

sublocale Category: paper_category worlds "book_preorder_arrows worlds le"
  fst snd book_preorder_compose book_preorder_identity
proof unfold_locales
  fix f
  assume "f \<in> book_preorder_arrows worlds le"
  then show "fst f \<in> worlds" by (simp add: book_preorder_arrow_member)
next
  fix f
  assume "f \<in> book_preorder_arrows worlds le"
  then show "snd f \<in> worlds" by (simp add: book_preorder_arrow_member)
next
  fix w
  assume world: "w \<in> worlds"
  show "book_preorder_identity w \<in> book_preorder_arrows worlds le"
    by (simp only: book_preorder_identity_def book_preorder_arrow_pair; rule conjI[OF world conjI[OF world reflexive[OF world]]])
next
  show "\<And>w. w \<in> worlds \<Longrightarrow> fst (book_preorder_identity w) = w"
    by (simp add: book_preorder_identity_def)
  show "\<And>w. w \<in> worlds \<Longrightarrow> snd (book_preorder_identity w) = w"
    by (simp add: book_preorder_identity_def)
  show "\<And>f g. f \<in> book_preorder_arrows worlds le \<Longrightarrow> g \<in> book_preorder_arrows worlds le \<Longrightarrow>
      snd f = fst g \<Longrightarrow> book_preorder_compose g f \<in> book_preorder_arrows worlds le"
    by (rule book_preorder_compose_arrow; assumption)
  show "\<And>f g. f \<in> book_preorder_arrows worlds le \<Longrightarrow> g \<in> book_preorder_arrows worlds le \<Longrightarrow>
      snd f = fst g \<Longrightarrow> fst (book_preorder_compose g f) = fst f"
    by (simp add: book_preorder_compose_def)
  show "\<And>f g. f \<in> book_preorder_arrows worlds le \<Longrightarrow> g \<in> book_preorder_arrows worlds le \<Longrightarrow>
      snd f = fst g \<Longrightarrow> snd (book_preorder_compose g f) = snd g"
    by (simp add: book_preorder_compose_def)
  show "\<And>f g h. f \<in> book_preorder_arrows worlds le \<Longrightarrow> g \<in> book_preorder_arrows worlds le \<Longrightarrow>
      h \<in> book_preorder_arrows worlds le \<Longrightarrow> snd f = fst g \<Longrightarrow> snd g = fst h \<Longrightarrow>
      book_preorder_compose h (book_preorder_compose g f) = book_preorder_compose (book_preorder_compose h g) f"
    by (simp add: book_preorder_compose_def)
  show "\<And>f. f \<in> book_preorder_arrows worlds le \<Longrightarrow> book_preorder_compose (book_preorder_identity (snd f)) f = f"
    by (simp add: book_preorder_compose_def book_preorder_identity_def)
  show "\<And>f. f \<in> book_preorder_arrows worlds le \<Longrightarrow> book_preorder_compose f (book_preorder_identity (fst f)) = f"
    by (simp add: book_preorder_compose_def book_preorder_identity_def)
qed

end

locale book_pointed_preorder = book_preorder worlds le
  for worlds :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool" +
  fixes root :: 'w
  assumes root_world: "root \<in> worlds"
    and root_below: "w \<in> worlds \<Longrightarrow> le root w"
begin

sublocale Rooted: paper_rooted_category worlds "book_preorder_arrows worlds le"
  fst snd book_preorder_compose book_preorder_identity root
proof unfold_locales
  show "root \<in> worlds" by (rule root_world)
next
  fix w
  assume world: "w \<in> worlds"
  have arrow: "(root,w) \<in> book_preorder_arrows worlds le"
    by (simp only: book_preorder_arrow_pair; rule conjI[OF root_world conjI[OF world root_below[OF world]]])
  show "\<exists>h\<in>book_preorder_arrows worlds le. fst h = root \<and> snd h = w"
    by (rule bexI[where x="(root,w)"], simp, rule arrow)
qed

end

text \<open>
  This is Definition 17.1 on printed p.359: ≤ is reflexive and
  transitive on W and @≤w for every w∈W. No antisymmetry is
  assumed, and mutually accessible distinct worlds are not identified.
  An arrow is the pair (w,v), so each hom-set has at most one element.
  Composition is g AFTER f. The result uses only the generic category
  interfaces, not any logical interpretation or modal-model condition.
\<close>

end
