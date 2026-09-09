theory Bacon_Book_Modalized_Map
  imports Bacon_Book_Modalized_Set Bacon_Source_Image_Action
begin

section \<open>Independent world-indexed maps commuting with counterparts\<close>

definition book_modalized_map ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow>
    ('w \<Rightarrow> 'a set) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('w \<Rightarrow> 'b set) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    ('w \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "book_modalized_map W le A iA B iB f \<longleftrightarrow>
    (\<forall>w\<in>W. \<forall>a\<in>A w. f w a \<in> B w) \<and>
    (\<forall>w\<in>W. \<forall>v\<in>W. le w v \<longrightarrow> (\<forall>a\<in>A w. f v (iA w v a) = iB w v (f w a)))"

lemma book_modalized_mapI:
  assumes typed: "\<And>w a. w \<in> W \<Longrightarrow> a \<in> A w \<Longrightarrow> f w a \<in> B w"
    and natural: "\<And>w v a. w \<in> W \<Longrightarrow> v \<in> W \<Longrightarrow> le w v \<Longrightarrow>
      a \<in> A w \<Longrightarrow> f v (iA w v a) = iB w v (f w a)"
  shows "book_modalized_map W le A iA B iB f"
  using typed natural unfolding book_modalized_map_def by blast

lemma book_modalized_map_type:
  "book_modalized_map W le A iA B iB f \<Longrightarrow> w \<in> W \<Longrightarrow> a \<in> A w \<Longrightarrow> f w a \<in> B w"
  unfolding book_modalized_map_def by blast

lemma book_modalized_map_natural:
  "book_modalized_map W le A iA B iB f \<Longrightarrow> w \<in> W \<Longrightarrow> v \<in> W \<Longrightarrow>
    le w v \<Longrightarrow> a \<in> A w \<Longrightarrow> f v (iA w v a) = iB w v (f w a)"
  unfolding book_modalized_map_def by blast

theorem book_modalized_map_action_map:
  assumes family: "book_modalized_map W le A iA B iB f"
  shows "paper_action_map W (book_preorder_arrows W le) fst snd
    A (\<lambda>h. iA (fst h) (snd h)) B (\<lambda>h. iB (fst h) (snd h)) f"
proof (rule paper_action_mapI)
  fix w a
  assume ww: "w \<in> W" and member: "a \<in> A w"
  show "f w a \<in> B w" by (rule book_modalized_map_type[OF family ww member])
next
  fix h a
  assume arrow: "h \<in> book_preorder_arrows W le" and member: "a \<in> A (fst h)"
  have sw: "fst h \<in> W" and tw: "snd h \<in> W" and related: "le (fst h) (snd h)"
    using arrow by (simp_all add: book_preorder_arrow_member)
  show "f (snd h) (iA (fst h) (snd h) a) = iB (fst h) (snd h) (f (fst h) a)"
    by (rule book_modalized_map_natural[OF family sw tw related member])
qed

theorem book_modalized_map_from_action_map:
  assumes family: "paper_action_map W (book_preorder_arrows W le) fst snd
    A (\<lambda>h. iA (fst h) (snd h)) B (\<lambda>h. iB (fst h) (snd h)) f"
  shows "book_modalized_map W le A iA B iB f"
proof (rule book_modalized_mapI)
  fix w a
  assume ww: "w \<in> W" and member: "a \<in> A w"
  show "f w a \<in> B w" by (rule paper_action_map_type[OF family ww member])
next
  fix w v a
  assume ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v" and member: "a \<in> A w"
  have arrow: "(w,v) \<in> book_preorder_arrows W le"
    by (simp only: book_preorder_arrow_pair; rule conjI[OF ww conjI[OF vw related]])
  have source_member: "a \<in> A (fst (w,v))" by (simp only: fst_conv; rule member)
  show "f v (iA w v a) = iB w v (f w a)"
    using paper_action_map_equivariant[OF family arrow source_member] by simp
qed

theorem book_modalized_map_iff_action_map:
  "book_modalized_map W le A iA B iB f \<longleftrightarrow>
    paper_action_map W (book_preorder_arrows W le) fst snd
      A (\<lambda>h. iA (fst h) (snd h)) B (\<lambda>h. iB (fst h) (snd h)) f"
  by (rule iffI; (rule book_modalized_map_action_map | rule book_modalized_map_from_action_map); assumption)

lemma book_modalized_map_identity:
  "book_modalized_map W le A iA A iA (\<lambda>w a. a)"
  by (rule book_modalized_mapI; simp)

theorem book_modalized_map_compose:
  assumes first: "book_modalized_map W le A iA B iB f"
    and second: "book_modalized_map W le B iB C iC g"
  shows "book_modalized_map W le A iA C iC (\<lambda>w a. g w (f w a))"
proof (rule book_modalized_mapI)
  fix w a
  assume ww: "w \<in> W" and member: "a \<in> A w"
  have intermediate: "f w a \<in> B w" by (rule book_modalized_map_type[OF first ww member])
  show "g w (f w a) \<in> C w" by (rule book_modalized_map_type[OF second ww intermediate])
next
  fix w v a
  assume ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v" and member: "a \<in> A w"
  have intermediate: "f w a \<in> B w" by (rule book_modalized_map_type[OF first ww member])
  have first_eq: "f v (iA w v a) = iB w v (f w a)"
    by (rule book_modalized_map_natural[OF first ww vw related member])
  have second_eq: "g v (iB w v (f w a)) = iC w v (g w (f w a))"
    by (rule book_modalized_map_natural[OF second ww vw related intermediate])
  show "g v (f v (iA w v a)) = iC w v (g w (f w a))" by (simp only: first_eq second_eq)
qed

text \<open>
  Definition 17.4, p.361, requires f(w,−):A_w→B_w and
  f(v,iA_wv(a))=iB_wv(f(w,a)). The raw predicate records exactly
  those two guarded clauses; to regard it as a homomorphism of
  modalized sets, the endpoints are separately required to satisfy
  book_modalized_set. The displayed equivalence is already true
  for raw families and hence needs no concealed endpoint assumption.

  The source and target fibers may have different HOL carriers.
  Identity and composition give Examples 17.4–17.5 at modalized
  endpoints. Empty fibers are permitted, and no injectivity,
  surjectivity, root condition or logical interpretation is imposed.
\<close>

end
