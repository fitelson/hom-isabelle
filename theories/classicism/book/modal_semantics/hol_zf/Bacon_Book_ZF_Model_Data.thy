theory Bacon_Book_ZF_Model_Data
  imports Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Dependent_Pairs
    Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Set
    Bacon_Source_Vocabulary_Development.Bacon_Source_Syntax
begin

section \<open>Set-theoretic data for an independent modal model\<close>

definition book_ZF_future :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> ZF" where
  "book_ZF_future W R w = Sep W (R w)"

definition book_ZF_pairs :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF" where
  "book_ZF_pairs W R A w = paper_ZF_sigma (book_ZF_future W R w) A"

definition book_ZF_collect :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> (ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "book_ZF_collect W R w P = Sep (book_ZF_future W R w) P"

definition book_ZF_restrict :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "book_ZF_restrict W R A v F = Lambda (book_ZF_pairs W R A v) (\<lambda>p. app F p)"

lemma book_ZF_future_member:
  "Elem v (book_ZF_future W R w) \<longleftrightarrow> Elem v W \<and> R w v"
  by (simp only: book_ZF_future_def Sep)

lemma book_ZF_pairs_member:
  "Elem (Opair v a) (book_ZF_pairs W R A w) \<longleftrightarrow> Elem v W \<and> R w v \<and> Elem a (A v)"
  by (simp only: book_ZF_pairs_def paper_ZF_sigma_pair_member book_ZF_future_member; blast)

lemma book_ZF_collect_member:
  "Elem v (book_ZF_collect W R w P) \<longleftrightarrow> Elem v W \<and> R w v \<and> P v"
  by (simp only: book_ZF_collect_def Sep book_ZF_future_member; blast)

lemma book_ZF_pairs_data:
  assumes member: "Elem p (book_ZF_pairs W R A w)"
  shows "Elem (Fst p) W" and "R w (Fst p)" and "Elem (Snd p) (A (Fst p))"
    and "Opair (Fst p) (Snd p) = p"
  using paper_ZF_sigma_projections[OF member[unfolded book_ZF_pairs_def]]
  by (simp only: book_ZF_future_member; blast)+

locale book_ZF_frame = book_pointed_preorder "explode W" R root
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF

lemma book_ZF_graph_eta:
  "Lambda A (app (Lambda A f)) = Lambda A f"
  by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI; rule Lambda_app; assumption)

text \<open>
  W and every value domain are actual sets in the standard HOL–ZF
  universe. The world type itself is not asserted to be an internal
  set. These definitions have no canonical-world, term-class, proof
  judgment, interpreter or countability parameter.
  The pointed-preorder condition includes @≤w for every w∈W,
  exactly as in Definition 17.1, p.359.
\<close>

end
