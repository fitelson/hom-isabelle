theory Bacon_Book_ZF_Model_Assignments
  imports Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Operator_Restriction
    Bacon_Book_Environment_Development.Bacon_Book_Language
    Bacon_Book_Environment_Development.Bacon_Book_Total_Assignments
begin

definition book_ZF_move :: "book_ZF_counterparts \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> nat \<Rightarrow> ZF" where
  "book_ZF_move i G w v g n = i (G n) w v (g n)"

context book_ZF_modal_structure
begin

theorem assignment_move_typed:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and access: "R w v"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G (book_ZF_move i G w v g)"
  unfolding book_env_typed_def book_ZF_move_def
  by (intro allI; rule transport_type[OF ww vw access book_env_at[OF typed]])

theorem assignment_move_composition:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and uw: "u \<in> explode W"
    and wv: "R w v" and vu: "R v u"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_move i G w u g = book_ZF_move i G v u (book_ZF_move i G w v g)"
  by (rule ext; simp only: book_ZF_move_def; rule transport_composition[OF ww vw uw wv vu book_env_at[OF typed]])

end

lemma book_ZF_move_update:
  "book_ZF_move i G w v (g(n := a)) = (book_ZF_move i G w v g)(n := i (G n) w v a)"
  by (rule ext; simp add: book_ZF_move_def)

text \<open>
  These are the assignment maps iᵂᵛ∘g of Definition 17.13.
  Typing and composition are consequences of modalized-set
  transport; updating one variable changes only that variable's
  transported value. No interpretation or proof judgment is assumed.
\<close>

end
