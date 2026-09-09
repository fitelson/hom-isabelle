theory Bacon_Book_Modal_Implication_Naturality
  imports Bacon_Book_Modal_Implication_Typing
begin

section \<open>Truncation preserves the explicitly local implication value\<close>

context book_preorder
begin

lemma book_preorder_future_subset:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and related: "le w v"
  shows "book_preorder_future worlds le v \<subseteq> book_preorder_future worlds le w"
  using transitive[OF ww vw] related by (auto simp: book_preorder_future_def)

theorem book_future_implication_naturality:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and related: "le w v"
    and pf: "p \<in> book_preorder_powerset worlds le w"
    and qf: "q \<in> book_preorder_powerset worlds le w"
  shows "book_preorder_truncate le
      (book_future_implication_set (book_preorder_future worlds le w) p q) v =
    book_future_implication_set (book_preorder_future worlds le v)
      (book_preorder_truncate le p v) (book_preorder_truncate le q v)"
proof -
  have nesting: "book_preorder_future worlds le v \<subseteq> book_preorder_future worlds le w"
    by (rule book_preorder_future_subset[OF ww vw related])
  have qw: "q \<subseteq> worlds" using qf
    by (auto simp: book_preorder_powerset_def book_preorder_future_def)
  show ?thesis using nesting qw
    by (auto simp: book_preorder_truncate_def book_future_implication_set_def book_preorder_future_def)
qed

theorem book_future_implication_truth:
  assumes world: "w \<in> worlds"
  shows "w \<in> book_future_implication_set (book_preorder_future worlds le w) p q \<longleftrightarrow>
    (w \<in> p \<longrightarrow> w \<in> q)"
  using reflexive[OF world] world
  by (auto simp: book_future_implication_set_def book_preorder_future_def)

end

text \<open>
  These are properties of the explicit future-domain expression, not
  an unqualified transcription of the printed global complement.
  The naturality equation is i_wv(if_w(p,q))=if_v(i_wv(p),i_wv(q)).
  The same-world membership test gives material implication by reflexivity.

  The antecedent's fiber premise records the intended input type; the
  set identity itself needs no further restriction on p. The consequent
  fiber premise excludes points outside the frame. Nothing here asserts
  that a proper sub-modalized proposition domain is closed under if,
  or that a curried higher-order interpretation already exists.
  Source context: Example 17.1 and Definition 18.1(3.3).
\<close>

end
