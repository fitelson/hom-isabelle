theory Bacon_Book_Modal_Implication_Typing
  imports Bacon_Book_Preorder_Powerset
begin

section \<open>The printed global complement and the future-domain reading\<close>

definition book_printed_implication_set :: "'w set \<Rightarrow> 'w set \<Rightarrow> 'w set \<Rightarrow> 'w set" where
  "book_printed_implication_set W p q = (W - p) \<union> q"

definition book_future_implication_set :: "'w set \<Rightarrow> 'w set \<Rightarrow> 'w set \<Rightarrow> 'w set" where
  "book_future_implication_set F p q = (F - p) \<union> q"

lemma book_printed_implication_local_iff:
  assumes antecedent: "p \<subseteq> F" and consequent: "q \<subseteq> F"
  shows "book_printed_implication_set W p q \<subseteq> F \<longleftrightarrow> W \<subseteq> F"
  using antecedent consequent unfolding book_printed_implication_set_def by blast

lemma book_future_implication_type:
  assumes consequent: "q \<subseteq> F"
  shows "book_future_implication_set F p q \<in> Pow F"
  using consequent unfolding book_future_implication_set_def by blast

lemma book_printed_implication_restriction:
  assumes future: "F \<subseteq> W" and consequent: "q \<subseteq> F"
  shows "book_printed_implication_set W p q \<inter> F = book_future_implication_set F p q"
  using future consequent unfolding book_printed_implication_set_def book_future_implication_set_def by blast

theorem book_printed_implication_future_iff:
  assumes antecedent: "p \<in> book_preorder_powerset W le v"
    and consequent: "q \<in> book_preorder_powerset W le v"
  shows "book_printed_implication_set W p q \<in> book_preorder_powerset W le v \<longleftrightarrow>
    book_preorder_future W le v = W"
proof -
  let ?F = "book_preorder_future W le v"
  have pf: "p \<subseteq> ?F" and qf: "q \<subseteq> ?F"
    using antecedent consequent by (simp_all add: book_preorder_powerset_def)
  have fw: "?F \<subseteq> W" by (auto simp: book_preorder_future_def)
  have typing: "book_printed_implication_set W p q \<subseteq> ?F \<longleftrightarrow> W \<subseteq> ?F"
    by (rule book_printed_implication_local_iff[OF pf qf])
  show ?thesis using typing fw by (auto simp: book_preorder_powerset_def)
qed

section \<open>A two-world regression for the untruncated expression\<close>

lemma book_two_world_pointed_preorder:
  "book_pointed_preorder (UNIV :: bool set) (\<lambda>w v. w \<longrightarrow> v) False"
  by unfold_locales auto

theorem book_printed_implication_two_world_failure:
  "book_pointed_preorder (UNIV :: bool set) (\<lambda>w v. w \<longrightarrow> v) False \<and>
    {} \<in> book_preorder_powerset UNIV (\<lambda>w v. w \<longrightarrow> v) True \<and>
    book_printed_implication_set UNIV {} {} \<notin>
      book_preorder_powerset UNIV (\<lambda>w v. w \<longrightarrow> v) True"
  by (rule conjI[OF book_two_world_pointed_preorder];
    auto simp: book_preorder_powerset_def book_preorder_future_def book_printed_implication_set_def)

text \<open>
  Definition 18.1(3.3), printed p.391, writes
  if(w,p)(v,q)=(W ∖ i_wv(p))∪q. Example 17.1, p.360,
  places the result in Pow(W↑v). Here p denotes the already transported
  antecedent i_wv(p), so both arguments are subsets of that future cone.

  The first equivalence proves that the untruncated printed expression
  has the required set type only when W↑v=W. The two-world example
  witnesses the failure on an ordinary pointed preorder: False≤True,
  while W↑True={True}, and the displayed expression on empty inputs is W.
  This is a typing regression, not a countermodel to Classicism or a
  proof that the book's intended modal semantics fails.

  The restriction theorem records the exact relation to the future-domain
  reading: intersecting the printed result with W↑v gives
  ((W↑v)∖i_wv(p))∪q. The two expressions are named separately;
  no model axiom is silently changed and no higher-order logical closure,
  interpretation, or completeness claim is supplied by these set lemmas.
\<close>

end
