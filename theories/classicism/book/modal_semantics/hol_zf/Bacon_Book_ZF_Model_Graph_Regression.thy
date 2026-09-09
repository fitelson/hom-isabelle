theory Bacon_Book_ZF_Model_Graph_Regression
  imports Bacon_Book_ZF_Model_Data
begin

theorem book_ZF_isFun_domain_insufficient:
  "isFun (Singleton Empty) \<and> Domain (Singleton Empty) = Empty \<and>
    Singleton Empty \<noteq> Lambda Empty (app (Singleton Empty))"
proof -
  have no_pair: "\<not> Elem (Opair x y) (Singleton Empty)" for x y
    by (simp add: Singleton Opair_def Upair_nonEmpty)
  have single_valued: "isFun (Singleton Empty)" unfolding isFun_def using no_pair by blast
  have domain_empty: "Domain (Singleton Empty) = Empty"
    by (rule iffD2[OF Ext]; simp only: Domain no_pair Empty; blast)
  have empty_graph: "Lambda Empty f = Empty" for f
    by (rule iffD2[OF Ext]; simp only: Lambda_def Repl Empty; blast)
  have nonempty: "Singleton Empty \<noteq> Empty" by (simp add: Singleton_def Upair_nonEmpty)
  show ?thesis by (simp only: single_valued domain_empty empty_graph; use nonempty in blast)
qed

text \<open>
  HOL–ZF's isFun checks single-valuedness but does not require every
  element to be an ordered pair. The singleton containing the empty
  set therefore passes isFun and has empty Domain, yet it is not the
  empty function graph. This checked regression explains why the
  independent modal structure requires exact Lambda reconstruction.
  The canonical and existing Fun(A,B) graph constructions are unaffected.
\<close>

end
