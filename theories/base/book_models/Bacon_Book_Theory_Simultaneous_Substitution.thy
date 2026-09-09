theory Bacon_Book_Theory_Simultaneous_Substitution
  imports Bacon_Book_Simultaneous_Substitution_Peeling
    Bacon_Book_Simultaneous_Substitution_Peeling_Free_For
    Bacon_Book_Simultaneous_Substitution_Singleton Bacon_Book_Substitution_Freshness
begin

section \<open>Finite simultaneous substitution in the least theory\<close>

text \<open>
  Source obligation: Definition 5.2 and Comprehension Check 5.1,
  pp.99/102. A capture-free finite simultaneous substitution preserves
  empty-premise derivability. The induction is on the table length, not
  on a presumed linewise substitution of proofs through Gen.

  For a head entry k↦B, first replace k by a fresh typed variable z.
  Recursively process the remaining table with every duplicate k removed.
  Finally insert the ORIGINAL B for z. Other payloads contain no free z,
  so they remain unchanged. Cross-references among replaced names are
  therefore permitted. Every step uses an already derived rule of the
  original nine-constructor calculus, with the same signature Σ.
\<close>

theorem book_theory_simultaneous_substitution:
  assumes rich: "sg_rich G" and proof_A: "book_theory_derivable \<Sigma> G {} A"
    and table: "book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G \<theta>"
    and permitted: "book_simult_free_for G \<theta> A"
  shows "book_theory_derivable \<Sigma> G {} (book_simult_subst G \<theta> A)"
  using proof_A table permitted
proof (induction \<theta> arbitrary: A rule: length_induct[case_names shorter])
  case (shorter \<theta>)
  show ?case
  proof (cases \<theta>)
    case Nil
    show ?thesis using shorter.prems(1) by (simp only: Nil book_simult_subst_empty)
  next
    case (Cons entry rest)
    obtain k B where entry: "entry = (k,B)" by (cases entry) auto
    have shape: "\<theta> = (k,B)#rest" using Cons entry by simp
    let ?tail = "book_subst_disable k rest"
    have original_table: "book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G ((k,B)#rest)"
      using shorter.prems(2) by (simp only: shape)
    have original_free: "book_simult_free_for G ((k,B)#rest) A"
      using shorter.prems(3) by (simp only: shape)
    obtain z where typed: "G z = book_subst_key_type k"
      and fresh: "z \<notin> named_vars A \<union> book_subst_table_variables rest"
      using book_subst_marker_exists[where \<sigma>="book_subst_key_type k" and A=A and \<theta>=rest,
        OF rich] by (elim exE conjE)
    have fresh_A: "z \<notin> named_vars A" and fresh_table: "z \<notin> book_subst_table_variables rest"
      using fresh by blast+
    have marker: "map_of ?tail (BSVar z (G z)) = None"
      by (simp add: book_subst_lookup_disable book_subst_fresh_key[OF fresh_table])
    have payloads: "z \<notin> named_fv C" if "map_of ?tail j = Some C" for j C
      by (rule book_subst_fresh_payload[OF fresh_table book_subst_disabled_lookup[OF that]])
    have capture_conditions:
      "book_simult_free_for G [(k,NVar z)] A \<and>
       book_simult_free_for G ?tail (book_simult_subst G [(k,NVar z)] A) \<and>
       named_free_for B z (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      by (rule book_simult_subst_peeling_free_for[OF fresh_A marker payloads original_free])
    have marker_typed: "has_ntype book_minimal_logical_type G (NVar z) (G z)"
      by (rule has_ntype.Var)
    have marker_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
      (NVar z) (book_subst_key_type k)"
      using marker_typed by (simp add: book_in_language_def named_in_language_def typed)
    have marked: "book_theory_derivable \<Sigma> G {} (book_simult_subst G [(k,NVar z)] A)"
      by (rule book_theory_simult_single[OF rich shorter.prems(1) marker_language conjunct1[OF capture_conditions]])
    have shorter: "length ?tail < length \<theta>"
      by (simp only: shape; rule book_subst_disable_shorter)
    have tail_language: "book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G ?tail"
      by (rule book_subst_table_language_tail_without_head[OF original_table])
    have tail_free: "book_simult_free_for G ?tail (book_simult_subst G [(k,NVar z)] A)"
      using capture_conditions by blast
    have residual: "book_theory_derivable \<Sigma> G {}
      (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      using shorter.IH shorter marked tail_language tail_free by blast
    have head_lookup: "map_of ((k,B)#rest) k = Some B" by simp
    have head_language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G z)"
      using book_subst_table_language_lookup[OF original_table head_lookup]
      by (simp only: typed)
    have final_free: "named_free_for B z (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      using capture_conditions by blast
    have result: "book_theory_derivable \<Sigma> G {}
      (named_subst z B (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A)))"
      by (rule book_theory_variable_substitution[OF rich residual head_language final_free])
    have decomposition: "book_simult_subst G ((k,B)#rest) A =
      named_subst z B (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      by (rule book_simult_subst_peeling[where G=G and z=z and k=k and A=A and rest=rest,
            OF fresh_A marker payloads])
    show ?thesis using result by (simp only: shape decomposition)
  qed
qed

end
