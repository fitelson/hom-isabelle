theory Bacon_Book_Conjunction_Simultaneous_Substitution
  imports Bacon_Book_Conjunction_Simultaneous_Substitution_Singleton
    Bacon_Book_Simultaneous_Substitution_Peeling_Free_For
begin

section \<open>Finite simultaneous replacement preserves native theoremhood\<close>

text \<open>
  If ⊢∧A and θ is a finite typed, capture-free replacement table,
  then ⊢∧A[θ]. Source: Definition 5.2, p.99, in the extension of
  §5.2, p.104. All payloads belong to the same native richer language.

  The induction is on table length and generalizes the formula. For
  k↦B, replace k by a fresh variable z; process the remaining table
  with ALL later k entries removed; then insert the ORIGINAL B for z.
  The proved peeling equation makes this simultaneous, single-pass
  substitution even when payloads mention other selected keys.

  The marker avoids the original formula's names and the remaining
  table's key/payload names. Freshness for B itself is unnecessary.
  The three capture conditions are supplied by the generic peeling
  theorem, not assumed separately. Primitive ∧ remains fixed because
  logical symbols are not table keys. No semantic argument or direct
  substitution of the fixed background theory is used in this proof.
\<close>

theorem book_conj_theory_simultaneous_substitution:
  assumes rich: "sg_rich G"
    and derivation: "book_conj_theory_derivable \<Sigma> G {} A"
    and table: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G \<theta>"
    and permitted: "book_simult_free_for G \<theta> A"
  shows "book_conj_theory_derivable \<Sigma> G {} (book_simult_subst G \<theta> A)"
  using derivation table permitted
proof (induction \<theta> arbitrary: A rule: length_induct[case_names smaller])
  case (smaller \<theta>)
  show ?case
  proof (cases \<theta>)
    case Nil
    show ?thesis using smaller.prems(1) by (simp only: Nil book_simult_subst_empty)
  next
    case (Cons entry rest)
    obtain k B where entry_shape: "entry = (k,B)" by (cases entry) auto
    have shape: "\<theta> = (k,B)#rest" using Cons entry_shape by simp
    let ?tail = "book_subst_disable k rest"
    have original_table: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G ((k,B)#rest)"
      using smaller.prems(2) by (simp only: shape)
    have original_free: "book_simult_free_for G ((k,B)#rest) A"
      using smaller.prems(3) by (simp only: shape)
    obtain z where marker_type: "G z = book_subst_key_type k"
      and fresh: "z \<notin> named_vars A \<union> book_subst_table_variables rest"
      using book_subst_marker_exists[where \<sigma>="book_subst_key_type k" and A=A and \<theta>=rest,
        OF rich] by blast
    have fresh_A: "z \<notin> named_vars A" and fresh_table: "z \<notin> book_subst_table_variables rest"
      using fresh by blast+
    have marker: "map_of ?tail (BSVar z (G z)) = None"
      by (simp add: book_subst_lookup_disable book_subst_fresh_key[OF fresh_table])
    have payloads: "z \<notin> named_fv C" if "map_of ?tail j = Some C" for j C
      by (rule book_subst_fresh_payload[OF fresh_table book_subst_disabled_lookup[OF that]])
    have captures:
      "book_simult_free_for G [(k,NVar z)] A \<and>
       book_simult_free_for G ?tail (book_simult_subst G [(k,NVar z)] A) \<and>
       named_free_for B z (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      by (rule book_simult_subst_peeling_free_for[OF fresh_A marker payloads original_free])
    have marker_language: "book_in_language book_conj_logical_type UNIV \<Sigma> G
      (NVar z) (book_subst_key_type k)"
      by (simp only: book_language_var_iff; rule sym[OF marker_type])
    have marker_table: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G [(k,NVar z)]"
      by (rule book_subst_table_language_singleton[OF marker_language])
    have marked: "book_conj_theory_derivable \<Sigma> G {} (book_simult_subst G [(k,NVar z)] A)"
      by (rule book_conj_theory_simult_single[OF rich smaller.prems(1) marker_table conjunct1[OF captures]])
    have shorter_tail: "length ?tail < length \<theta>"
      by (simp only: shape; rule book_subst_disable_shorter)
    have tail_language: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G ?tail"
      by (rule book_subst_table_language_tail_without_head[OF original_table])
    have tail_free: "book_simult_free_for G ?tail (book_simult_subst G [(k,NVar z)] A)"
      by (rule conjunct1[OF conjunct2[OF captures]])
    have residual: "book_conj_theory_derivable \<Sigma> G {}
      (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      using smaller.IH shorter_tail marked tail_language tail_free by blast
    have found: "map_of ((k,B)#rest) k = Some B" by simp
    have head_language: "book_in_language book_conj_logical_type UNIV \<Sigma> G B (G z)"
      using book_subst_table_language_lookup[OF original_table found]
      by (simp only: marker_type)
    have final_free: "named_free_for B z (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      by (rule conjunct2[OF conjunct2[OF captures]])
    have result: "book_conj_theory_derivable \<Sigma> G {}
      (named_subst z B (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A)))"
      by (rule book_conj_theory_variable_substitution[OF rich residual head_language final_free])
    have decomposition: "book_simult_subst G ((k,B)#rest) A =
      named_subst z B (book_simult_subst G ?tail (book_simult_subst G [(k,NVar z)] A))"
      by (rule book_simult_subst_peeling[where G=G and z=z and k=k and A=A and rest=rest,
        OF fresh_A marker payloads])
    show ?thesis using result by (simp only: shape decomposition)
  qed
qed

end
