theory Bacon_Book_Full_Ambient_Henkin_Successor
  imports Bacon_Book_Full_Ambient_Henkin_Extension Bacon_Book_Full_Classicism_Closed_Successor
begin

context book_countable_ambient_signature
begin

section \<open>A witness-complete successor inside the fixed ambient language\<close>

theorem book_full_C_ambient_henkin_successor_exists:
  assumes rich: "sg_rich G" and world: "book_full_C_closed_maximal_extension \<Sigma> G T w"
    and pl: "book_theory_formula \<Sigma> G P" and closed: "named_fv P = {}"
    and missing: "book_box G P \<notin> w"
  shows "\<exists>v. book_full_C_closed_maximal_extension (book_ambient_henkin_signature G) G {} v \<and>
    book_full_C_theory_consistent (book_ambient_henkin_signature G) G v \<and>
    book_closed_constant_witness_complete (book_ambient_henkin_signature G) G v \<and>
    book_not G P \<in> v \<and> P \<notin> v \<and> book_C_unboxed_sentences \<Sigma> G w \<subseteq> v"
proof -
  let ?K = "book_C_unboxed_sentences \<Sigma> G w"
  let ?\<Omega> = "book_ambient_henkin_signature G"
  obtain u where maximal_u: "book_full_C_closed_maximal_extension \<Sigma> G (insert (book_not G P) ?K) u"
    and negative_u: "book_not G P \<in> u" and kernel_u: "?K \<subseteq> u"
    using book_full_C_closed_successor_exists[OF rich world pl closed missing] by blast
  have uc: "book_full_C_theory_consistent \<Sigma> G u" by (rule book_full_C_closed_maximal_consistent[OF rich maximal_u])
  have udata: "book_closed_formula_set \<Sigma> G u" by (rule book_full_C_closed_maximal_data(1)[OF maximal_u])
  have ul: "book_theory_formula \<Sigma> G A" if "A \<in> u" for A
    by (rule conjunct1[OF book_closed_formula_set_member[OF udata that]])
  obtain v where maximal_v: "book_full_C_closed_maximal_extension ?\<Omega> G {} v"
    and vc: "book_full_C_theory_consistent ?\<Omega> G v"
    and originals: "\<forall>A\<in>u. book_universal_closure G A \<in> v"
    and witnesses: "book_closed_constant_witness_complete ?\<Omega> G v"
    using book_full_C_ambient_henkin_extension_exists[OF rich ul uc] by blast
  have extends: "u \<subseteq> v"
  proof
    fix A
    assume member: "A \<in> u"
    have ac: "named_fv A = {}" by (rule conjunct2[OF book_closed_formula_set_member[OF udata member]])
    have closure_in_v: "book_universal_closure G A \<in> v" by (rule bspec[OF originals member])
    show "A \<in> v" using closure_in_v by (simp only: book_universal_closure_of_closed[OF ac])
  qed
  have negative: "book_not G P \<in> v" by (rule subsetD[OF extends negative_u])
  have kernel: "?K \<subseteq> v" by (rule subset_trans[OF kernel_u extends])
  have unchanged: "book_typed_name_map (\<lambda>\<tau> c. c) P = P" by (rule book_typed_name_map_id)
  have maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> c \<in> ?\<Omega> \<tau>"
    by (rule subsetD[OF book_ambient_henkin_signature_contains]; assumption)
  have new_pl: "book_theory_formula ?\<Omega> G P"
    using book_typed_name_map_language[where \<rho>="\<lambda>\<tau> c. c", OF pl maps] by (simp only: unchanged)
  have H_maximal: "book_closed_maximal_extension ?\<Omega> G (book_full_C_closed_theorems ?\<Omega> G \<union> {}) v"
    using maximal_v unfolding book_full_C_closed_maximal_extension_def .
  have absent: "P \<notin> v"
    using negative book_closed_maximal_negation_iff[OF rich H_maximal new_pl closed] by blast
  show ?thesis by (rule exI[where x=v], rule conjI[OF maximal_v conjI[OF vc
    conjI[OF witnesses conjI[OF negative conjI[OF absent kernel]]]]])
qed

end

text \<open>
  Proposition 18.3's successor construction, with explicit countable
  ambient-language hypotheses: when □P is absent, first obtain a
  consistent closed successor seed, then take its old-name-preserving
  Henkin completion. The resulting v contains ¬P and every old A with
  □A ∈ w, and has witnesses for every closed predicate in its own Ω.
  The preceding theory proves Σσ ⊆ Ωσ ⊆ Bσ and infinite Bσ − Ωσ.

  This is an actual successor set, not an assumption about an unspecified
  model. Organizing these pairs (Ω,v) as worlds, proving the all-type
  term interpretation and its truth lemma, and establishing modal
  completeness remain separate construction steps.
\<close>

end
