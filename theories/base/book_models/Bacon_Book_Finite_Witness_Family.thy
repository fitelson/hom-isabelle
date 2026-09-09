theory Bacon_Book_Finite_Witness_Family
  imports Bacon_Book_Witness_Family_Syntax
begin

section \<open>Freshness in a partial witness signature\<close>

lemma book_witness_family_next_fresh:
  assumes old_fresh: "c i \<notin> \<Sigma> (\<tau> i)"
    and outside: "i \<notin> I" and injective: "inj_on c (insert i I)"
  shows "c i \<notin> book_witness_family_signature \<Sigma> \<tau> c I (\<tau> i)"
proof
  assume member: "c i \<in> book_witness_family_signature \<Sigma> \<tau> c I (\<tau> i)"
  have in_image: "c i \<in> image c {j\<in>I. \<tau> j = \<tau> i}"
    using member old_fresh by (auto simp: book_witness_family_signature_def)
  obtain j where index: "j \<in> I" and same_name: "c j = c i"
    using in_image by auto
  have j_member: "j \<in> insert i I" using index by simp
  have i_member: "i \<in> insert i I" by (rule insertI1)
  have equality: "j = i" by (rule inj_onD[OF injective same_name j_member i_member])
  show False using outside index equality by simp
qed

section \<open>Finite conditional witness families preserve consistency\<close>

text \<open>
  Let I be finite. Each closed Fᵢ:τᵢ→t belongs to the OLD signature Σ;
  each cᵢ is fresh at τᵢ, and the names cᵢ are distinct on I. If S is
  a consistent set of formulas of Σ, then S∪W[I] is consistent in Σ[I].

  Induction adjoins one conditional witness to the preceding partial
  signature. Injectivity makes its name fresh there; signature
  monotonicity supplies the old predicate and premise language guards.
  The input S may be open or infinite. This theorem is FINITE-family
  consistency only: no enumeration, infinite-family limit, witness
  completeness, model, or H premise is used.
\<close>

theorem book_theory_consistent_finite_witness_family:
  assumes finite_I: "finite I"
    and rich: "sg_rich G"
    and consistent: "book_theory_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Sigma> (\<tau> i)"
    and injective: "inj_on c I"
  shows "book_theory_consistent (book_witness_family_signature \<Sigma> \<tau> c I) G
    (S \<union> book_witness_family_axioms G \<tau> F c I)"
  using finite_I predicates closed fresh injective
proof (induction rule: finite_induct)
  case empty
  show ?case using consistent
    by (simp only: book_witness_family_signature_empty book_witness_family_axioms_empty Un_empty_right)
next
  case (insert i I)
  let ?\<Omega> = "book_witness_family_signature \<Sigma> \<tau> c I"
  let ?P = "S \<union> book_witness_family_axioms G \<tau> F c I"
  have i_member: "i \<in> insert i I" by (rule insertI1)
  have tail_predicates: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F j) (Arr (\<tau> j) Prop)"
    if "j \<in> I" for j
    by (rule insert.prems(1), rule insertI2[OF that])
  have tail_closed: "named_fv (F j) = {}" if "j \<in> I" for j
    by (rule insert.prems(2), rule insertI2[OF that])
  have tail_fresh: "c j \<notin> \<Sigma> (\<tau> j)" if "j \<in> I" for j
    by (rule insert.prems(3), rule insertI2[OF that])
  have tail_injective: "inj_on c I"
    by (rule inj_on_subset[OF insert.prems(4) subset_insertI])
  have partial_consistent: "book_theory_consistent ?\<Omega> G ?P"
    by (rule insert.IH[OF tail_predicates tail_closed tail_fresh tail_injective])
  have partial_language: "book_theory_formula ?\<Omega> G A" if "A \<in> ?P" for A
    by (rule book_witness_family_premises_language[OF rich language tail_predicates that])
  have old_predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    by (rule insert.prems(1)[OF i_member])
  have enlarged_predicate: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G (F i) (Arr (\<tau> i) Prop)"
    by (rule book_language_signature_mono[OF old_predicate]; rule book_witness_family_signature_inclusion)
  have current_closed: "named_fv (F i) = {}" by (rule insert.prems(2)[OF i_member])
  have current_fresh: "c i \<notin> ?\<Omega> (\<tau> i)"
    by (rule book_witness_family_next_fresh[
      where \<Sigma>=\<Sigma> and \<tau>=\<tau> and c=c and i=i and I=I,
      OF insert.prems(3)[OF i_member] insert.hyps(2) insert.prems(4)])
  have extended: "book_theory_consistent (book_add_constant ?\<Omega> (c i) (\<tau> i)) G
    (insert (book_witness_axiom G (\<tau> i) (F i) (c i)) ?P)"
    by (rule book_theory_consistent_conditional_witness[
      OF rich partial_consistent partial_language enlarged_predicate current_closed current_fresh])
  have premise_equation: "S \<union> book_witness_family_axioms G \<tau> F c (insert i I) =
    insert (book_witness_axiom G (\<tau> i) (F i) (c i)) ?P"
    by (simp add: book_witness_family_axioms_insert)
  show ?case using extended
    by (simp only: book_witness_family_signature_insert premise_equation)
qed

end
