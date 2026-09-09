theory Bacon_Book_Classicism_Finite_Witness_Family
  imports Bacon_Book_Classicism_Conditional_Witness
    Bacon_Book_Environment_Development.Bacon_Book_Finite_Witness_Family
begin

section \<open>Finite witness families over the actual changing C background\<close>

text \<open>
  The finite induction follows the verified H construction, but each
  successor uses the new C conditional-witness theorem. Thus the
  consistency predicate at every stage includes C of THAT signature,
  not merely the original C axioms. The syntax and freshness lemmas
  are reused without redefining the witness family.
  Predicates are closed and belong to the original stage language;
  the later iteration must cover predicates involving new names.
\<close>

theorem book_C_consistent_finite_witness_family:
  assumes finite_I: "finite I"
    and rich: "sg_rich G"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Sigma> (\<tau> i)"
    and injective: "inj_on c I"
  shows "book_C_theory_consistent (book_witness_family_signature \<Sigma> \<tau> c I) G
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
  have partial_consistent: "book_C_theory_consistent ?\<Omega> G ?P"
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
  have extended: "book_C_theory_consistent (book_add_constant ?\<Omega> (c i) (\<tau> i)) G
    (insert (book_witness_axiom G (\<tau> i) (F i) (c i)) ?P)"
    by (rule book_C_consistent_conditional_witness[
      OF rich partial_consistent partial_language enlarged_predicate current_closed current_fresh])
  have premise_equation: "S \<union> book_witness_family_axioms G \<tau> F c (insert i I) =
    insert (book_witness_axiom G (\<tau> i) (F i) (c i)) ?P"
    by (simp add: book_witness_family_axioms_insert)
  show ?case using extended
    by (simp only: book_witness_family_signature_insert premise_equation)
qed

end

