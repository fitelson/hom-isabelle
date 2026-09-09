theory Bacon_Book_Classicism_Conditional_Witness
  imports Bacon_Book_Classicism_Fresh_Background
begin

section \<open>One fresh conditional witness preserves consistency over the enlarged C\<close>

theorem book_C_consistent_conditional_witness:
  assumes rich: "sg_rich G" and consistent: "book_C_theory_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and fresh: "c \<notin> \<Sigma> \<sigma>"
  shows "book_C_theory_consistent (book_add_constant \<Sigma> c \<sigma>) G (insert (book_witness_axiom G \<sigma> F c) S)"
proof -
  let ?\<Omega> = "book_add_constant \<Sigma> c \<sigma>"
  let ?Cold = "{A. book_C_proves \<Sigma> G A}"
  let ?Cnew = "{A. book_C_proves ?\<Omega> G A}"
  let ?W = "book_witness_axiom G \<sigma> F c"
  have old_consistent: "book_theory_consistent \<Sigma> G (?Cold \<union> S)"
    using consistent by (simp add: book_C_theory_consistent_def book_C_theory_derivable_def book_theory_consistent_def)
  have old_language: "book_theory_formula \<Sigma> G A" if "A \<in> ?Cold \<union> S" for A
    using that language book_C_proves_language[OF rich] by blast
  have witnessed: "book_theory_consistent ?\<Omega> G (insert ?W (?Cold \<union> S))"
    by (rule book_theory_consistent_conditional_witness[OF rich old_consistent old_language predicate closed fresh])
  have inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> ?\<Omega> \<tau>" by (rule book_add_constant_subset)
  have enlarged_F: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G F (Arr \<sigma> Prop)"
    by (rule book_language_signature_mono[OF predicate inclusion])
  have witness_type: "book_theory_formula ?\<Omega> G ?W"
    by (rule book_witness_axiom_language[OF rich enlarged_F book_add_constant_member])
  show ?thesis
  proof (unfold book_C_theory_consistent_def, rule notI)
    assume contradiction: "book_C_theory_derivable ?\<Omega> G (insert ?W S) (book_bottom G)"
    have proof_new: "book_theory_derivable ?\<Omega> G (?Cnew \<union> insert ?W S) (book_bottom G)"
      using contradiction unfolding book_C_theory_derivable_def .
    have proof_old: "book_theory_derivable ?\<Omega> G (?Cold \<union> insert ?W S) (book_bottom G)"
    proof (rule book_theory_derivable_cut[OF proof_new])
      fix A
      assume member: "A \<in> ?Cnew \<union> insert ?W S"
      show "book_theory_derivable ?\<Omega> G (?Cold \<union> insert ?W S) A"
      proof (cases "book_C_proves ?\<Omega> G A")
        case True
        show ?thesis by (rule book_C_new_constant_theorem_from_old_background[OF rich True])
      next
        case False
        have extra: "A \<in> insert ?W S" using member False by simp
        have typed: "book_theory_formula ?\<Omega> G A"
        proof (cases "A = ?W")
          case True
          show ?thesis by (simp only: True; rule witness_type)
        next
          case False
          have old: "A \<in> S" using extra False by simp
          show ?thesis by (rule book_language_signature_mono[OF language[OF old] inclusion])
        qed
        show ?thesis by (rule book_theory_derivable.Assumption[OF UnI2[OF extra] typed])
      qed
    qed
    have sets: "?Cold \<union> insert ?W S = insert ?W (?Cold \<union> S)" by blast
    show False using witnessed proof_old by (simp only: sets book_theory_consistent_def; blast)
  qed
qed

text \<open>
  The complete C background in Σ[c:σ] is retained. The earlier H
  conditional-witness theorem first applies to CΣ∪S, whose formulas
  use only the old signature. A separate proof recovers every new C
  theorem from that old background, so a contradiction with CΣ[c:σ]
  would already contradict the checked H witness extension.

  This is a genuine one-witness consistency result, not conservativity
  of the witness axiom, not simultaneous Henkin completion, and not
  full modal completeness. The predicate F must be closed and c fresh
  at its declared type. S may be infinite and open.
\<close>

end
