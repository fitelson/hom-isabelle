theory Bacon_Book_Conjunction_Background_Retraction
  imports Bacon_Book_Primitive_Conjunction_Axiom_Theory Bacon_Book_Remove_Constant
begin

section \<open>Deleting an old-name key leaves the conjunction tag available\<close>

text \<open>
  Put Γ=target(Σ) and Ω=Γ without Inl(c):σ. The distinguished
  Inr(⋆):t→t→t remains declared. Retraction into Ω therefore fixes
  that tag, while it may replace occurrences of Inl(c):σ in operands.
  Source role: nonlogical substitution in Definition 5.2, p.99, applied
  to the fixed-background encoding of §5.2, p.104.

  Retraction sends every Π∧ instance to another Π∧ instance in Γ;
  it need not fix an instance literally. No global freshness condition
  on the infinite Π∧ is required for this syntactic membership statement.
  Retraction of an actual proof uses its separate finite support.
\<close>

lemma book_conj_remove_keeps_tag:
  "Inr () \<in> book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma> book_conj_type"
  by (cases "book_conj_type = \<sigma>") (simp_all add: book_remove_constant_def book_conj_target_tag_iff)

lemma book_conj_retract_target_apply:
  assumes tag: "Inr () \<in> \<Omega> book_conj_type"
  shows "named_retract \<Omega> v (book_conj_target_apply P Q) =
    book_conj_target_apply (named_retract \<Omega> v P) (named_retract \<Omega> v Q)"
  by (simp only: book_conj_target_apply_def named_retract.simps tag if_True)

lemma book_conj_background_retract_operand:
  assumes stock: "\<And>\<rho>. G (v \<rho>) = \<rho>"
    and language: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G P"
  shows "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G
    (named_retract (book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>) v P)"
proof -
  let ?\<Omega> = "book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>"
  have retracted: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G (named_retract ?\<Omega> v P) Prop"
    by (rule book_retract_language[OF language stock])
  show ?thesis by (rule book_language_signature_mono[OF retracted]; rule book_remove_constant_subset)
qed

theorem book_conj_background_retract_axiom:
  assumes stock: "\<And>\<rho>. G (v \<rho>) = \<rho>" and member: "A \<in> book_conj_axioms \<Sigma> G"
  shows "named_retract (book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>) v A
    \<in> book_conj_axioms \<Sigma> G"
  using member
proof (induction rule: book_conj_axioms.induct)
  case (Intro P Q)
  let ?\<Omega> = "book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>"
  have tag: "Inr () \<in> ?\<Omega> book_conj_type" by (rule book_conj_remove_keeps_tag)
  have pl: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v P)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Intro.hyps(1)])
  have ql: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v Q)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Intro.hyps(2)])
  show ?case by (simp only: book_retract_imp book_conj_retract_target_apply[where \<Omega>="?\<Omega>" and v=v, OF tag];
      rule book_conj_axioms.Intro[OF pl ql])
next
  case (Left P Q)
  let ?\<Omega> = "book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>"
  have tag: "Inr () \<in> ?\<Omega> book_conj_type" by (rule book_conj_remove_keeps_tag)
  have pl: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v P)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Left.hyps(1)])
  have ql: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v Q)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Left.hyps(2)])
  show ?case by (simp only: book_retract_imp book_conj_retract_target_apply[where \<Omega>="?\<Omega>" and v=v, OF tag];
      rule book_conj_axioms.Left[OF pl ql])
next
  case (Right P Q)
  let ?\<Omega> = "book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>"
  have tag: "Inr () \<in> ?\<Omega> book_conj_type" by (rule book_conj_remove_keeps_tag)
  have pl: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v P)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Right.hyps(1)])
  have ql: "book_printed_theory_formula (book_conj_target_signature \<Sigma>) G (named_retract ?\<Omega> v Q)"
    by (rule book_conj_background_retract_operand[where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>,
      OF stock Right.hyps(2)])
  show ?case by (simp only: book_retract_imp book_conj_retract_target_apply[where \<Omega>="?\<Omega>" and v=v, OF tag];
      rule book_conj_axioms.Right[OF pl ql])
qed

corollary book_conj_background_retract_subset:
  assumes stock: "\<And>\<rho>. G (v \<rho>) = \<rho>"
  shows "image (named_retract (book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>) v)
    (book_conj_axioms \<Sigma> G) \<subseteq> book_conj_axioms \<Sigma> G"
proof
  fix B
  assume member: "B \<in> image (named_retract
    (book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>) v) (book_conj_axioms \<Sigma> G)"
  obtain A where source: "A \<in> book_conj_axioms \<Sigma> G"
    and shape: "B = named_retract (book_remove_constant (book_conj_target_signature \<Sigma>) (Inl c) \<sigma>) v A"
    using member by blast
  show "B \<in> book_conj_axioms \<Sigma> G"
    by (simp only: shape; rule book_conj_background_retract_axiom[
      where G=G and v=v and \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>, OF stock source])
qed

end
