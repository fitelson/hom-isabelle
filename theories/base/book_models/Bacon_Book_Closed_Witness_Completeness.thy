theory Bacon_Book_Closed_Witness_Completeness
  imports Bacon_Book_Conditional_Witness
begin

section \<open>Closed predicates with declared constant witnesses\<close>

text \<open>
  For each closed F:σ→t, either ¬∃σF belongs to M or Fc belongs
  to M for some declared constant c:σ. This is the CLOSED-predicate
  version of Bacon's witness completeness (Definition 15.4, p.319),
  strengthened from an arbitrary witness term to a declared constant.

  Representation. ∃σ remains the literal λ-defined operator. The
  predicate below tests only closed predicates; it does not itself
  require every member of M to be closed, make M a global theory,
  or decide all open formulas.
  Constants are witnesses, not semantic domain elements. No model or
  existence of a maximal extension is assumed by the definition.
\<close>

definition book_closed_constant_witness_complete ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_closed_constant_witness_complete \<Sigma> G M \<longleftrightarrow>
    (\<forall>\<sigma> F. book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)
      \<longrightarrow> named_fv F = {} \<longrightarrow>
      (book_not G (NApp (book_exists_const G \<sigma>) F) \<in> M \<or>
        (\<exists>c\<in>\<Sigma> \<sigma>. NApp F (NConst c \<sigma>) \<in> M)))"

section \<open>Conditional axioms and closed maximality give witnesses\<close>

text \<open>
  Suppose M is maximal among consistent closed-formula extensions, and
  it contains W(F,c)=(∃σF)→Fc for some declared c for every closed F.
  Closed negation completeness decides ∃σF. In its positive case MP
  derives Fc from M, and closure under CLOSED consequences places Fc
  in M. In the other case M contains ¬∃σF. Only this closed decision
  and closure are used; no unrestricted open deduction is invoked.
\<close>

theorem book_closed_constant_witness_complete_from_conditionals:
  assumes rich: "sg_rich G"
    and maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and scheme: "\<And>\<sigma> F. book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)
      \<Longrightarrow> named_fv F = {} \<Longrightarrow> \<exists>c\<in>\<Sigma> \<sigma>. book_witness_axiom G \<sigma> F c \<in> M"
  shows "book_closed_constant_witness_complete \<Sigma> G M"
proof (unfold book_closed_constant_witness_complete_def, intro allI impI)
  fix \<sigma> F
  assume predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  let ?E = "NApp (book_exists_const G \<sigma>) F"
  have E_language: "book_theory_formula \<Sigma> G ?E"
    by (rule book_exists_application_language[OF rich predicate])
  have E_closed: "named_fv ?E = {}"
    by (simp only: book_exists_application_fv closed)
  show "book_not G ?E \<in> M \<or> (\<exists>c\<in>\<Sigma> \<sigma>. NApp F (NConst c \<sigma>) \<in> M)"
  proof (cases "?E \<in> M")
    case True
    obtain c where declared: "c \<in> \<Sigma> \<sigma>"
      and conditional_member: "book_witness_axiom G \<sigma> F c \<in> M"
      using scheme[OF predicate closed] by blast
    have witness_constant: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NConst c \<sigma>) \<sigma>"
      by (simp add: book_language_const_iff declared)
    have instance_language: "book_theory_formula \<Sigma> G (NApp F (NConst c \<sigma>))"
      by (rule book_language_App[OF predicate witness_constant])
    have instance_closed: "named_fv (NApp F (NConst c \<sigma>)) = {}"
      by (simp only: named_fv.simps closed Un_empty_right)
    have conditional_language: "book_theory_formula \<Sigma> G (book_witness_axiom G \<sigma> F c)"
      by (rule book_witness_axiom_language[OF rich predicate declared])
    have existential: "book_theory_derivable \<Sigma> G M ?E"
      by (rule book_theory_derivable.Assumption[OF True E_language])
    have conditional: "book_theory_derivable \<Sigma> G M (book_witness_axiom G \<sigma> F c)"
      by (rule book_theory_derivable.Assumption[OF conditional_member conditional_language])
    have implication: "book_theory_derivable \<Sigma> G M (book_imp ?E (NApp F (NConst c \<sigma>)))"
      using conditional by (simp only: book_witness_axiom_def)
    have instance_derivation: "book_theory_derivable \<Sigma> G M (NApp F (NConst c \<sigma>))"
      by (rule book_theory_derivable.MP[OF existential implication instance_language])
    have instance_member: "NApp F (NConst c \<sigma>) \<in> M"
      by (rule book_closed_maximal_derivable_member[OF maximal instance_language instance_closed instance_derivation])
    show ?thesis by (rule disjI2, rule bexI[where x=c], rule instance_member, rule declared)
  next
    case False
    have decision: "?E \<in> M \<or> book_not G ?E \<in> M"
      by (rule book_closed_maximal_decides[OF rich maximal E_language E_closed])
    have negative: "book_not G ?E \<in> M" using decision False by blast
    show ?thesis by (rule disjI1[OF negative])
  qed
qed

end
