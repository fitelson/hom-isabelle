theory Bacon_Book_Theory_Constant_Substitution
  imports Bacon_Book_Remove_Constant Bacon_Book_Constant_Substitution_Abstraction
    Bacon_Book_Theory_Variable_Substitution
begin

section \<open>Single nonlogical-constant substitution in an axiom-generated theorem\<close>

text \<open>
  If ⊢ A and B:σ is free for the nonlogical constant c:σ in A,
  then ⊢ A[B/cσ]. First replace c by a typed variable fresh for
  the entire proof and for B, using retraction. Next apply the derived
  free-variable substitution rule. The fresh-marker equations identify
  the result with literal single-pass constant substitution.

  Source: the nonlogical-constant part of Definition 5.2, p.99, and
  the proof-transformation discussion on p.102. Every Gen and β/η
  condition is discharged by the finite proof-support argument; no
  substitution constructor is added. The empty premise set matters:
  an arbitrary theory need not be closed under replacing its constants.

  This is a single-constant result. The later simultaneous-substitution
  leaf supplies the additional fresh-variable decomposition needed when
  payloads mention other replaced names; Bacon_Book_Logic then proves
  the least-theory/least-logic identification.
\<close>

theorem book_theory_constant_substitution:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G {} A"
    and replacement: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    and free_for: "book_const_free_for B c \<sigma> A"
  shows "book_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> B A)"
proof -
  obtain x where typed: "G x = \<sigma>" and fresh: "x \<notin> named_vars A \<union> named_vars B"
    and abstracted: "book_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> (NVar x) A)"
    using book_theory_fresh_constant_variable[where c=c and \<sigma>=\<sigma> and F="named_vars B",
      OF rich derivation named_vars_finite] by (elim exE conjE)
  have fresh_A: "x \<notin> named_vars A" using fresh by blast
  have replacement_type: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G x)"
    by (simp only: typed; rule replacement)
  have permitted: "named_free_for B x (book_const_subst c \<sigma> (NVar x) A)"
    by (rule book_const_abstract_free_for[OF fresh_A free_for])
  have instantiated: "book_theory_derivable \<Sigma> G {}
    (named_subst x B (book_const_subst c \<sigma> (NVar x) A))"
    by (rule book_theory_variable_substitution[OF rich abstracted replacement_type permitted])
  show ?thesis using instantiated by (simp only: book_const_abstract_instantiate[OF fresh_A])
qed

end
