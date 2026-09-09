theory Bacon_Source_BBK_Vector_Congruence
  imports Bacon_Source_BBK_Interface Bacon_Source_Vector_Syntax
begin

section \<open>Application congruence along a finite typed vector\<close>

text \<open>
  If ⟦F⟧ᵍ = ⟦H⟧ʰ and corresponding arguments have equal denotations,
  then ⟦F A₁…Aₙ⟧ᵍ = ⟦H B₁…Bₙ⟧ʰ. This is repeated application
  of Bacon–Dorr Definition 3.1(ii.b), including the empty vector and
  mixed argument types.

  Status: a theorem of the weaker finite-frame structure. No renaming,
  substitution, Functionality, or logical truth principle is used. It is
  an ingredient in deriving rather than assuming renaming coherence.
\<close>

context paper_db_bbk_structure
begin

lemma paper_db_application_language:
  assumes F: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
  shows "sterm_in_language paper_logical_type signature \<Gamma> (SApp F A) \<tau>"
  using F A unfolding sterm_in_language_def by (auto intro: has_stype.App)

theorem paper_db_vector_application_cong:
  assumes F: "sterm_in_language paper_logical_type signature \<Gamma> F (sarrow_type \<sigma>s \<tau>)"
    and H: "sterm_in_language paper_logical_type signature \<Delta> H (sarrow_type \<sigma>s \<tau>)"
    and As: "list_all2 (\<lambda>A \<sigma>. sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>) As \<sigma>s"
    and Bs: "list_all2 (\<lambda>B \<sigma>. sterm_in_language paper_logical_type signature \<Delta> B \<sigma>) Bs \<sigma>s"
    and env_g: "pbbk_env_typed domain \<Gamma> g" and env_h: "pbbk_env_typed domain \<Delta> h"
    and heads: "denote g F = denote h H"
    and arguments: "list_all2 (\<lambda>A B. denote g A = denote h B) As Bs"
  shows "denote g (sapp_vec F As) = denote h (sapp_vec H Bs)"
  using F H As Bs heads arguments
proof (induction \<sigma>s arbitrary: F H As Bs)
  case Nil
  have empty: "As = []" "Bs = []" using Nil.prems(3,4) by (cases As; cases Bs; simp_all)+
  show ?case using Nil.prems(5) by (simp only: empty sapp_vec.simps)
next
  case (Cons \<sigma> \<sigma>s)
  obtain A As' where left: "As = A # As'"
    and A: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and tail_As: "list_all2 (\<lambda>A \<rho>. sterm_in_language paper_logical_type signature \<Gamma> A \<rho>) As' \<sigma>s"
    using Cons.prems(3) by (cases As) auto
  obtain B Bs' where right: "Bs = B # Bs'"
    and B: "sterm_in_language paper_logical_type signature \<Delta> B \<sigma>"
    and tail_Bs: "list_all2 (\<lambda>B \<rho>. sterm_in_language paper_logical_type signature \<Delta> B \<rho>) Bs' \<sigma>s"
    using Cons.prems(4) by (cases Bs) auto
  have arg_eq: "denote g A = denote h B"
    and tail_eq: "list_all2 (\<lambda>A B. denote g A = denote h B) As' Bs'"
    using Cons.prems(6) by (simp_all add: left right)
  have ft: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> (sarrow_type \<sigma>s \<tau>))"
    using Cons.prems(1) by (simp only: sarrow_type.simps)
  have ht: "sterm_in_language paper_logical_type signature \<Delta> H (Arr \<sigma> (sarrow_type \<sigma>s \<tau>))"
    using Cons.prems(2) by (simp only: sarrow_type.simps)
  have next_eq: "denote g (SApp F A) = denote h (SApp H B)"
    by (rule denote_application_cong[OF ft A ht B env_g env_h Cons.prems(5) arg_eq])
  have result: "denote g (sapp_vec (SApp F A) As') = denote h (sapp_vec (SApp H B) Bs')"
    by (rule Cons.IH[OF paper_db_application_language[OF ft A]
      paper_db_application_language[OF ht B] tail_As tail_Bs next_eq tail_eq])
  show ?case using result by (simp only: left right sapp_vec.simps)
qed

end

end
