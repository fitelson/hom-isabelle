theory Bacon_Book_Henkin_Closed_Terms
  imports Bacon_Book_Henkin_Full_Signature
begin

section \<open>The expanded language has a closed term of every type\<close>

text \<open>
  For each σ, the closed predicate λxσ.⊥ belongs to the initial
  expanded language. Stage one therefore declares its witness name
  Witness(0,σ,λx.⊥). That declared constant is a closed term of type σ
  in the full signature.

  Source role: nonempty canonical typed domains in the term-quotient
  construction discussed on pp.320–321. The name is allocated even for
  this false predicate: its conditional witness premise does NOT assert
  that the predicate is true. This is syntactic inhabitation of the
  expanded language, not a model or a semantic nonemptiness assumption.
  No consistency premise or old constant of type σ is required.
\<close>

theorem book_henkin_full_closed_term_exists:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<exists>A :: ('c book_henkin_name) book_named_term.
    book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G A \<sigma> \<and> named_fv A = {}"
proof -
  let ?n = "named_chart_fresh G [] \<sigma>"
  let ?F = "NLam ?n (book_bottom G) :: ('c book_henkin_name) book_named_term"
  have ntype: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have bottom_language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G 0) G (book_bottom G) Prop"
    by (rule book_bottom_language[OF rich])
  have lambda_language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G 0) G ?F (Arr (G ?n) Prop)"
    by (rule book_language_Lam[OF bottom_language])
  have predicate: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G 0) G ?F (Arr \<sigma> Prop)"
    using lambda_language by (simp only: ntype)
  have closed: "named_fv ?F = {}" by (simp add: book_bottom_closed)
  have stage_declared: "BookWitness 0 \<sigma> ?F \<in> book_henkin_signature \<Sigma> G (Suc 0) \<sigma>"
    by (rule book_henkin_signature_witness[OF closed predicate])
  have declared: "BookWitness 0 \<sigma> ?F \<in> book_henkin_full_signature \<Sigma> G \<sigma>"
    by (rule subsetD[OF book_henkin_stage_in_full stage_declared])
  have term_language: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G (NConst (BookWitness 0 \<sigma> ?F) \<sigma>) \<sigma>"
    using declared by (simp add: book_language_const_iff)
  show ?thesis by (rule exI[where x="NConst (BookWitness 0 \<sigma> ?F) \<sigma>"],
    rule conjI[OF term_language]; simp)
qed

end
