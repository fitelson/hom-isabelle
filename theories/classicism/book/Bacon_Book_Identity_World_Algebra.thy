theory Bacon_Book_Identity_World_Algebra
  imports Bacon_Book_H_Identity_Certificates
begin

section \<open>Identity in a closed C world is an application congruence\<close>

locale book_C_identity_world =
  fixes \<Sigma> :: "'c ssignature" and G :: sgcontext and w :: "'c book_named_term set"
  assumes rich: "sg_rich G" and maximal: "book_C_closed_maximal_extension \<Sigma> G {} w"
begin

lemma apply_H:
  assumes theorem_H: "book_H \<Sigma> G (book_imp A B)" and member: "A \<in> w" and closed: "named_fv B = {}"
  shows "B \<in> w"
  by (rule book_C_closed_world_apply_theorem[OF rich book_C_closed_maximal_is_world[OF maximal]
    book_C_proves.H[OF theorem_H] member closed])

lemma identity_refl:
  assumes member: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "book_leibniz G \<sigma> A A \<in> w"
proof -
  have original: "book_C_proves \<Sigma> G (book_leibniz G \<sigma> A A)"
    by (rule book_C_proves.H[OF book_H_leibniz_reflexive[OF rich book_closed_terms_language[OF member]]])
  have closed: "named_fv (book_leibniz G \<sigma> A A) = {}"
    by (simp only: book_leibniz_fv book_closed_terms_closed[OF member] Un_empty)
  show ?thesis by (rule book_C_closed_maximal_original_theorem[OF rich maximal original closed])
qed

lemma identity_sym:
  assumes am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and identity: "book_leibniz G \<sigma> A B \<in> w"
  shows "book_leibniz G \<sigma> B A \<in> w"
proof -
  have closed: "named_fv (book_leibniz G \<sigma> B A) = {}"
    by (simp only: book_leibniz_fv book_closed_terms_closed[OF am] book_closed_terms_closed[OF bm] Un_empty)
  show ?thesis by (rule apply_H[OF book_H_identity_symmetry[OF rich book_closed_terms_language[OF am]
    book_closed_terms_language[OF bm]] identity closed])
qed

lemma identity_trans:
  assumes am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and cm: "C \<in> book_closed_terms \<Sigma> G \<sigma>"
    and first: "book_leibniz G \<sigma> A B \<in> w" and second: "book_leibniz G \<sigma> B C \<in> w"
  shows "book_leibniz G \<sigma> A C \<in> w"
proof -
  let ?F = "book_leibniz G \<sigma> B C"
  let ?R = "book_leibniz G \<sigma> A C"
  have tail_closed: "named_fv (book_imp ?F ?R) = {}"
    by (simp only: book_imp_fv book_leibniz_fv book_closed_terms_closed[OF am]
      book_closed_terms_closed[OF bm] book_closed_terms_closed[OF cm] Un_empty)
  have conditional: "book_imp ?F ?R \<in> w"
    by (rule apply_H[OF book_H_identity_transitivity[OF rich book_closed_terms_language[OF am]
      book_closed_terms_language[OF bm] book_closed_terms_language[OF cm]] first tail_closed])
  have fl: "book_theory_formula \<Sigma> G ?F" by (rule book_leibniz_language[OF rich
    book_closed_terms_language[OF bm] book_closed_terms_language[OF cm]])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_leibniz_language[OF rich
    book_closed_terms_language[OF am] book_closed_terms_language[OF cm]])
  have derivation: "book_C_theory_derivable \<Sigma> G w ?R"
    by (rule book_C_theory_MP[OF book_C_theory_assume[OF second fl]
      book_C_theory_assume[OF conditional book_imp_language[OF fl rl]] rl])
  have closed: "named_fv ?R = {}"
    by (simp only: book_leibniz_fv book_closed_terms_closed[OF am] book_closed_terms_closed[OF cm] Un_empty)
  show ?thesis by (rule book_C_closed_maximal_consequence[OF rich maximal derivation closed])
qed

lemma identity_application:
  assumes fm: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)" and hm: "H \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and heads: "book_leibniz G (Arr \<sigma> \<tau>) F H \<in> w" and arguments: "book_leibniz G \<sigma> A B \<in> w"
  shows "book_leibniz G \<tau> (NApp F A) (NApp H B) \<in> w"
proof -
  let ?I = "book_leibniz G \<sigma> A B"
  let ?R = "book_leibniz G \<tau> (NApp F A) (NApp H B)"
  have tail_closed: "named_fv (book_imp ?I ?R) = {}"
    by (simp only: book_imp_fv book_leibniz_fv named_fv.simps book_closed_terms_closed[OF fm]
      book_closed_terms_closed[OF hm] book_closed_terms_closed[OF am] book_closed_terms_closed[OF bm] Un_empty)
  have conditional: "book_imp ?I ?R \<in> w"
    by (rule apply_H[OF book_H_identity_application[OF rich book_closed_terms_language[OF fm]
      book_closed_terms_language[OF hm] book_closed_terms_language[OF am] book_closed_terms_language[OF bm]] heads tail_closed])
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_leibniz_language[OF rich
    book_closed_terms_language[OF am] book_closed_terms_language[OF bm]])
  have rl: "book_theory_formula \<Sigma> G ?R" by (rule book_leibniz_language[OF rich
    book_language_App[OF book_closed_terms_language[OF fm] book_closed_terms_language[OF am]]
    book_language_App[OF book_closed_terms_language[OF hm] book_closed_terms_language[OF bm]]])
  have derivation: "book_C_theory_derivable \<Sigma> G w ?R"
    by (rule book_C_theory_MP[OF book_C_theory_assume[OF arguments il]
      book_C_theory_assume[OF conditional book_imp_language[OF il rl]] rl])
  have closed: "named_fv ?R = {}"
    by (simp only: book_leibniz_fv named_fv.simps book_closed_terms_closed[OF fm]
      book_closed_terms_closed[OF hm] book_closed_terms_closed[OF am] book_closed_terms_closed[OF bm] Un_empty)
  show ?thesis by (rule book_C_closed_maximal_consequence[OF rich maximal derivation closed])
qed

end

text \<open>
  This algebra uses membership of literal Leibniz identities in w.
  Reflexivity comes from an original H theorem; symmetry, transitivity
  and congruence use H implications and ordinary C-background consequence.
  The earlier book_closed_terms set is reused only as typed closed syntax.
  No conversion-class equality, semantic identity axiom or Functionality
  is used to define or prove these world-identity laws.
\<close>

end
