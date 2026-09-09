theory Bacon_Book_Full_Classicism_Structural
  imports Bacon_Book_Full_Classicism_Necessitation
    Bacon_Book_Environment_Development.Bacon_Book_Universal_Closure
begin

section \<open>Derived operations on original full-C theorems\<close>

theorem book_full_C_generalize:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
  shows "book_full_C_proves \<Sigma> G (book_all G n A)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_full_C_proves_language[OF rich derivation])
  have base: "book_theory_derivable \<Sigma> G {A} A" by (rule book_theory_derivable.Assumption; (simp | rule al))
  have quantified: "book_theory_derivable \<Sigma> G {A} (book_all G n A)" by (rule book_theory_generalize[OF rich base])
  show ?thesis by (rule book_full_C_contains_theory_derivation[OF rich quantified]; simp add: derivation)
qed

theorem book_full_C_all_elim:
  assumes rich: "sg_rich G" and quantified: "book_full_C_proves \<Sigma> G (book_all G n A)"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_proves \<Sigma> G A"
proof -
  have base: "book_theory_derivable \<Sigma> G {book_all G n A} (book_all G n A)"
    by (rule book_theory_derivable.Assumption; (simp | rule book_all_language[OF al]))
  have body: "book_theory_derivable \<Sigma> G {book_all G n A} A" by (rule book_theory_all_elim_variable[OF base al])
  show ?thesis by (rule book_full_C_contains_theory_derivation[OF rich body]; simp add: quantified)
qed

theorem book_full_C_variable_substitution:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B (G n)"
    and free: "named_free_for B n A"
  shows "book_full_C_proves \<Sigma> G (named_subst n B A)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_full_C_proves_language[OF rich derivation])
  have base: "book_theory_derivable \<Sigma> G {A} A" by (rule book_theory_derivable.Assumption; (simp | rule al))
  have substituted: "book_theory_derivable \<Sigma> G {A} (named_subst n B A)"
    by (rule book_theory_variable_substitution[OF rich base bl free])
  show ?thesis by (rule book_full_C_contains_theory_derivation[OF rich substituted]; simp add: derivation)
qed

theorem book_full_C_MF_body:
  assumes rich: "sg_rich G"
  shows "book_full_C_proves \<Sigma> G (book_MF_body G \<sigma> \<tau>)"
proof -
  have body: "book_theory_formula \<Sigma> G (book_MF_body G \<sigma> \<tau>)" by (rule book_MF_body_language[OF rich])
  have first: "book_full_C_proves \<Sigma> G
    (book_all G (book_MF_left G \<sigma> \<tau>) (book_all G (book_MF_right G \<sigma> \<tau>) (book_MF_body G \<sigma> \<tau>)))"
    by (simp only: book_MF_axiom_def[symmetric]; rule book_full_C_proves.MF)
  have second: "book_full_C_proves \<Sigma> G (book_all G (book_MF_right G \<sigma> \<tau>) (book_MF_body G \<sigma> \<tau>))"
    by (rule book_full_C_all_elim[OF rich first book_all_language[OF body]])
  show ?thesis by (rule book_full_C_all_elim[OF rich second body])
qed

text \<open>
  Generalization, elimination of a universal binder with its own
  variable, and capture-guarded term substitution are derived from H
  theory operations over an already proved full-C theorem. These are
  operations on original theorems, not a new local-assumption calculus.
  Removing the two outer binders of MF yields its open body at the
  selected typed variables; arbitrary term instances require the stated
  free-for provisos, not silent capture-prone textual substitution.
\<close>

end
