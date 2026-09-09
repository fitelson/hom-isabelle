theory Bacon_Book_Closed_Universal_Instances
  imports Bacon_Book_Closed_Maximal_Truth Bacon_Book_Conversion_Classes
begin

section \<open>Universal membership entails every closed instance\<close>

text \<open>
  If ∀σF∈M and M is maximal among consistent closed-formula sets,
  then FA∈M for each closed Σ-term A:σ, provided F is closed.
  The source UI axiom and MP supply a derivation; closed-consequence
  closure supplies membership. This is the forward half of the canonical
  quantifier truth lemma (Bacon, p.321). It needs neither a valuation
  nor witness completeness, and does not claim its converse.
\<close>

theorem book_closed_maximal_forall_instance:
  assumes maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and predicate: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
    and argument: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    and universal: "NApp (NLogical (SBAll \<sigma>)) F \<in> M"
  shows "NApp F A \<in> M"
proof -
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    by (rule book_closed_terms_language[OF predicate])
  have al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    by (rule book_closed_terms_language[OF argument])
  have ul: "book_theory_formula \<Sigma> G (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule book_language_App[OF book_all_operator_language fl])
  have instance_language: "book_theory_formula \<Sigma> G (NApp F A)"
    by (rule book_language_App[OF fl al])
  have instance_closed: "named_fv (NApp F A) = {}"
    by (simp only: named_fv.simps book_closed_terms_closed[OF predicate]
        book_closed_terms_closed[OF argument]; simp)
  have universal_derivation: "book_theory_derivable \<Sigma> G M (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule book_theory_derivable.Assumption[OF universal ul])
  have ui: "book_theory_derivable \<Sigma> G M
    (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F A))"
    by (rule book_theory_derivable.UI[OF fl al])
  have instance_derivation: "book_theory_derivable \<Sigma> G M (NApp F A)"
    by (rule book_theory_derivable.MP[OF universal_derivation ui instance_language])
  show ?thesis by (rule book_closed_maximal_derivable_member[
    OF maximal instance_language instance_closed instance_derivation])
qed

end
