theory Bacon_Book_Lambda_I_Closed_Universal_Instances
  imports Bacon_Book_Lambda_I_Closed_Maximal_Truth Bacon_Book_Lambda_I_Conversion_Classes
begin

section \<open>Universal membership entails every closed instance\<close>

text \<open>
  If ∀σF∈M and M is maximal among λI-consistent closed λI-formula sets,
  then FA∈M for each closed λI term A:σ of Σ, provided F is a closed λI
  predicate.
  The source UI axiom and MP supply a derivation; closed-consequence
  closure supplies membership. This is the forward half of the canonical
  quantifier truth lemma (Bacon, p.321). It needs neither a valuation
  nor witness completeness, and does not claim its converse.
\<close>

theorem book_lambda_I_closed_maximal_forall_instance:
  assumes maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and predicate: "F \<in> book_lambda_I_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
    and argument: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
    and universal: "NApp (NLogical (SBAll \<sigma>)) F \<in> M"
  shows "NApp F A \<in> M"
proof -
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    by (rule book_lambda_I_closed_terms_language[OF predicate])
  have al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    by (rule book_lambda_I_closed_terms_language[OF argument])
  have fr: "book_lambda_I F" by (rule book_lambda_I_closed_terms_relevant[OF predicate])
  have ar: "book_lambda_I A" by (rule book_lambda_I_closed_terms_relevant[OF argument])
  have ul: "book_lambda_I_formula \<Sigma> G (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule conjI[OF book_language_App[OF book_all_operator_language fl]]; simp add: fr)
  have instance_language: "book_lambda_I_formula \<Sigma> G (NApp F A)"
    by (rule conjI[OF book_language_App[OF fl al]]; simp add: fr ar)
  have instance_closed: "named_fv (NApp F A) = {}"
    by (simp only: named_fv.simps book_lambda_I_closed_terms_closed[OF predicate]
        book_lambda_I_closed_terms_closed[OF argument]; simp)
  have universal_derivation: "book_lambda_I_derivable \<Sigma> G M (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule book_lambda_I_derivable.Assumption[OF universal ul])
  have ui: "book_lambda_I_derivable \<Sigma> G M
    (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F A))"
    by (rule book_lambda_I_derivable.UI[OF book_lambda_I_closed_terms_LI[OF predicate] book_lambda_I_closed_terms_LI[OF argument]])
  have instance_derivation: "book_lambda_I_derivable \<Sigma> G M (NApp F A)"
    by (rule book_lambda_I_derivable.MP[OF universal_derivation ui instance_language])
  show ?thesis by (rule book_lambda_I_closed_maximal_derivable_member[
    OF maximal instance_language instance_closed instance_derivation])
qed

end
