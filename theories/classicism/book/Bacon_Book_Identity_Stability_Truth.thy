theory Bacon_Book_Identity_Stability_Truth
  imports Bacon_Book_Implication_Leibniz_Congruence
begin

section \<open>Identity of arguments preserves the proposition expressed by identity\<close>

context book_full_minimal_model
begin

lemma book_identity_argument_leibniz_cong:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and al: "book_in_language book_minimal_logical_type UNIV signature stock A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B \<sigma>"
    and equivalent: "book_leibniz_equiv domain app V \<sigma> (denote g A) (denote g B)"
  shows "book_leibniz_equiv domain app V Prop
    (denote g (book_leibniz stock \<sigma> A A)) (denote g (book_leibniz stock \<sigma> A B))"
proof -
  let ?F = "NApp (book_leibniz_const stock \<sigma>) A"
  have fl: "book_in_language book_minimal_logical_type UNIV signature stock ?F (Arr \<sigma> Prop)"
    by (rule book_language_App[OF book_leibniz_const_language[OF rich] al])
  have fm: "denote g ?F \<in> domain (Arr \<sigma> Prop)" by (rule denote_type[OF UNIV_I fl typed])
  have applied: "book_leibniz_equiv domain app V Prop
    (app \<sigma> Prop (denote g ?F) (denote g A)) (app \<sigma> Prop (denote g ?F) (denote g B))"
    by (rule book_leibniz_argument_cong[OF rich typed equivalent fm])
  have aa: "denote g (book_leibniz stock \<sigma> A A) = app \<sigma> Prop (denote g ?F) (denote g A)"
    unfolding book_leibniz_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fl al typed])
  have ab: "denote g (book_leibniz stock \<sigma> A B) = app \<sigma> Prop (denote g ?F) (denote g B)"
    unfolding book_leibniz_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fl bl typed])
  show ?thesis by (simp only: aa ab; rule applied)
qed

theorem book_identity_stability_conditional_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and al: "book_in_language book_minimal_logical_type UNIV signature stock A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B \<sigma>"
    and necessary_refl: "V (denote g (book_box stock (book_leibniz stock \<sigma> A A)))"
    and identity: "V (denote g (book_leibniz stock \<sigma> A B))"
  shows "V (denote g (book_box stock (book_leibniz stock \<sigma> A B)))"
proof -
  have aal: "book_theory_formula signature stock (book_leibniz stock \<sigma> A A)"
    by (rule book_leibniz_language[OF rich al al])
  have abl: "book_theory_formula signature stock (book_leibniz stock \<sigma> A B)"
    by (rule book_leibniz_language[OF rich al bl])
  have equivalent: "book_leibniz_equiv domain app V \<sigma> (denote g A) (denote g B)"
    using identity by (simp only: book_leibniz_truth[OF rich typed al bl])
  have propositions: "book_leibniz_equiv domain app V Prop
    (denote g (book_leibniz stock \<sigma> A A)) (denote g (book_leibniz stock \<sigma> A B))"
    by (rule book_identity_argument_leibniz_cong[OF rich typed al bl equivalent])
  have aa_top: "book_leibniz_equiv domain app V Prop
    (denote g (book_leibniz stock \<sigma> A A)) (denote g (book_top stock))"
    using necessary_refl by (simp only: book_box_truth[OF rich typed aal])
  have ab_top: "book_leibniz_equiv domain app V Prop
    (denote g (book_leibniz stock \<sigma> A B)) (denote g (book_top stock))"
    by (rule book_leibniz_trans[OF book_leibniz_sym[OF propositions] aa_top])
  show ?thesis by (simp only: book_box_truth[OF rich typed abl]; rule ab_top)
qed

end

text \<open>
  In a full minimal H model, A≈σB implies that the propositions A=σA
  and A=σB are themselves Leibniz-equivalent: apply the typed predicate
  (=σ)A to the equivalent arguments. If A=σA is equivalent to ⊤, so
  is A=σB. The premise □(A=σA) is retained explicitly. We do not assume
  identity of merely true propositions or necessitate a local identity.
\<close>

end
