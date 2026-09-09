theory Bacon_Book_Classicism_Boxed_PE
  imports Bacon_Book_Boxed_PE_Truth
begin

section \<open>Discharging the three identities in the native C calculus\<close>

theorem book_H_boxed_PE_from_identities:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_theory_derivable \<Sigma> G (book_boxed_PE_premises G P Q)
    (book_imp (book_box G (book_iff G P Q)) (book_leibniz G Prop P Q))"
proof -
  let ?S = "book_boxed_PE_premises G P Q"
  let ?B = "book_box G (book_iff G P Q)"
  let ?I = "book_leibniz G Prop P Q"
  have sl: "\<And>A. A \<in> ?S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    by (rule book_boxed_PE_premises_language[OF rich pl ql]; assumption)
  have bl: "book_theory_formula \<Sigma> G ?B" by (rule book_box_language[OF rich book_iff_language[OF rich pl ql]])
  have il: "book_theory_formula \<Sigma> G ?I" by (rule book_leibniz_language[OF rich pl ql])
  have consequence: "book_canonical_consequence \<Sigma> G ?S (book_imp ?B ?I)"
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k"
      and all_valid: "\<forall>A\<in>?S. book_formula_valid D G J V A"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp ?B ?I)"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have identities: "V (J g A)" if "A \<in> ?S" for A
        using all_valid typed that unfolding book_formula_valid_def by blast
      have calculation: "V (J g ?B) \<longrightarrow> V (J g ?I)"
        by (intro impI; rule M.book_boxed_PE_conditional_truth[OF rich typed pl ql identities]; assumption)
      show "V (J g (book_imp ?B ?I))" by (simp only: M.book_imp_truth[OF typed bl il]; rule calculation)
    qed
  qed
  show ?thesis by (rule book_canonical_completeness[OF rich sl book_imp_language[OF bl il] consequence])
qed

theorem book_C_boxed_propositional_equivalence:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_C_proves \<Sigma> G (book_imp (book_box G (book_iff G P Q)) (book_leibniz G Prop P Q))"
  by (rule book_C_contains_theory_derivation[OF rich book_H_boxed_PE_from_identities[OF rich pl ql]];
    rule book_C_boxed_PE_premises[OF rich pl ql]; assumption)

theorem book_C_world_boxed_propositional_equivalence:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and pl: "book_theory_formula (fst w) G P" and ql: "book_theory_formula (fst w) G Q"
    and pc: "named_fv P = {}" and qc: "named_fv Q = {}"
    and boxed: "book_box G (book_iff G P Q) \<in> snd w"
  shows "book_leibniz G Prop P Q \<in> snd w"
proof -
  have old_world: "snd w \<in> book_C_closed_worlds (fst w) G"
    by (rule book_C_closed_maximal_is_world[OF book_C_canonical_world_data(4)[OF world]])
  have closed: "named_fv (book_leibniz G Prop P Q) = {}" by (simp only: book_leibniz_fv pc qc Un_empty)
  show ?thesis by (rule book_C_closed_world_apply_theorem[OF rich old_world
    book_C_boxed_propositional_equivalence[OF rich pl ql] boxed closed])
qed

text \<open>
  C ⊢ □(P↔Q) → (P=ₜQ), for well-typed P,Q, including open formulas.
  H consequence from the three Boolean identities is first established.
  Each identity is then discharged as an original C theorem, using the
  already proved closure of C under the native H theory calculus.
  The world corollary applies this original implication by ordinary MP.
  No C completeness, proposition separation, or local Necessitation is
  used. This is the propositional identity step in Proposition 18.4.
\<close>

end
