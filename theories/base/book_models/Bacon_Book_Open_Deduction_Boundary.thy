theory Bacon_Book_Open_Deduction_Boundary
  imports Bacon_Book_Theory_Propositional_Basics Bacon_Book_Theory_Soundness
begin

section \<open>An open assumption generates falsity under the theory rules\<close>

text \<open>
  Let p:t be the chosen propositional variable and let T = ⊥→⊥.
  From p infer T→p; Gen yields T→∀p.p, and MP with the theorem T
  yields ⊥. Source rules: Definition 5.1 and Definition 5.4,
  Bacon pp.98 and 102. Here ⊥ is the literal Table 4.1 definition.

  This is theory-level derivability from the open assumption p. Gen
  retains its printed condition p ∉ FV(T); it is not given an additional
  premise-set freshness condition. This differs from an MP-only local
  consequence judgment.
\<close>

theorem book_theory_open_prop_bottom:
  assumes rich: "sg_rich G"
  shows "book_theory_derivable \<Sigma> G {NVar (book_prop_name G)} (book_bottom G)"
proof -
  let ?n = "book_prop_name G"
  let ?p = "NVar ?n"
  let ?T = "book_imp (book_bottom G) (book_bottom G)"
  have pl: "book_theory_formula \<Sigma> G ?p"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have bottom: "book_theory_formula \<Sigma> G (book_bottom G)"
    by (rule book_bottom_language[OF rich])
  have tl: "book_theory_formula \<Sigma> G ?T" by (rule book_imp_language[OF bottom bottom])
  have theorem_T: "book_theory_derivable \<Sigma> G {} ?T" by (rule book_theory_imp_refl[OF bottom])
  have T: "book_theory_derivable \<Sigma> G {?p} ?T"
    by (rule book_theory_derivable_mono[OF theorem_T empty_subsetI])
  have p: "book_theory_derivable \<Sigma> G {?p} ?p"
    by (rule book_theory_derivable.Assumption[OF insertI1 pl])
  have conditional: "book_theory_derivable \<Sigma> G {?p} (book_imp ?T ?p)"
    by (rule book_theory_imp_weaken[OF p tl pl])
  have fresh: "?n \<notin> named_fv ?T" by (simp only: book_imp_fv book_bottom_closed; simp)
  have generalized: "book_theory_derivable \<Sigma> G {?p} (book_imp ?T (book_all G ?n ?p))"
    by (rule book_theory_derivable.Gen[OF conditional tl pl fresh])
  have quantified: "book_theory_formula \<Sigma> G (book_all G ?n ?p)"
    by (rule book_all_language[OF pl])
  have result: "book_theory_derivable \<Sigma> G {?p} (book_all G ?n ?p)"
    by (rule book_theory_derivable.MP[OF T generalized quantified])
  show ?thesis by (simp only: book_bottom_as_all[OF rich]; rule result)
qed

section \<open>The unrestricted open-discharge conclusion is not valid in a given model\<close>

text \<open>
  In a full minimal model, take a false point f and the true point
  t = (κ(→) f) f. A typed assignment updated to give p the value t
  makes p true and ⊥ false. Consequently p→⊥ is not valid, and
  theory soundness excludes a proof of it from no assumptions.

  Scope. The nonvalidity and nonderivability results below are conditional
  on the explicitly given book_full_minimal_model and rich stock.
  They do not establish independent inhabitation of that model class.
  This is a counterexample to unrestricted discharge of an OPEN assumption,
  not to a deduction theorem restricted to closed discharged formulas or
  proofs with the required eigenvariable conditions (Theorem 15.2, p.318).
\<close>

context book_full_minimal_model
begin

lemma book_open_deduction_assignment:
  assumes rich: "sg_rich stock"
  shows "\<exists>g. book_env_typed domain stock g \<and>
    V (denote g (NVar (book_prop_name stock))) \<and> \<not> V (denote g (book_bottom stock))"
proof -
  obtain f where member: "f \<in> domain Prop" and false_f: "\<not> V f"
    using false_proposition by (elim bexE)
  let ?t = "app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) f) f"
  have true_point: "?t \<in> domain Prop \<and> V ?t"
    by (rule book_implication_true_point[where V=V, OF book_minimal_implication_value_type member implication_truth])
  obtain g0 where original: "book_env_typed domain stock g0"
    using book_minimal_assignment_exists by (elim exE)
  let ?n = "book_prop_name stock"
  let ?g = "g0(?n := ?t)"
  have n_type: "stock ?n = Prop" by (rule book_prop_name_type[OF rich])
  have named_member: "?t \<in> domain (stock ?n)" by (simp only: n_type; rule conjunct1[OF true_point])
  have typed: "book_env_typed domain stock ?g" by (rule book_env_update[OF original named_member])
  have variable: "denote ?g (NVar ?n) = ?t"
    using denote_var[where n="?n", OF UNIV_I typed] by simp
  have p_true: "V (denote ?g (NVar ?n))" by (simp only: variable; rule conjunct2[OF true_point])
  have bottom_false: "\<not> V (denote ?g (book_bottom stock))" by (rule book_bottom_false[OF rich typed])
  show ?thesis by (rule exI[where x="?g"], rule conjI[OF typed conjI[OF p_true bottom_false]])
qed

theorem book_open_deduction_not_valid:
  assumes rich: "sg_rich stock"
  shows "\<not> book_formula_valid domain stock denote V
    (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
proof
  assume valid: "book_formula_valid domain stock denote V
    (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
  obtain g where typed: "book_env_typed domain stock g"
    and p_true: "V (denote g (NVar (book_prop_name stock)))"
    and bottom_false: "\<not> V (denote g (book_bottom stock))"
    using book_open_deduction_assignment[OF rich] by (elim exE conjE)
  have pl: "book_theory_formula signature stock (NVar (book_prop_name stock))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have bottom: "book_theory_formula signature stock (book_bottom stock)"
    by (rule book_bottom_language[OF rich])
  have true_imp: "V (denote g (book_imp (NVar (book_prop_name stock)) (book_bottom stock)))"
    by (rule book_formula_validE[OF valid typed])
  have material: "V (denote g (NVar (book_prop_name stock))) \<longrightarrow> V (denote g (book_bottom stock))"
    by (rule iffD1[OF book_imp_truth[OF typed pl bottom] true_imp])
  have contradiction: "V (denote g (book_bottom stock))" by (rule mp[OF material p_true])
  show False by (rule notE[OF bottom_false contradiction])
qed

theorem book_open_deduction_not_derivable:
  assumes rich: "sg_rich stock"
  shows "\<not> book_theory_derivable signature stock {}
    (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
proof
  assume derivation: "book_theory_derivable signature stock {}
    (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
  have valid: "book_formula_valid domain stock denote V
    (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
    by (rule book_axiom_generated_soundness[OF rich derivation])
  show False by (rule notE[OF book_open_deduction_not_valid[OF rich] valid])
qed

theorem book_unrestricted_open_deduction_counterexample:
  assumes rich: "sg_rich stock"
  shows "book_theory_derivable signature stock {NVar (book_prop_name stock)} (book_bottom stock) \<and>
    \<not> book_theory_derivable signature stock {} (book_imp (NVar (book_prop_name stock)) (book_bottom stock))"
  by (rule conjI[OF book_theory_open_prop_bottom[OF rich] book_open_deduction_not_derivable[OF rich]])

end

end
