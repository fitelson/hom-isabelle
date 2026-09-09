theory Bacon_Book_Term_Logical_Clauses
  imports Bacon_Book_Term_Valuation
begin

context book_C_identity_world
begin

lemma term_implication_app_classes:
  assumes pm: "P \<in> book_closed_terms \<Sigma> G Prop" and qm: "Q \<in> book_closed_terms \<Sigma> G Prop"
  shows "book_C_term_app \<Sigma> G w Prop Prop
    (book_C_term_app \<Sigma> G w Prop (Arr Prop Prop) (book_C_term_logical_value \<Sigma> G w SImp)
      (book_C_identity_class \<Sigma> G w Prop P)) (book_C_identity_class \<Sigma> G w Prop Q) =
    book_C_identity_class \<Sigma> G w Prop (book_imp P Q)"
proof -
  have op: "NLogical SImp \<in> book_closed_terms \<Sigma> G (Arr Prop (Arr Prop Prop))"
    using book_C_logical_closed_terms[of SImp \<Sigma> G] by simp
  have partial: "NApp (NLogical SImp) P \<in> book_closed_terms \<Sigma> G (Arr Prop Prop)"
    by (rule book_closed_terms_App[OF op pm])
  show ?thesis by (simp only: book_C_term_logical_value_def book_minimal_logical_type.simps
    term_app_classes[OF op pm] term_app_classes[OF partial qm] book_imp_def)
qed

theorem term_implication_truth:
  assumes pm: "p \<in> book_C_identity_domain \<Sigma> G w Prop"
    and qm: "q \<in> book_C_identity_domain \<Sigma> G w Prop"
  shows "book_C_term_valuation w
    (book_C_term_app \<Sigma> G w Prop Prop
      (book_C_term_app \<Sigma> G w Prop (Arr Prop Prop) (book_C_term_logical_value \<Sigma> G w SImp) p) q)
    = (book_C_term_valuation w p \<longrightarrow> book_C_term_valuation w q)"
proof -
  let ?P = "book_C_identity_rep p"
  let ?Q = "book_C_identity_rep q"
  have pc: "?P \<in> book_closed_terms \<Sigma> G Prop" by (rule identity_rep_typed[OF pm])
  have qc: "?Q \<in> book_closed_terms \<Sigma> G Prop" by (rule identity_rep_typed[OF qm])
  have ps: "book_C_identity_class \<Sigma> G w Prop ?P = p" by (rule identity_rep_class[OF pm])
  have qs: "book_C_identity_class \<Sigma> G w Prop ?Q = q" by (rule identity_rep_class[OF qm])
  have application: "book_C_term_app \<Sigma> G w Prop Prop
      (book_C_term_app \<Sigma> G w Prop (Arr Prop Prop) (book_C_term_logical_value \<Sigma> G w SImp) p) q =
    book_C_identity_class \<Sigma> G w Prop (book_imp ?P ?Q)"
    using term_implication_app_classes[OF pc qc] by (simp only: ps qs)
  show ?thesis using term_valuation_implication_class[OF pc qc]
    by (simp only: application ps qs; blast)
qed

lemma term_forall_app_class:
  assumes fm: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
  shows "book_C_term_app \<Sigma> G w (Arr \<sigma> Prop) Prop (book_C_term_logical_value \<Sigma> G w (SBAll \<sigma>))
    (book_C_identity_class \<Sigma> G w (Arr \<sigma> Prop) F) =
    book_C_identity_class \<Sigma> G w Prop (NApp (NLogical (SBAll \<sigma>)) F)"
proof -
  have op: "NLogical (SBAll \<sigma>) \<in> book_closed_terms \<Sigma> G (Arr (Arr \<sigma> Prop) Prop)"
    using book_C_logical_closed_terms[of "SBAll \<sigma>" \<Sigma> G] by simp
  show ?thesis by (simp only: book_C_term_logical_value_def book_minimal_logical_type.simps; rule term_app_classes[OF op fm])
qed

theorem term_forall_truth:
  assumes witnesses: "book_closed_constant_witness_complete \<Sigma> G w"
    and fm: "f \<in> book_C_identity_domain \<Sigma> G w (Arr \<sigma> Prop)"
  shows "book_C_term_valuation w
    (book_C_term_app \<Sigma> G w (Arr \<sigma> Prop) Prop (book_C_term_logical_value \<Sigma> G w (SBAll \<sigma>)) f)
    = (\<forall>a\<in>book_C_identity_domain \<Sigma> G w \<sigma>.
      book_C_term_valuation w (book_C_term_app \<Sigma> G w \<sigma> Prop f a))"
proof -
  let ?F = "book_C_identity_rep f"
  have fc: "?F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> Prop)" by (rule identity_rep_typed[OF fm])
  have fs: "book_C_identity_class \<Sigma> G w (Arr \<sigma> Prop) ?F = f" by (rule identity_rep_class[OF fm])
  have op: "NLogical (SBAll \<sigma>) \<in> book_closed_terms \<Sigma> G (Arr (Arr \<sigma> Prop) Prop)"
    using book_C_logical_closed_terms[of "SBAll \<sigma>" \<Sigma> G] by simp
  have uc: "NApp (NLogical (SBAll \<sigma>)) ?F \<in> book_closed_terms \<Sigma> G Prop"
    by (rule book_closed_terms_App[OF op fc])
  have application: "book_C_term_app \<Sigma> G w (Arr \<sigma> Prop) Prop (book_C_term_logical_value \<Sigma> G w (SBAll \<sigma>)) f =
    book_C_identity_class \<Sigma> G w Prop (NApp (NLogical (SBAll \<sigma>)) ?F)"
    using term_forall_app_class[OF fc] by (simp only: fs)
  have instances: "(\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>. NApp ?F A \<in> w) =
    (\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>.
      book_C_term_valuation w (book_C_term_app \<Sigma> G w \<sigma> Prop f (book_C_identity_class \<Sigma> G w \<sigma> A)))"
  proof (rule ball_cong[OF refl])
    fix A
    assume am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    have ap: "book_C_term_app \<Sigma> G w \<sigma> Prop f (book_C_identity_class \<Sigma> G w \<sigma> A) =
      book_C_identity_class \<Sigma> G w Prop (NApp ?F A)"
      using term_app_classes[OF fc am] by (simp only: fs)
    show "(NApp ?F A \<in> w) =
      book_C_term_valuation w (book_C_term_app \<Sigma> G w \<sigma> Prop f (book_C_identity_class \<Sigma> G w \<sigma> A))"
      by (simp only: ap term_valuation_class[OF book_closed_terms_App[OF fc am]])
  qed
  have all_values: "(\<forall>A\<in>book_closed_terms \<Sigma> G \<sigma>.
      book_C_term_valuation w (book_C_term_app \<Sigma> G w \<sigma> Prop f (book_C_identity_class \<Sigma> G w \<sigma> A))) =
    (\<forall>a\<in>book_C_identity_domain \<Sigma> G w \<sigma>. book_C_term_valuation w (book_C_term_app \<Sigma> G w \<sigma> Prop f a))"
    unfolding book_C_identity_domain_def by simp
  show ?thesis by (simp only: application term_valuation_class[OF uc]
    book_closed_maximal_forall_iff[OF rich term_H_maximal witnesses fc] instances all_values)
qed

end

text \<open>
  Both primitive clauses range over every typed identity-class value.
  For ∀σ, witness completeness first gives the closed-term equivalence;
  the exact image definition of Tσ then changes the quantification
  from terms to all domain values. No full model, semantic quantifier
  law or restriction to selected representatives is assumed.
\<close>

end
