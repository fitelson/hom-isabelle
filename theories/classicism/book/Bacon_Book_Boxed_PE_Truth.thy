theory Bacon_Book_Boxed_PE_Truth
  imports Bacon_Book_Boxed_PE_Identities
begin

context book_full_minimal_model
begin

theorem book_boxed_PE_conditional_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and pl: "book_theory_formula signature stock P" and ql: "book_theory_formula signature stock Q"
    and identities: "\<And>A. A \<in> book_boxed_PE_premises stock P Q \<Longrightarrow> V (denote g A)"
    and boxed: "V (denote g (book_box stock (book_iff stock P Q)))"
  shows "V (denote g (book_leibniz stock Prop P Q))"
proof -
  let ?E = "book_iff stock P Q"
  let ?T = "book_top stock"
  have el: "book_theory_formula signature stock ?E" by (rule book_iff_language[OF rich pl ql])
  have tl: "book_theory_formula signature stock ?T" by (rule book_top_language[OF rich])
  have ep: "book_theory_formula signature stock (book_imp ?E P)" by (rule book_imp_language[OF el pl])
  have eq: "book_theory_formula signature stock (book_imp ?E Q)" by (rule book_imp_language[OF el ql])
  have tp: "book_theory_formula signature stock (book_imp ?T P)" by (rule book_imp_language[OF tl pl])
  have tq: "book_theory_formula signature stock (book_imp ?T Q)" by (rule book_imp_language[OF tl ql])
  have common_truth: "V (denote g (book_leibniz stock Prop (book_imp ?E P) (book_imp ?E Q)))"
    by (rule identities; simp only: book_boxed_PE_premises_def; blast)
  have p_truth: "V (denote g (book_leibniz stock Prop (book_imp ?T P) P))"
    by (rule identities; simp only: book_boxed_PE_premises_def; blast)
  have q_truth: "V (denote g (book_leibniz stock Prop (book_imp ?T Q) Q))"
    by (rule identities; simp only: book_boxed_PE_premises_def; blast)
  have common: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?E P)) (denote g (book_imp ?E Q))"
    using common_truth by (simp only: book_leibniz_truth[OF rich typed ep eq])
  have p_identity: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?T P)) (denote g P)"
    using p_truth by (simp only: book_leibniz_truth[OF rich typed tp pl])
  have q_identity: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?T Q)) (denote g Q)"
    using q_truth by (simp only: book_leibniz_truth[OF rich typed tq ql])
  have et: "book_leibniz_equiv domain app V Prop (denote g ?E) (denote g ?T)"
    using boxed by (simp only: book_box_truth[OF rich typed el])
  have left: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?E P)) (denote g (book_imp ?T P))"
    by (rule book_imp_antecedent_leibniz_cong[OF rich typed el tl pl et])
  have right: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?E Q)) (denote g (book_imp ?T Q))"
    by (rule book_imp_antecedent_leibniz_cong[OF rich typed el tl ql et])
  have p_to_ep: "book_leibniz_equiv domain app V Prop (denote g P) (denote g (book_imp ?E P))"
    by (rule book_leibniz_trans[OF book_leibniz_sym[OF p_identity] book_leibniz_sym[OF left]])
  have eq_to_q: "book_leibniz_equiv domain app V Prop (denote g (book_imp ?E Q)) (denote g Q)"
    by (rule book_leibniz_trans[OF right q_identity])
  have result: "book_leibniz_equiv domain app V Prop (denote g P) (denote g Q)"
    by (rule book_leibniz_trans[OF book_leibniz_trans[OF p_to_ep common] eq_to_q])
  show ?thesis by (simp only: book_leibniz_truth[OF rich typed pl ql]; rule result)
qed

end

text \<open>
  Under □E, E is Leibniz-equivalent to ⊤. Antecedent congruence
  changes E→P and E→Q to ⊤→P and ⊤→Q. The three supplied identities
  then yield P=ₜQ by symmetry and transitivity. This is a conditional
  H-model calculation; its identity premises are not silently assumed
  valid in every H model. They will be discharged as original C theorems.
\<close>

end
