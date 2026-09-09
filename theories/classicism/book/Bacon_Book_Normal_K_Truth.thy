theory Bacon_Book_Normal_K_Truth
  imports Bacon_Book_Implication_Leibniz_Congruence
begin

section \<open>The exact additional identity needed for K\<close>

context book_full_minimal_model
begin

theorem book_normal_K_truth_from_identity:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and pl: "book_theory_formula signature stock P" and ql: "book_theory_formula signature stock Q"
    and identity: "V (denote g (book_leibniz stock Prop (book_imp (book_top stock) Q) Q))"
    and boxed_imp: "V (denote g (book_box stock (book_imp P Q)))"
    and boxed_p: "V (denote g (book_box stock P))"
  shows "V (denote g (book_box stock Q))"
proof -
  have tl: "book_theory_formula signature stock (book_top stock)" by (rule book_top_language[OF rich])
  have il: "book_theory_formula signature stock (book_imp P Q)" by (rule book_imp_language[OF pl ql])
  have tql: "book_theory_formula signature stock (book_imp (book_top stock) Q)" by (rule book_imp_language[OF tl ql])
  have pt: "book_leibniz_equiv domain app V Prop (denote g P) (denote g (book_top stock))"
    using boxed_p by (simp only: book_box_truth[OF rich typed pl])
  have it: "book_leibniz_equiv domain app V Prop (denote g (book_imp P Q)) (denote g (book_top stock))"
    using boxed_imp by (simp only: book_box_truth[OF rich typed il])
  have tq: "book_leibniz_equiv domain app V Prop (denote g (book_imp (book_top stock) Q)) (denote g Q)"
    using identity by (simp only: book_leibniz_truth[OF rich typed tql ql])
  have congruence: "book_leibniz_equiv domain app V Prop
      (denote g (book_imp P Q)) (denote g (book_imp (book_top stock) Q))"
    by (rule book_imp_antecedent_leibniz_cong[OF rich typed pl tl ql pt])
  have middle: "book_leibniz_equiv domain app V Prop
      (denote g (book_imp (book_top stock) Q)) (denote g (book_top stock))"
    by (rule book_leibniz_trans[OF book_leibniz_sym[OF congruence] it])
  have qt: "book_leibniz_equiv domain app V Prop (denote g Q) (denote g (book_top stock))"
    by (rule book_leibniz_trans[OF book_leibniz_sym[OF tq] middle])
  show ?thesis by (simp only: book_box_truth[OF rich typed ql]; rule qt)
qed

end

text \<open>
  The extra premise is (⊤→Q)=ₜQ, not just their truth equivalence.
  With it, Leibniz congruence and transitivity derive K. H does not
  receive that identity as an axiom; the later C proof supplies it by
  propositional Equivalence. No full C model is assumed in this lemma.
\<close>

end
