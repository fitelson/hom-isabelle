theory Bacon_Book_Implication_Leibniz_Congruence
  imports Bacon_Book_Box_Truth
    Bacon_Book_Environment_Development.Bacon_Book_Leibniz_Application
begin

section \<open>Replacing the antecedent by a Leibniz-equivalent value\<close>

context book_full_minimal_model
begin

lemma book_imp_antecedent_leibniz_cong:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and al: "book_theory_formula signature stock A" and bl: "book_theory_formula signature stock B"
    and ql: "book_theory_formula signature stock Q"
    and equivalent: "book_leibniz_equiv domain app V Prop (denote g A) (denote g B)"
  shows "book_leibniz_equiv domain app V Prop
    (denote g (book_imp A Q)) (denote g (book_imp B Q))"
proof -
  have heads: "book_leibniz_equiv domain app V (Arr Prop Prop)
      (app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g A))
      (app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g B))"
    by (rule book_leibniz_argument_cong[OF rich typed equivalent book_minimal_implication_value_type])
  have qm: "denote g Q \<in> domain Prop" by (rule denote_type[OF UNIV_I ql typed])
  have results: "book_leibniz_equiv domain app V Prop
      (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g A)) (denote g Q))
      (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g B)) (denote g Q))"
    by (rule book_leibniz_head_cong[OF rich typed heads qm])
  show ?thesis by (simp only: book_imp_denote[OF typed al ql] book_imp_denote[OF typed bl ql]; rule results)
qed

end

end
