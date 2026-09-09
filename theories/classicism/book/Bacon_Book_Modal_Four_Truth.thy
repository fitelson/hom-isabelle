theory Bacon_Book_Modal_Four_Truth
  imports Bacon_Book_Implication_Leibniz_Congruence
begin

section \<open>Leibniz congruence for the literal Box operator\<close>

context book_full_minimal_model
begin

lemma book_box_top_true:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "V (denote g (book_box stock (book_top stock)))"
proof -
  have tl: "book_theory_formula signature stock (book_top stock)" by (rule book_top_language[OF rich])
  have tm: "denote g (book_top stock) \<in> domain Prop" by (rule denote_type[OF UNIV_I tl typed])
  show ?thesis by (simp only: book_box_truth[OF rich typed tl];
    rule book_leibniz_refl[where D=domain and \<sigma>=Prop, OF tm])
qed

theorem book_modal_four_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and pl: "book_theory_formula signature stock P"
    and necessary_box_top: "V (denote g (book_box stock (book_box stock (book_top stock))))"
    and boxed: "V (denote g (book_box stock P))"
  shows "V (denote g (book_box stock (book_box stock P)))"
proof -
  have tl: "book_theory_formula signature stock (book_top stock)" by (rule book_top_language[OF rich])
  have bpl: "book_theory_formula signature stock (book_box stock P)" by (rule book_box_language[OF rich pl])
  have btl: "book_theory_formula signature stock (book_box stock (book_top stock))" by (rule book_box_language[OF rich tl])
  have operator: "denote g (book_box_const stock) \<in> domain (Arr Prop Prop)"
    by (rule denote_type[OF UNIV_I book_box_const_language[OF rich] typed])
  have pt: "book_leibniz_equiv domain app V Prop (denote g P) (denote g (book_top stock))"
    using boxed by (simp only: book_box_truth[OF rich typed pl])
  have applied: "book_leibniz_equiv domain app V Prop
      (app Prop Prop (denote g (book_box_const stock)) (denote g P))
      (app Prop Prop (denote g (book_box_const stock)) (denote g (book_top stock)))"
    by (rule book_leibniz_argument_cong[OF rich typed pt operator])
  have bp: "denote g (book_box stock P) = app Prop Prop (denote g (book_box_const stock)) (denote g P)"
    unfolding book_box_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I book_box_const_language[OF rich] pl typed])
  have bt: "denote g (book_box stock (book_top stock)) =
      app Prop Prop (denote g (book_box_const stock)) (denote g (book_top stock))"
    unfolding book_box_def by (rule denote_app[OF UNIV_I UNIV_I UNIV_I book_box_const_language[OF rich] tl typed])
  have congruence: "book_leibniz_equiv domain app V Prop
      (denote g (book_box stock P)) (denote g (book_box stock (book_top stock)))"
    by (simp only: bp bt; rule applied)
  have btt: "book_leibniz_equiv domain app V Prop (denote g (book_box stock (book_top stock))) (denote g (book_top stock))"
    using necessary_box_top by (simp only: book_box_truth[OF rich typed btl])
  have result: "book_leibniz_equiv domain app V Prop (denote g (book_box stock P)) (denote g (book_top stock))"
    by (rule book_leibniz_trans[OF congruence btt])
  show ?thesis by (simp only: book_box_truth[OF rich typed bpl]; rule result)
qed

end

text \<open>
  H makes □⊤ true because its defining identity is reflexive.
  The second result keeps □□⊤ as an explicit premise. Leibniz
  congruence applies the Box operator to P≈⊤, then transitivity
  uses □⊤≈⊤. It does not assume identity of merely true propositions
  or Necessitation under the temporary assumption □P.
\<close>

end
