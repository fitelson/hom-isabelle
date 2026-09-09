theory Bacon_Book_Box_Truth
  imports Bacon_Book_Classicism_Propositional_Equivalence
    Bacon_Book_Environment_Development.Bacon_Book_Minimal_Leibniz_Truth
begin

section \<open>The literal Box application in an arbitrary minimal H model\<close>

context book_full_minimal_model
begin

theorem book_box_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_theory_formula signature stock P"
  shows "V (denote g (book_box stock P)) =
    book_leibniz_equiv domain app V Prop (denote g P) (denote g (book_top stock))"
proof -
  let ?n = "book_prop_name stock"
  let ?body = "book_leibniz stock Prop (NVar ?n) (book_top stock)"
  let ?h = "g(?n := denote g P)"
  have nt: "stock ?n = Prop" by (rule book_prop_name_type[OF rich])
  have variable: "book_theory_formula signature stock (NVar ?n)" by (simp only: book_language_var_iff nt)
  have truth: "book_theory_formula signature stock (book_top stock)" by (rule book_top_language[OF rich])
  have body: "book_theory_formula signature stock ?body" by (rule book_leibniz_language[OF rich variable truth])
  have pm: "denote g P \<in> domain (stock ?n)"
    using denote_type[OF UNIV_I language typed] by (simp only: nt)
  have ht: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed pm])
  have application: "denote g (book_box stock P) =
    app Prop Prop (denote g (NLam ?n ?body)) (denote g P)"
    using denote_app[OF UNIV_I UNIV_I UNIV_I book_box_const_language[OF rich] language typed]
    by (simp only: book_box_def book_box_const_def)
  have beta: "app Prop Prop (denote g (NLam ?n ?body)) (denote g P) = denote ?h ?body"
    using book_full_lambda_application[OF body typed pm] by (simp only: nt)
  have variable_value: "denote ?h (NVar ?n) = denote g P"
    using denote_var[where n="?n", OF UNIV_I ht] by simp
  have top_value: "denote ?h (book_top stock) = denote g (book_top stock)"
    by (rule book_denote_locality[OF UNIV_I truth ht typed]; simp only: book_top_closed; simp)
  show ?thesis by (simp only: application beta book_leibniz_truth[OF rich ht variable truth] variable_value top_value)
qed

corollary book_box_unfolding_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_theory_formula signature stock P"
  shows "V (denote g (book_box stock P)) =
    V (denote g (book_leibniz stock Prop P (book_top stock)))"
  by (simp only: book_box_truth[OF rich typed language]
    book_leibniz_truth[OF rich typed language book_top_language[OF rich]])

end

text \<open>
  The value of the literal λ application is evaluated at an actual
  typed assignment update. The resulting identity is Leibniz equivalence,
  not HOL equality. These facts hold in every supplied minimal H model;
  no C axiom, modal model, Functionality or completeness premise is used.
\<close>

end
