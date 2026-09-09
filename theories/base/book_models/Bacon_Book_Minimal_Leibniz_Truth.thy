theory Bacon_Book_Minimal_Leibniz_Truth
  imports Bacon_Book_Minimal_Leibniz_Syntax Bacon_Book_Minimal_Boolean_Truth
    Bacon_Book_Two_Abstractions
begin

section \<open>The literal Leibniz operator quantifies over every semantic predicate\<close>

text \<open>
  The formula (λxy.∀Z.(Zx↔Zy))AB is true exactly when ⟦A⟧ᵍ and
  ⟦B⟧ᵍ are Leibniz-equivalent. Source: Table 4.1 and Definition 4.4,
  p.93, together with Definition 15.5, p.321.

  The two actual argument applications first update x and y with their
  values at the original assignment. Universal truth then ranges over
  every P ∈ Dσ→t; a third typed update supplies P to Z. Distinctness
  keeps all three assigned values in place. The literal biconditional's
  proved truth clause reduces its two predicate applications to the
  defining tests for Leibniz equivalence.

  Status: full minimal models, rich stock and a given typed assignment.
  No actual identity, Functionality, source H judgment, restriction to
  denotable predicates, or new logical identity clause is assumed.
\<close>

context book_full_minimal_model
begin

theorem book_leibniz_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A \<sigma>"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B \<sigma>"
  shows "V (denote g (book_leibniz stock \<sigma> A B)) =
    book_leibniz_equiv domain app V \<sigma> (denote g A) (denote g B)"
proof -
  let ?x = "book_leibniz_x stock \<sigma>"
  let ?y = "book_leibniz_y stock \<sigma>"
  let ?z = "book_leibniz_z stock \<sigma>"
  let ?a = "denote g A"
  let ?b = "denote g B"
  let ?h = "(g(?x := ?a))(?y := ?b)"
  let ?M = "book_leibniz_matrix stock \<sigma> :: 'c book_named_term"
  have xt: "stock ?x = \<sigma>" by (rule book_leibniz_name_types(1)[OF rich])
  have yt: "stock ?y = \<sigma>" by (rule book_leibniz_name_types(2)[OF rich])
  have zt: "stock ?z = Arr \<sigma> Prop" by (rule book_leibniz_name_types(3)[OF rich])
  have ax: "book_in_language book_minimal_logical_type UNIV signature stock A (stock ?x)"
    by (simp only: xt; rule A)
  have by_type: "book_in_language book_minimal_logical_type UNIV signature stock B (stock ?y)"
    by (simp only: yt; rule B)
  have am: "?a \<in> domain \<sigma>" by (rule denote_type[OF UNIV_I A typed])
  have bm: "?b \<in> domain \<sigma>" by (rule denote_type[OF UNIV_I B typed])
  have ht: "book_env_typed domain stock ?h"
    by (rule book_two_argument_updates_typed[OF typed ax by_type])
  have matrix_language: "book_in_language book_minimal_logical_type UNIV signature stock ?M Prop"
    by (rule book_leibniz_matrix_language[OF rich])
  have body_language: "book_in_language book_minimal_logical_type UNIV signature stock
    (book_leibniz_body stock \<sigma>) Prop"
    by (rule book_leibniz_body_language[OF rich])
  have evaluated: "denote g (book_leibniz stock \<sigma> A B) =
    denote ?h (book_leibniz_body stock \<sigma>)"
    using book_two_abstractions_denote[where x="?x" and y="?y", OF typed body_language ax by_type]
    by (simp only: book_leibniz_def book_leibniz_const_def)
  have quantified: "V (denote ?h (book_leibniz_body stock \<sigma>)) =
    (\<forall>P \<in> domain (Arr \<sigma> Prop). V (denote (?h(?z := P)) ?M))"
    using book_all_truth[where n="?z", OF ht matrix_language]
    by (simp only: book_leibniz_body_def zt)
  have xl: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?x) \<sigma>"
    by (rule book_leibniz_variables_language(1)[OF rich])
  have yl: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?y) \<sigma>"
    by (rule book_leibniz_variables_language(2)[OF rich])
  have zl: "book_in_language book_minimal_logical_type UNIV signature stock (NVar ?z) (Arr \<sigma> Prop)"
    by (rule book_leibniz_variables_language(3)[OF rich])
  have left_language: "book_in_language book_minimal_logical_type UNIV signature stock
    (NApp (NVar ?z) (NVar ?x)) Prop"
    by (rule book_language_App[OF zl xl])
  have right_language: "book_in_language book_minimal_logical_type UNIV signature stock
    (NApp (NVar ?z) (NVar ?y)) Prop"
    by (rule book_language_App[OF zl yl])
  have pointwise: "V (denote (?h(?z := P)) ?M) =
    (V (app \<sigma> Prop P ?a) = V (app \<sigma> Prop P ?b))"
    if member: "P \<in> domain (Arr \<sigma> Prop)" for P
  proof -
    let ?k = "?h(?z := P)"
    have named_member: "P \<in> domain (stock ?z)" by (simp only: zt; rule member)
    have kt: "book_env_typed domain stock ?k" by (rule book_env_update[OF ht named_member])
    have x_value: "denote ?k (NVar ?x) = ?a"
      using denote_var[where n="?x", OF UNIV_I kt] book_leibniz_names_distinct[OF rich, where \<sigma>=\<sigma>]
      by auto
    have y_value: "denote ?k (NVar ?y) = ?b"
      using denote_var[where n="?y", OF UNIV_I kt] book_leibniz_names_distinct[OF rich, where \<sigma>=\<sigma>]
      by auto
    have z_value: "denote ?k (NVar ?z) = P"
      using denote_var[where n="?z", OF UNIV_I kt] by simp
    have left_value: "denote ?k (NApp (NVar ?z) (NVar ?x)) = app \<sigma> Prop P ?a"
      using denote_app[OF UNIV_I UNIV_I UNIV_I zl xl kt] by (simp only: z_value x_value)
    have right_value: "denote ?k (NApp (NVar ?z) (NVar ?y)) = app \<sigma> Prop P ?b"
      using denote_app[OF UNIV_I UNIV_I UNIV_I zl yl kt] by (simp only: z_value y_value)
    show ?thesis using book_iff_truth[OF rich kt left_language right_language]
      by (simp only: book_leibniz_matrix_def left_value right_value)
  qed
  have all_tests: "(\<forall>P \<in> domain (Arr \<sigma> Prop). V (denote (?h(?z := P)) ?M)) =
    (\<forall>P \<in> domain (Arr \<sigma> Prop). V (app \<sigma> Prop P ?a) = V (app \<sigma> Prop P ?b))"
  proof (rule ball_cong[OF refl])
    fix P
    assume member: "P \<in> domain (Arr \<sigma> Prop)"
    show "V (denote (?h(?z := P)) ?M) =
      (V (app \<sigma> Prop P ?a) = V (app \<sigma> Prop P ?b))"
      by (rule pointwise[OF member])
  qed
  have relation: "book_leibniz_equiv domain app V \<sigma> ?a ?b =
    (\<forall>P \<in> domain (Arr \<sigma> Prop). V (app \<sigma> Prop P ?a) = V (app \<sigma> Prop P ?b))"
    by (simp add: book_leibniz_equiv_def am bm)
  show ?thesis by (simp only: evaluated quantified all_tests relation)
qed

end

end
