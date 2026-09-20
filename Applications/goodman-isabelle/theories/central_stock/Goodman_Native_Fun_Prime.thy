theory Goodman_Native_Fun_Prime
  imports Goodman_Legacy_Central_Stock.Bacon_PP_QSS_Recombination_Bridge
    Goodman_Integration_T6.Goodman_T6_Restricted_Signature
begin

section \<open>Evaluation-injectivity in the independent named language\<close>

text \<open>
  With explicit, distinct unary-operator names X and Y fresh for p,
  fun′(p) says ∀XY. (Pure(X) ∧ Pure(Y)) → (Xp = Yp → X = Y).
  These are the book's Leibniz identities, not HOL equality. The named
  constructor below makes the binders explicit; callers must ensure
  freshness to read it as a predicate of the original free p. The closed
  existential instance chooses and checks all three distinct typed names.
\<close>

definition gb_fun_prime_with_names where
  "gb_fun_prime_with_names G x y p = book_all G x (book_all G y
    (book_imp (book_and G (gb_pure gb_unary (NVar x)) (gb_pure gb_unary (NVar y)))
      (book_imp (book_leibniz G Prop (NApp (NVar x) p) (NApp (NVar y) p))
        (book_leibniz G gb_unary (NVar x) (NVar y)))))"

definition gb_exists_fun_prime where
  "gb_exists_fun_prime G = book_exists G (gb_x G Prop)
    (gb_fun_prime_with_names G (gb_y G Prop gb_unary) (gb_z G Prop gb_unary gb_unary)
      (NVar (gb_x G Prop)))"

lemma gb_fun_prime_with_names_language:
  assumes rich: "sg_rich G" and x: "G x = gb_unary" and y: "G y = gb_unary"
    and pl: "book_theory_formula gb_signature G p"
  shows "book_theory_formula gb_signature G (gb_fun_prime_with_names G x y p)"
proof -
  have xl: "book_in_language book_minimal_logical_type UNIV gb_signature G (NVar x) gb_unary"
    and yl: "book_in_language book_minimal_logical_type UNIV gb_signature G (NVar y) gb_unary"
    by (simp_all only: book_language_var_iff x y)
  have xp: "book_theory_formula gb_signature G (NApp (NVar x) p)"
    and yp: "book_theory_formula gb_signature G (NApp (NVar y) p)"
    by (rule book_language_App[OF xl pl], rule book_language_App[OF yl pl])
  show ?thesis unfolding gb_fun_prime_with_names_def
    by (intro book_all_language book_imp_language book_and_language[OF rich]
      gb_pure_language book_leibniz_language[OF rich] xl yl xp yp)
qed

lemma gb_fun_prime_with_names_fv:
  "named_fv (gb_fun_prime_with_names G x y p) = named_fv p - {x, y}"
  by (auto simp: gb_fun_prime_with_names_def book_all_fv book_imp_fv book_and_fv book_leibniz_fv)

lemma gb_exists_fun_prime_names:
  "sg_rich G \<Longrightarrow> distinct [gb_x G Prop, gb_y G Prop gb_unary, gb_z G Prop gb_unary gb_unary]"
  by (rule gb_names_distinct; assumption)

lemma gb_exists_fun_prime_language:
  "sg_rich G \<Longrightarrow> book_theory_formula gb_signature G (gb_exists_fun_prime G)"
  unfolding gb_exists_fun_prime_def
  by (intro book_exists_language gb_fun_prime_with_names_language gb_names_type gb_x_language; assumption)

lemma gb_exists_fun_prime_closed:
  "named_fv (gb_exists_fun_prime G) = {}"
  by (simp add: gb_exists_fun_prime_def book_exists_fv gb_fun_prime_with_names_fv)

theorem gi_exists_fun_prime_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_exists_fun_prime = gb_exists_fun_prime G"
  by (simp add: pp_exists_fun_prime_def pp_fun_prime_def gb_exists_fun_prime_def gb_fun_prime_with_names_def
    pp_unary_ty_def gi_pure_translation gb_x_def gb_y_def gb_z_def Let_def
    shift_by_def shift_ren_def named_chart_fresh_def insert_commute)

section \<open>The repaired central stock supplies its own witness\<close>

theorem gi_repaired_native_exists_fun_prime:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_zeroary_exhaustion G) (gb_exists_fun_prime G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "[] ; insert pp_zeroary_exhaustion pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    using CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion[where \<Gamma>="[]"]
    by (simp only: pp_recombination_zeroary_exhaustion_axioms_def)
  have translated: "goodman_book_proves gb_signature G (gb_recombination_PP_zeroary_exhaustion G)
    (gi_to_book G [] k pp_exists_fun_prime)"
    by (rule gi_repaired_PP_preservation_in_signature[OF rich names original _ _ gi_exists_fun_prime_admitted[OF names]]; simp)
  show ?thesis using translated by (simp only: gi_exists_fun_prime_translation[OF names])
qed

text \<open>
  The existence of a fun′ proposition is derived, not assumed. This
  endpoint retains the repaired central stock, including zeroary
  Exhaustion and unique fundamentality. It does not establish the
  uncorrected Recombination-only QSS bridge or consistency of the stock.
\<close>

end
