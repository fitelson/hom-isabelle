theory Goodman_Native_QSS
  imports Goodman_Native_Fun_Prime
begin

section \<open>QSS in the independent named language\<close>

text \<open>
  QSS: ∀XYr. (Pure(X) ∧ Pure(Y) ∧ Fun(r)) → (Xr = Yr → X = Y).
  X and Y have type t→t, and r has type t. All identities are the book's
  Leibniz identities. This is an independent named formula, not a name
  for the translation of pp_QSS. Its translation equality is proved below.
\<close>

definition gb_QSS_instance where
  "gb_QSS_instance G X Y r = book_imp
    (book_and G (gb_pure gb_unary X) (book_and G (gb_pure gb_unary Y) (gb_fun Prop r)))
    (book_imp (book_leibniz G Prop (NApp X r) (NApp Y r)) (book_leibniz G gb_unary X Y))"

definition gb_QSS where
  "gb_QSS G = book_all G (gb_x G gb_unary) (book_all G (gb_y G gb_unary gb_unary)
    (book_all G (gb_z G gb_unary gb_unary Prop)
      (gb_QSS_instance G (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary gb_unary))
        (NVar (gb_z G gb_unary gb_unary Prop)))))"

lemma gb_QSS_instance_language:
  assumes rich: "sg_rich G"
    and xl: "book_in_language book_minimal_logical_type UNIV gb_signature G X gb_unary"
    and yl: "book_in_language book_minimal_logical_type UNIV gb_signature G Y gb_unary"
    and rl: "book_theory_formula gb_signature G r"
  shows "book_theory_formula gb_signature G (gb_QSS_instance G X Y r)"
proof -
  have xr: "book_theory_formula gb_signature G (NApp X r)" by (rule book_language_App[OF xl rl])
  have yr: "book_theory_formula gb_signature G (NApp Y r)" by (rule book_language_App[OF yl rl])
  show ?thesis unfolding gb_QSS_instance_def
    by (intro book_imp_language book_and_language[OF rich] gb_pure_language gb_fun_language
      book_leibniz_language[OF rich] xl yl rl xr yr)
qed

lemma gb_QSS_language:
  "sg_rich G \<Longrightarrow> book_theory_formula gb_signature G (gb_QSS G)"
  unfolding gb_QSS_def
  by (intro book_all_language gb_QSS_instance_language gb_x_language gb_y_language gb_z_language; assumption)

lemma gb_QSS_instance_fv:
  "named_fv (gb_QSS_instance G X Y r) = named_fv X \<union> named_fv Y \<union> named_fv r"
  by (auto simp: gb_QSS_instance_def book_imp_fv book_and_fv book_leibniz_fv)

lemma gb_QSS_closed:
  "named_fv (gb_QSS G) = {}"
  by (auto simp: gb_QSS_def gb_QSS_instance_fv book_all_fv)

lemma gi_QSS_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_QSS"
  by (simp add: pp_QSS_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
    gi_goodman_names_def gb_signature_def)

theorem gi_QSS_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_QSS = gb_QSS G"
  by (simp add: pp_QSS_def gb_QSS_def gb_QSS_instance_def pp_unary_ty_def
    gi_pure_translation gi_fun_translation gb_x_def gb_y_def gb_z_def Let_def
    named_chart_fresh_def insert_commute)

theorem gi_repaired_native_QSS:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_zeroary_exhaustion G) (gb_QSS G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have old: "[] ; insert pp_zeroary_exhaustion pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    using CEV_QSS_from_recombination_with_zeroary_exhaustion[where \<Gamma>="[]"]
    by (simp only: pp_recombination_zeroary_exhaustion_axioms_def)
  have result: "goodman_book_proves gb_signature G (gb_recombination_PP_zeroary_exhaustion G)
    (gi_to_book G [] k pp_QSS)"
    by (rule gi_repaired_PP_preservation_in_signature[OF rich names old _ _ gi_QSS_admitted[OF names]]; simp)
  show ?thesis using result by (simp only: gi_QSS_translation[OF names])
qed

section \<open>QSS and unique fundamentality supply the witness\<close>

lemma gi_QSS_unique_native_stock_exists:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G {gb_QSS G, gb_unique_fundamental G Prop} (gb_exists_fun_prime G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  let ?S = "{pp_QSS, pp_unique_fundamental Prop}"
  have qss: "\<And>\<Delta>. \<Delta> ; ?S \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    by (rule CEV_axiom_proves.Axiom; (simp | rule gi_old_closed_weaken[OF typed_pp_QSS]))
  have unique: "pp_unique_fundamental Prop \<in> ?S" by simp
  have old: "[] ; ?S \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    by (rule CEV_exists_fun_prime_from_QSS_and_unique_fundamentality[OF qss unique])
  have closed: "\<And>B. B \<in> ?S \<Longrightarrow> [] \<turnstile> B : Prop"
    by (auto intro: typed_pp_QSS typed_pp_unique_fundamental)
  have admitted: "\<And>B. B \<in> ?S \<Longrightarrow> gi_constants_admitted k gb_signature B"
    using names by (auto simp: pp_unique_fundamental_def pp_fun_def pp_Fun_def
      gi_goodman_names_def gb_signature_def intro: gi_QSS_admitted)
  have transferred: "goodman_book_proves gb_signature G (image (gi_to_book G [] k) ?S)
    (gi_to_book G [] k pp_exists_fun_prime)"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich old closed _ _ admitted
      gi_exists_fun_prime_admitted[OF names]]; simp)
  show ?thesis using transferred by (simp only: image_insert image_empty gi_QSS_translation[OF names]
    gi_unique_fundamental_translation[OF names] gi_exists_fun_prime_translation[OF names])
qed

theorem gi_native_exists_fun_prime_from_QSS:
  assumes rich: "sg_rich G" and qss: "goodman_book_proves gb_signature G T (gb_QSS G)"
    and unique: "goodman_book_proves gb_signature G T (gb_unique_fundamental G Prop)"
  shows "goodman_book_proves gb_signature G T (gb_exists_fun_prime G)"
  by (rule goodman_book_cut[OF gi_QSS_unique_native_stock_exists[OF rich]];
    use qss unique in auto)

text \<open>
  The final theorem takes QSS and unique fundamentality as theorem-level
  premises in the same extension T. It does not assume their validity in
  arbitrary models. The separate repaired-stock theorem still retains
  zeroary Exhaustion; no claim of a Recombination-only derivation is made.
\<close>

end
