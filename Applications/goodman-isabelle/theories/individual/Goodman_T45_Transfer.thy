theory Goodman_T45_Transfer
  imports Goodman_T3_Transfer
begin

section \<open>T4: evaluation injectivity at the higher type\<close>

text \<open>
  For C:t→(t→t), T4 says Pure(C) → ¬fun′_(t→t)(Cr). The source parameter
  theorem requires only that C and r are typed: purity remains an explicit
  object-language antecedent, not a consequence of syntactic closedness.
  The quantified version covers every C. A closed pure C is consequently a
  special case, not the entire scope of the verified parameter theorem.
  The stock is logical purity plus application closure; PP and fun′(r) are
  not assumed. Higher-type fun′ quantifies predicates of the higher type.
\<close>

lemma gi_T4_source_stock:
  "pp_T4_axioms = pp_T2_min_axioms"
  by (simp only: pp_T4_axioms_def pp_T2_min_axioms_def)

lemma gi_T4_fun_prime_at_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature p \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_fun_prime_at \<sigma> p)"
  by (simp add: pp_fun_prime_at_def pp_pure_def pp_Pure_def gi_goodman_names_def
    gb_signature_def shift_by_def gi_constants_rename)

lemma gi_T4_parameter_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature C \<Longrightarrow>
    gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature
      (Imp (pp_pure pp_T4_C_ty C) (Neg (pp_fun_prime_at pp_unary_ty (App C r))))"
  by (simp add: gi_T4_fun_prime_at_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def)

lemma gi_T4_quantified_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T4_no_higher_fun_prime r)"
  by (simp add: pp_T4_no_higher_fun_prime_def gi_T4_fun_prime_at_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

theorem gi_T4_parameter_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and ct: "\<Gamma> \<turnstile> C : pp_T4_C_ty" and rt: "\<Gamma> \<turnstile> r : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ca: "gi_constants_admitted k gb_signature C" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (Imp (pp_pure pp_T4_C_ty C) (Neg (pp_fun_prime_at pp_unary_ty (App C r)))))"
proof -
  have source: "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_pure pp_T4_C_ty C) (Neg (pp_fun_prime_at pp_unary_ty (App C r)))"
    using CEV_Goodman_T4_parameter[OF subset_refl ct rt] by (simp only: gi_T4_source_stock)
  show ?thesis by (rule gi_T2_min_native_preservation[OF rich names source chart distinct
    gi_T4_parameter_admitted[OF names ca ra]])
qed

theorem gi_T4_quantified_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (pp_T4_no_higher_fun_prime r))"
proof -
  have source: "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T4_no_higher_fun_prime r"
    using CEV_Goodman_T4[OF rt] by (simp only: gi_T4_source_stock)
  show ?thesis by (rule gi_T2_min_native_preservation[OF rich names source chart distinct
    gi_T4_quantified_admitted[OF names ra]])
qed

definition gb_T4_fun_prime_at where
  "gb_T4_fun_prime_at G ns \<sigma> p =
    (let x = named_chart_fresh G ns (Arr \<sigma> Prop);
         y = named_chart_fresh G (x # ns) (Arr \<sigma> Prop)
     in book_all G x (book_all G y
       (book_imp (book_and G (gb_pure (Arr \<sigma> Prop) (NVar x)) (gb_pure (Arr \<sigma> Prop) (NVar y)))
         (book_imp (book_leibniz G Prop (NApp (NVar x) p) (NApp (NVar y) p))
           (book_leibniz G (Arr \<sigma> Prop) (NVar x) (NVar y))))))"

lemma gb_T4_fun_prime_at_proposition:
  "gb_T4_fun_prime_at G ns Prop p = gb_T2a_fun_prime_on_chart G ns p"
  by (simp add: gb_T4_fun_prime_at_def gb_T2a_fun_prime_on_chart_def gb_fun_prime_with_names_def Let_def)

lemma gi_T4_fun_prime_application_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [c, r] k (pp_fun_prime_at \<sigma> (App (Var 0) (Var 1))) =
      gb_T4_fun_prime_at G [c, r] \<sigma> (NApp (NVar c) (NVar r))"
  by (simp add: pp_fun_prime_at_def gb_T4_fun_prime_at_def gi_pure_translation
    Let_def shift_by_def shift_ren_def)

definition gb_T4_claim where
  "gb_T4_claim G r =
    (let c = named_chart_fresh G [r] (Arr Prop gb_unary)
     in book_all G c (book_imp (gb_pure (Arr Prop gb_unary) (NVar c))
       (book_not G (gb_T4_fun_prime_at G [c, r] gb_unary (NApp (NVar c) (NVar r))))))"

lemma gi_T4_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (pp_T4_no_higher_fun_prime (Var 0)) = gb_T4_claim G r"
  by (simp add: pp_T4_no_higher_fun_prime_def gb_T4_claim_def pp_T4_C_ty_def pp_unary_ty_def
    pp_fun_prime_at_def gb_T4_fun_prime_at_def gi_pure_translation Let_def
    shift_def shift_by_def shift_ren_def)

theorem gi_T4_no_higher_fun_prime:
  assumes rich: "sg_rich G" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G) (gb_T4_claim G r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [r] k (pp_T4_no_higher_fun_prime (Var 0)))"
    by (rule gi_T4_quantified_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T4_claim_translation[OF names])
qed

section \<open>T5: conditional proliferation, not a consistency or existence proof\<close>

lemma gi_T5_source_stock:
  "pp_T5_axioms = pp_T6_core_PP_axioms"
  by (simp only: pp_T5_axioms_def)

lemma gi_T5_proliferation_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (pp_T5_proliferation r))"
  by (simp add: pp_T5_proliferation_def gi_T2_fun_prime_admitted shift_def gi_constants_rename)

lemma gi_T5_no_two_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (Neg (pp_T5_two_fun_prime r)))"
  by (simp add: pp_T5_two_fun_prime_def gi_T2_fun_prime_admitted shift_def gi_constants_rename)

theorem gi_T5_proliferation_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_T5_proliferation r)))"
proof -
  have source: "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (pp_T5_proliferation r)"
    using CEV_Goodman_T5[OF rt] by (simp only: gi_T5_source_stock)
  show ?thesis by (rule gi_T2_PP_native_preservation[OF rich names source chart distinct
    gi_T5_proliferation_admitted[OF names ra]])
qed

theorem gi_T5_no_two_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (Neg (pp_T5_two_fun_prime r))))"
proof -
  have source: "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (pp_T5_two_fun_prime r))"
    using CEV_Goodman_T5_no_two_fun_prime[OF subset_refl rt] by (simp only: gi_T5_source_stock)
  show ?thesis by (rule gi_T2_PP_native_preservation[OF rich names source chart distinct
    gi_T5_no_two_admitted[OF names ra]])
qed

lemma gi_T5_fun_prime_head_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G (r # ns) k (pp_fun_prime (Var 0)) = gb_T2a_fun_prime_on_chart G (r # ns) (NVar r)"
  by (simp add: pp_fun_prime_def gb_T2a_fun_prime_on_chart_def gb_fun_prime_with_names_def
    pp_unary_ty_def gi_pure_translation Let_def shift_by_def shift_ren_def)

definition gb_T5_proliferation where
  "gb_T5_proliferation G r =
    (let q = named_chart_fresh G [r] Prop
     in book_exists G q (book_and G (gb_T2a_fun_prime_on_chart G [q, r] (NVar q))
       (book_and G (book_not G (book_leibniz G Prop (NVar q) (NVar r)))
         (book_not G (book_leibniz G Prop (NVar q) (book_not G (NVar r)))))))"

definition gb_T5_two_fun_prime where
  "gb_T5_two_fun_prime G r =
    (let q = named_chart_fresh G [r] Prop
     in book_all G q (book_imp (gb_T2a_fun_prime_on_chart G [q, r] (NVar q))
       (book_or G (book_leibniz G Prop (NVar q) (NVar r))
         (book_leibniz G Prop (NVar q) (book_not G (NVar r))))))"

definition gb_T5_claim where
  "gb_T5_claim G r = book_imp (gb_T2a_fun_prime_on_chart G [r] (NVar r)) (gb_T5_proliferation G r)"

definition gb_T5_no_two_claim where
  "gb_T5_no_two_claim G r = book_imp (gb_T2a_fun_prime_on_chart G [r] (NVar r))
    (book_not G (gb_T5_two_fun_prime G r))"

lemma gi_T5_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (pp_T5_proliferation (Var 0))) = gb_T5_claim G r"
  by (simp add: gb_T5_claim_def pp_T5_proliferation_def gb_T5_proliferation_def
    gi_T5_fun_prime_head_translation Let_def shift_def shift_ren_def)

lemma gi_T5_no_two_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_T5_two_fun_prime (Var 0)))) = gb_T5_no_two_claim G r"
  by (simp add: gb_T5_no_two_claim_def pp_T5_two_fun_prime_def gb_T5_two_fun_prime_def
    gi_T5_fun_prime_head_translation Let_def shift_def shift_ren_def)

theorem gi_T5_proliferation:
  assumes rich: "sg_rich G" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T5_claim G r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (pp_T5_proliferation (Var 0))))"
    by (rule gi_T5_proliferation_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T5_claim_translation[OF names])
qed

theorem gi_T5_no_two:
  assumes rich: "sg_rich G" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T5_no_two_claim G r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_T5_two_fun_prime (Var 0)))))"
    by (rule gi_T5_no_two_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T5_no_two_claim_translation[OF names])
qed

text \<open>
  Every native fun′ occurrence above protects its argument's free names:
  [r] for the free input, [c,r] for Cr, and [q,r] for the existential witness.
  T4 quantifies higher-type predicates, while T5 remains at proposition type.
  T5 yields a third fun′ proposition only under fun′(r); it does not establish
  that this antecedent is satisfiable. No classification principle such as
  L2, Inv, TU, or WI is added. General arbitrary-term conclusions are explicitly
  labelled translated; the final variable-instance conclusions are independently
  written named formulas with proved source correspondences.
\<close>

end
