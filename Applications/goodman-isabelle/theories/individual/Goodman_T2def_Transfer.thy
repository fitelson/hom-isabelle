theory Goodman_T2def_Transfer
  imports Goodman_T2bc_Transfer
begin

section \<open>The PP stock for T2d and T2f\<close>

text \<open>
  T2d and T2f use logical purity, application closure, and PP, represented
  by gb_T6_core. T2e uses only gb_T2_min_axioms, without PP. None of the
  three results assumes Persistence, Exhaustion, Recombination, or the
  existence of a fun′ proposition. Every conclusion retains fun′(r) as
  an antecedent. The different axiom stocks remain visible in the results.
\<close>

theorem gi_T2_PP_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G ns k A)"
proof -
  have image: "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_core_PP_axioms) (gi_to_book G ns k A)"
    by (rule gi_CEV_axiom_preservation[OF rich derivation gi_T6_core_closed chart distinct])
  have native: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T6_core G) (gi_to_book G ns k A)"
    by (rule goodman_book_mono[OF image gi_T6_core_inclusion[OF rich names]])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    native gb_T6_core_language[OF rich]])
qed

section \<open>T2d: fun′ propositions are possibly pure\<close>

lemma gi_T2d_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (ObjDiamond (pp_pure Prop r)))"
  by (simp add: gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def ObjDiamond_def ObjBox_def ObjTrue_def)

theorem gi_T2d_possibly_pure_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (ObjDiamond (pp_pure Prop r))))"
  by (rule gi_T2_PP_native_preservation[OF rich names
    CEV_Goodman_T2d[OF subset_refl typed] chart distinct gi_T2d_admitted[OF names admitted]])

definition gb_T2d_claim where
  "gb_T2d_claim G = book_imp (gb_T2_fun_prime_at G)
    (gb_T2_source_diamond G [gb_x G Prop] (gb_pure Prop (NVar (gb_x G Prop))))"

lemma gi_T2d_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k
      (Imp (pp_fun_prime (Var 0)) (ObjDiamond (pp_pure Prop (Var 0)))) = gb_T2d_claim G"
  by (simp add: gb_T2d_claim_def gi_T2_fun_prime_var_translation
    gi_T2_diamond_translation gi_pure_translation)

theorem gi_T2d_possibly_pure:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T2d_claim G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [gb_x G Prop] = [Prop]" by (simp add: gb_names_type[OF rich])
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [gb_x G Prop] k
      (Imp (pp_fun_prime (Var 0)) (ObjDiamond (pp_pure Prop (Var 0)))))"
    by (rule gi_T2d_possibly_pure_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T2d_claim_translation[OF names])
qed

section \<open>T2e: noncontingency is false but possible\<close>

definition gb_T2_source_box where
  "gb_T2_source_box G ns A = book_leibniz G Prop A (gi_old_top G ns)"

lemma gi_T2_box_translation:
  "gi_to_book G ns k (ObjBox A) = gb_T2_source_box G ns (gi_to_book G ns k A)"
  by (simp add: ObjBox_def gb_T2_source_box_def gi_true_translation)

definition gb_T2_noncontingent where
  "gb_T2_noncontingent G ns r = book_or G
    (gb_T2_source_box G ns r) (gb_T2_source_box G ns (book_not G r))"

definition gb_T2e_false_but_possible where
  "gb_T2e_false_but_possible G ns r = book_and G
    (book_not G (gb_T2_noncontingent G ns r))
    (gb_T2_source_diamond G ns (gb_T2_noncontingent G ns r))"

lemma gi_T2_noncontingent_translation:
  "gi_to_book G ns k (pp_noncontingent r) = gb_T2_noncontingent G ns (gi_to_book G ns k r)"
  by (simp add: pp_noncontingent_def gb_T2_noncontingent_def gi_T2_box_translation)

lemma gi_T2e_false_but_possible_translation:
  "gi_to_book G ns k (pp_T2e_false_but_possible r) =
    gb_T2e_false_but_possible G ns (gi_to_book G ns k r)"
  by (simp add: pp_T2e_false_but_possible_def gb_T2e_false_but_possible_def
    gi_T2_noncontingent_translation gi_T2_diamond_translation)

lemma gi_T2_noncontingent_admitted:
  "gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_noncontingent r)"
  by (simp add: pp_noncontingent_def ObjBox_def ObjTrue_def)

lemma gi_T2e_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (pp_T2e_false_but_possible r))"
  by (simp add: gi_T2_fun_prime_admitted pp_T2e_false_but_possible_def
    gi_T2_noncontingent_admitted ObjDiamond_def ObjBox_def ObjTrue_def)

theorem gi_T2e_false_but_possible_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_T2e_false_but_possible r)))"
  by (rule gi_T2_min_native_preservation[OF rich names
    CEV_Goodman_T2e[OF subset_refl typed] chart distinct gi_T2e_admitted[OF names admitted]])

definition gb_T2e_claim where
  "gb_T2e_claim G = book_imp (gb_T2_fun_prime_at G)
    (gb_T2e_false_but_possible G [gb_x G Prop] (NVar (gb_x G Prop)))"

lemma gi_T2e_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (pp_T2e_false_but_possible (Var 0))) = gb_T2e_claim G"
  by (simp add: gb_T2e_claim_def gi_T2_fun_prime_var_translation
    gi_T2e_false_but_possible_translation)

theorem gi_T2e_false_but_possible:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G) (gb_T2e_claim G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [gb_x G Prop] = [Prop]" by (simp add: gb_names_type[OF rich])
  have translated: "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (pp_T2e_false_but_possible (Var 0))))"
    by (rule gi_T2e_false_but_possible_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T2e_claim_translation[OF names])
qed

section \<open>T2f: the full conjunction of fifteen object-language inequalities\<close>

text \<open>
  Put t = ⊤₀, f = ¬⊤₀, n = ¬r, a = (r = t), and b = (r = f).
  The source list is [t,f,r,n,a,b]. The formula below spells out all fifteen
  inequalities in lexicographic order. It is an object-language conjunction
  of negated Leibniz identities, not HOL list distinctness or syntactic
  inequality of terms. The local abbreviation neq merely constructs that
  object-language formula; it is not a predicate on semantic denotations.
\<close>

definition gb_T2f_six_distinct where
  "gb_T2f_six_distinct G ns r =
    (let t = gi_old_top G ns; f = book_not G t; n = book_not G r;
         a = book_leibniz G Prop r t; b = book_leibniz G Prop r f;
         neq = (\<lambda>x y. book_not G (book_leibniz G Prop x y))
     in book_and G (neq t f)
       (book_and G (neq t r)
       (book_and G (neq t n)
       (book_and G (neq t a)
       (book_and G (neq t b)
       (book_and G (neq f r)
       (book_and G (neq f n)
       (book_and G (neq f a)
       (book_and G (neq f b)
       (book_and G (neq r n)
       (book_and G (neq r a)
       (book_and G (neq r b)
       (book_and G (neq n a)
       (book_and G (neq n b) (neq a b)))))))))))))))"

lemma gi_T2f_six_distinct_translation:
  "gi_to_book G ns k (pp_T2f_six_distinct r) =
    gb_T2f_six_distinct G ns (gi_to_book G ns k r)"
  by (simp add: pp_T2f_six_distinct_def gb_T2f_six_distinct_def ObjFalse_def
    gi_true_translation Let_def)

lemma gi_T2f_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (pp_T2f_six_distinct r))"
  by (simp add: gi_T2_fun_prime_admitted pp_T2f_six_distinct_def ObjTrue_def ObjFalse_def)

theorem gi_T2f_six_distinct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_T2f_six_distinct r)))"
  by (rule gi_T2_PP_native_preservation[OF rich names
    CEV_Goodman_T2f[OF subset_refl typed] chart distinct gi_T2f_admitted[OF names admitted]])

definition gb_T2f_claim where
  "gb_T2f_claim G = book_imp (gb_T2_fun_prime_at G)
    (gb_T2f_six_distinct G [gb_x G Prop] (NVar (gb_x G Prop)))"

lemma gi_T2f_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (pp_T2f_six_distinct (Var 0))) = gb_T2f_claim G"
  by (simp add: gb_T2f_claim_def gi_T2_fun_prime_var_translation gi_T2f_six_distinct_translation)

theorem gi_T2f_six_distinct:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T2f_claim G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [gb_x G Prop] = [Prop]" by (simp add: gb_names_type[OF rich])
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [gb_x G Prop] k (Imp (pp_fun_prime (Var 0))
      (pp_T2f_six_distinct (Var 0))))"
    by (rule gi_T2f_six_distinct_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T2f_claim_translation[OF names])
qed

text \<open>
  The final three theorems have independently written named conclusions
  with the free proposition r = gb_x G Prop and the previously verified fresh
  unary binders for fun′. They use the source representatives of truth,
  falsity, necessity, and possibility; no canonical-representative identity is
  assumed. The general parameter versions remain explicitly translated.
  None of these conditional results proves that a fun′ proposition exists
  or that either axiom stock is consistent.
\<close>

end
