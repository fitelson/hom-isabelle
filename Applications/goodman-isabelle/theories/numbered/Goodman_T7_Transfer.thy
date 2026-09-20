theory Goodman_T7_Transfer
  imports Goodman_Legacy_T7.Bacon_PP_Goodman_T7_Absorption
    Goodman_Integration_Individual.Goodman_T45_Transfer
begin

section \<open>T7a keeps L2 but adds no classification of reversible operators\<close>

text \<open>
  For D(p) = ∀Xq.((Pure(X) ∧ fun′(q) ∧ p = Xq) → ¬Xp), put d = D(r).
  T7a says fun′(r) → (¬D(d) ∧ ∃Z.(Group(Z) ∧ D(Zd))). The identity member
  of this family is false and some pure reversible member is true.
  The source stock is the purity/application/PP core plus L2; the closed
  existence result also assumes ∃r.fun′(r). Inv, TU, and WI are not premises,
  even though the source import chain includes their separate developments.
\<close>

definition gi_T7_native_axioms where
  "gi_T7_native_axioms G k = insert (gi_to_book G [] k pp_L2) (gb_T6_core G)"

definition gi_T7_native_full_axioms where
  "gi_T7_native_full_axioms G k = insert (gb_exists_fun_prime G) (gi_T7_native_axioms G k)"

lemma gi_T7_axioms_closed:
  "A \<in> pp_T7_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T7_axioms_def by (auto intro: gi_T6_core_closed typed_pp_L2)

lemma gi_T7_full_axioms_closed:
  "A \<in> pp_T7_full_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T7_full_axioms_def by (auto intro: gi_T7_axioms_closed typed_pp_exists_fun_prime)

lemma gi_T7_native_axioms_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> gi_T7_native_axioms G k"
  shows "book_theory_formula gb_signature G A"
proof -
  have l2: "book_theory_formula gb_signature G (gi_to_book G [] k pp_L2)"
    by (rule gi_to_book_language[OF rich typed_pp_L2 _ gi_L2_admitted[OF names]]; simp)
  show ?thesis using member unfolding gi_T7_native_axioms_def
    by (auto intro: l2 gb_T6_core_language[OF rich])
qed

lemma gi_T7_native_full_axioms_language:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> A \<in> gi_T7_native_full_axioms G k \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gi_T7_native_full_axioms_def
  by (auto intro: gb_exists_fun_prime_language gi_T7_native_axioms_language)

lemma gi_T7_stock_inclusion:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_T7_axioms \<subseteq> gi_T7_native_axioms G k"
  unfolding pp_T7_axioms_def gi_T7_native_axioms_def image_insert
  using gi_T6_core_inclusion by blast

lemma gi_T7_full_stock_inclusion:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_T7_full_axioms \<subseteq> gi_T7_native_full_axioms G k"
  unfolding pp_T7_full_axioms_def gi_T7_native_full_axioms_def image_insert
  using gi_T7_stock_inclusion gi_exists_fun_prime_translation by blast

lemma gi_T7_liar_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_T6_liar"
  by (simp add: pp_T6_liar_def gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def)

lemma gi_T7_absorbed_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T7_absorbed r)"
  by (simp add: pp_T7_absorbed_def gi_T7_liar_admitted gi_T2a_group_member_admitted
    shift_def gi_constants_rename)

lemma gi_T7_parameter_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (Imp (pp_fun_prime r)
      (Conj (Neg (App pp_T6_liar (App pp_T6_liar r))) (pp_T7_absorbed r)))"
  by (simp add: gi_T2_fun_prime_admitted gi_T7_liar_admitted gi_T7_absorbed_admitted)

lemma gi_T7_result_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_T7_absorption_result"
  by (simp add: pp_T7_absorption_result_def gi_T2_fun_prime_admitted gi_T7_liar_admitted gi_T7_absorbed_admitted)

theorem gi_T7a_parameter_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gi_T7_native_axioms G k)
    (gi_to_book G ns k (Imp (pp_fun_prime r)
      (Conj (Neg (App pp_T6_liar (App pp_T6_liar r))) (pp_T7_absorbed r))))"
proof -
  let ?A = "Imp (pp_fun_prime r)
    (Conj (Neg (App pp_T6_liar (App pp_T6_liar r))) (pp_T7_absorbed r))"
  have source: "\<Gamma> ; pp_T7_axioms \<turnstile>\<^sub>CEV\<^sup>+ ?A"
    by (rule CEV_Goodman_T7a_parameter[OF subset_refl rt])
  have image: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) pp_T7_axioms)
    (gi_to_book G ns k ?A)"
    by (rule gi_CEV_axiom_preservation[OF rich source gi_T7_axioms_closed chart distinct])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gi_T7_native_axioms G k) (gi_to_book G ns k ?A)"
    by (rule goodman_book_mono[OF image gi_T7_stock_inclusion[OF rich names]])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich source chart
    gi_T7_parameter_admitted[OF names ra] universal gi_T7_native_axioms_language[OF rich names]])
qed

theorem gi_T7a_closed_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_native_full_axioms G k)
    (gi_to_book G [] k pp_T7_absorption_result)"
proof -
  have image: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) pp_T7_full_axioms)
    (gi_to_book G [] k pp_T7_absorption_result)"
    by (rule gi_CEV_axiom_preservation[OF rich CEV_Goodman_T7a gi_T7_full_axioms_closed]; simp)
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gi_T7_native_full_axioms G k)
    (gi_to_book G [] k pp_T7_absorption_result)"
    by (rule goodman_book_mono[OF image gi_T7_full_stock_inclusion[OF rich names]])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich CEV_Goodman_T7a _
    gi_T7_result_admitted[OF names] universal gi_T7_native_full_axioms_language[OF rich names]]; simp)
qed

section \<open>Independent named definitions of the liar and its family\<close>

definition gb_T7_liar where
  "gb_T7_liar G ns =
    (let p = named_chart_fresh G ns Prop;
         x = named_chart_fresh G (p # ns) gb_unary;
         q = named_chart_fresh G (x # p # ns) Prop
     in NLam p (book_all G x (book_all G q
       (book_imp (book_and G (gb_pure gb_unary (NVar x))
         (book_and G (gb_T2a_fun_prime_on_chart G (q # x # p # ns) (NVar q))
           (book_leibniz G Prop (NVar p) (NApp (NVar x) (NVar q)))))
         (book_not G (NApp (NVar x) (NVar p)))))))"

lemma gi_T7_liar_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k pp_T6_liar = gb_T7_liar G ns"
  by (simp add: pp_T6_liar_def gb_T7_liar_def gi_T5_fun_prime_head_translation
    gi_pure_translation pp_unary_ty_def Let_def)

definition gb_T7_absorbed where
  "gb_T7_absorbed G r =
    (let z = named_chart_fresh G [r] gb_unary; d = gb_T7_liar G [z, r]
     in book_exists G z (book_and G (gb_T2a_group_member G [z, r] (NVar z))
       (NApp d (NApp (NVar z) (NApp d (NVar r))))))"

lemma gi_T7_absorbed_var_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (pp_T7_absorbed (Var 0)) = gb_T7_absorbed G r"
  by (simp add: pp_T7_absorbed_def gb_T7_absorbed_def gi_T2a_group_member_var_translation
    gi_T7_liar_translation pp_unary_ty_def Let_def shift_def shift_ren_def)

definition gb_T7_parameter_claim where
  "gb_T7_parameter_claim G r =
    (let d = gb_T7_liar G [r]
     in book_imp (gb_T2a_fun_prime_on_chart G [r] (NVar r))
       (book_and G (book_not G (NApp d (NApp d (NVar r)))) (gb_T7_absorbed G r)))"

definition gb_T7_absorption_result where
  "gb_T7_absorption_result G =
    (let r = gb_x G Prop; d = gb_T7_liar G [r]
     in book_exists G r (book_and G (gb_T2a_fun_prime_on_chart G [r] (NVar r))
       (book_and G (book_not G (NApp d (NApp d (NVar r)))) (gb_T7_absorbed G r))))"

lemma gi_T7_parameter_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (Imp (pp_fun_prime (Var 0))
      (Conj (Neg (App pp_T6_liar (App pp_T6_liar (Var 0)))) (pp_T7_absorbed (Var 0)))) =
        gb_T7_parameter_claim G r"
  by (simp add: gb_T7_parameter_claim_def gi_T5_fun_prime_head_translation gi_T7_liar_translation
    gi_T7_absorbed_var_translation Let_def)

lemma gi_T7_absorption_result_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_T7_absorption_result = gb_T7_absorption_result G"
  by (simp add: pp_T7_absorption_result_def gb_T7_absorption_result_def gi_T5_fun_prime_head_translation
    gi_T7_liar_translation gi_T7_absorbed_var_translation gb_x_def[symmetric] Let_def)

theorem gi_T7a_parameter:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gi_T7_native_axioms G k) (gb_T7_parameter_claim G r)"
proof -
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gi_T7_native_axioms G k)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0))
      (Conj (Neg (App pp_T6_liar (App pp_T6_liar (Var 0)))) (pp_T7_absorbed (Var 0)))))"
    by (rule gi_T7a_parameter_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp only: gi_T7_parameter_claim_translation[OF names])
qed

theorem gi_T7a_closed:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_native_full_axioms G k) (gb_T7_absorption_result G)"
  using gi_T7a_closed_translated[OF rich names]
  by (simp only: gi_T7_absorption_result_translation[OF names])

section \<open>Derive the witness from the repaired central stock\<close>

definition gi_T7_repaired_native_axioms where
  "gi_T7_repaired_native_axioms G k =
    insert (gi_to_book G [] k pp_L2) (gb_recombination_PP_zeroary_exhaustion G)"

lemma gi_T7_native_core_in_repaired:
  "gi_T7_native_axioms G k \<subseteq> gi_T7_repaired_native_axioms G k"
  unfolding gi_T7_native_axioms_def gi_T7_repaired_native_axioms_def gb_T6_core_def
    gb_recombination_PP_zeroary_exhaustion_def gb_recombination_PP_axioms_def
    gb_recombination_background_def gb_background_axioms_def by blast

theorem gi_T7a_repaired_central_stock:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_repaired_native_axioms G k) (gb_T7_absorption_result G)"
proof (rule goodman_book_cut[OF gi_T7a_closed[OF rich names]])
  fix A assume member: "A \<in> gi_T7_native_full_axioms G k"
  show "goodman_book_proves gb_signature G (gi_T7_repaired_native_axioms G k) A"
  proof (cases "A = gb_exists_fun_prime G")
    case True
    show ?thesis unfolding True
      by (rule goodman_book_mono[OF gi_repaired_native_exists_fun_prime[OF rich]];
        auto simp: gi_T7_repaired_native_axioms_def)
  next
    case False
    have old: "A \<in> gi_T7_native_axioms G k"
      using member False unfolding gi_T7_native_full_axioms_def by blast
    have new: "A \<in> gi_T7_repaired_native_axioms G k"
      using old gi_T7_native_core_in_repaired by blast
    show ?thesis by (rule goodman_book_proves.Axiom[OF new gi_T7_native_axioms_language[OF rich names old]])
  qed
qed

text \<open>
  L2 remains an explicitly translated extra principle in every stock above.
  The independently written native conclusions include the liar and the
  pure-reversible witness condition; their binder charts change with context
  exactly as in the original terms. Identifying the closed liar across those
  charts up to α-conversion is unnecessary for these literal source matches.

  The final result replaces the separate ∃fun′ axiom by the checked native
  bridge. It thereby adds the repaired central assumptions, notably unique
  fundamentality, Recombination, and zeroary Exhaustion; it does not derive
  the witness from the smaller PP common core alone. No classification axiom
  Inv/TU/WI or consistency claim has been introduced. T7b remains underspecified
  in the source notes and no substitute theorem is invented here.
\<close>

end
