theory Goodman_T2a_Transfer
  imports Goodman_T2def_Transfer
begin

section \<open>T2a: closure under pure reversible operators\<close>

text \<open>
  The three conclusions are
  Reversible(Z) → ((fun′(r) ∧ Pure(Z)) → fun′(Zr)),
  (fun′(r) ∧ Group(Z)) → fun′(Zr), and fun′(r) → fun′(¬r).
  Reversible(Z) includes a pure two-sided inverse. Group(Z) additionally
  says that Z itself is pure. All proofs here retain the original stock
  of logical purity, application closure, and PP. We do not claim that
  PP is necessary, or that this is the weakest possible stock.
\<close>

lemma gi_T2a_reversible_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature Z \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_reversible Z)"
  by (simp add: pp_reversible_def pp_compose_def pp_identity_operator_def
    pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def
    shift_def gi_constants_rename)

lemma gi_T2a_group_member_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature Z \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_group_member Z)"
  by (simp add: pp_group_member_def gi_T2a_reversible_admitted
    pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def)

theorem gi_T2a_reversible_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and za: "gi_constants_admitted k gb_signature Z"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_reversible Z)
      (Imp (Conj (pp_fun_prime r) (pp_pure pp_unary_ty Z)) (pp_fun_prime (App Z r)))))"
proof (rule gi_T2_PP_native_preservation[OF rich names
    CEV_fun_prime_under_reversible[OF subset_refl rt zt] chart distinct])
  show "gi_constants_admitted k gb_signature (Imp (pp_reversible Z)
      (Imp (Conj (pp_fun_prime r) (pp_pure pp_unary_ty Z)) (pp_fun_prime (App Z r))))"
    using names ra za
    by (simp add: gi_T2a_reversible_admitted gi_T2_fun_prime_admitted
      pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def)
qed

theorem gi_T2a_group_member_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and za: "gi_constants_admitted k gb_signature Z"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (Conj (pp_fun_prime r) (pp_group_member Z)) (pp_fun_prime (App Z r))))"
proof (rule gi_T2_PP_native_preservation[OF rich names
    CEV_fun_prime_under_group_member[OF subset_refl rt zt] chart distinct])
  show "gi_constants_admitted k gb_signature
    (Imp (Conj (pp_fun_prime r) (pp_group_member Z)) (pp_fun_prime (App Z r)))"
    using names ra za by (simp add: gi_T2a_group_member_admitted gi_T2_fun_prime_admitted)
qed

theorem gi_T2a_negation_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_fun_prime (Neg r))))"
proof (rule gi_T2_PP_native_preservation[OF rich names
    CEV_fun_prime_under_negation[OF subset_refl rt] chart distinct])
  show "gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) (pp_fun_prime (Neg r)))"
    using names ra by (simp add: gi_T2_fun_prime_admitted)
qed

section \<open>Native operators with explicit fresh binder charts\<close>

definition gb_T2a_fun_prime_on_chart where
  "gb_T2a_fun_prime_on_chart G ns p =
    (let x = named_chart_fresh G ns gb_unary;
         y = named_chart_fresh G (x # ns) gb_unary
     in gb_fun_prime_with_names G x y p)"

lemma gb_T2a_fun_prime_chart_fresh:
  fixes ns :: "nat list"
  assumes rich: "sg_rich G"
  shows "G (named_chart_fresh G ns gb_unary) = gb_unary"
    "G (named_chart_fresh G (named_chart_fresh G ns gb_unary # ns) gb_unary) = gb_unary"
    "named_chart_fresh G ns gb_unary \<notin> set ns"
    "named_chart_fresh G (named_chart_fresh G ns gb_unary # ns) gb_unary
      \<notin> insert (named_chart_fresh G ns gb_unary) (set ns)"
proof -
  show "G (named_chart_fresh G ns gb_unary) = gb_unary"
    by (rule named_chart_fresh_type[OF rich])
  show "G (named_chart_fresh G (named_chart_fresh G ns gb_unary # ns) gb_unary) = gb_unary"
    by (rule named_chart_fresh_type[OF rich])
  show "named_chart_fresh G ns gb_unary \<notin> set ns"
    by (rule named_chart_fresh_notin[OF rich])
  show "named_chart_fresh G (named_chart_fresh G ns gb_unary # ns) gb_unary
      \<notin> insert (named_chart_fresh G ns gb_unary) (set ns)"
    using named_chart_fresh_notin[OF rich,
      where ns="named_chart_fresh G ns gb_unary # ns" and \<sigma>=gb_unary] by simp
qed

definition gb_T2a_reversible where
  "gb_T2a_reversible G ns Z =
    (let i = named_chart_fresh G ns gb_unary;
         p = named_chart_fresh G (i # ns) Prop;
         ident = NLam p (NVar p);
         zi = NLam p (NApp Z (NApp (NVar i) (NVar p)));
         iz = NLam p (NApp (NVar i) (NApp Z (NVar p)))
     in book_exists G i (book_and G (gb_pure gb_unary (NVar i))
       (book_and G (book_leibniz G gb_unary zi ident) (book_leibniz G gb_unary iz ident))))"

definition gb_T2a_group_member where
  "gb_T2a_group_member G ns Z = book_and G (gb_pure gb_unary Z) (gb_T2a_reversible G ns Z)"

text \<open>
  These builders avoid the names in ns. For their intended reading, ns
  must contain the free names of the displayed arguments. The native
  theorem instances below use ns = [z,r], Z = z, and p = r or zr;
  the negation instance uses ns = [r]. Thus all free argument names are
  explicitly protected from the newly introduced binders.
\<close>

lemma gi_T2a_fun_prime_var1_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (pp_fun_prime (Var 1)) = gb_T2a_fun_prime_on_chart G [z, r] (NVar r)"
  by (simp add: pp_fun_prime_def gb_T2a_fun_prime_on_chart_def gb_fun_prime_with_names_def
    pp_unary_ty_def gi_pure_translation Let_def shift_by_def shift_ren_def)

lemma gi_T2a_fun_prime_application_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (pp_fun_prime (App (Var 0) (Var 1))) =
      gb_T2a_fun_prime_on_chart G [z, r] (NApp (NVar z) (NVar r))"
  by (simp add: pp_fun_prime_def gb_T2a_fun_prime_on_chart_def gb_fun_prime_with_names_def
    pp_unary_ty_def gi_pure_translation Let_def shift_by_def shift_ren_def)

lemma gi_T2a_reversible_var_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (pp_reversible (Var 0)) = gb_T2a_reversible G [z, r] (NVar z)"
  by (simp add: pp_reversible_def pp_compose_def pp_identity_operator_def gb_T2a_reversible_def
    pp_unary_ty_def gi_pure_translation Let_def shift_def shift_ren_def)

lemma gi_T2a_group_member_var_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (pp_group_member (Var 0)) = gb_T2a_group_member G [z, r] (NVar z)"
  by (simp add: pp_group_member_def gb_T2a_group_member_def gi_pure_translation
    gi_T2a_reversible_var_translation pp_unary_ty_def)

definition gb_T2a_reversible_claim where
  "gb_T2a_reversible_claim G z r =
    book_imp (gb_T2a_reversible G [z, r] (NVar z))
      (book_imp (book_and G (gb_T2a_fun_prime_on_chart G [z, r] (NVar r))
        (gb_pure gb_unary (NVar z)))
        (gb_T2a_fun_prime_on_chart G [z, r] (NApp (NVar z) (NVar r))))"

definition gb_T2a_group_member_claim where
  "gb_T2a_group_member_claim G z r =
    book_imp (book_and G (gb_T2a_fun_prime_on_chart G [z, r] (NVar r))
      (gb_T2a_group_member G [z, r] (NVar z)))
      (gb_T2a_fun_prime_on_chart G [z, r] (NApp (NVar z) (NVar r)))"

lemma gi_T2a_reversible_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (Imp (pp_reversible (Var 0))
      (Imp (Conj (pp_fun_prime (Var 1)) (pp_pure pp_unary_ty (Var 0)))
        (pp_fun_prime (App (Var 0) (Var 1))))) = gb_T2a_reversible_claim G z r"
  by (simp only: gb_T2a_reversible_claim_def gi_to_book.simps gi_T2a_reversible_var_translation
    gi_T2a_fun_prime_var1_translation gi_T2a_fun_prime_application_translation
    gi_pure_translation pp_unary_ty_def; simp)

lemma gi_T2a_group_member_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [z, r] k (Imp (Conj (pp_fun_prime (Var 1)) (pp_group_member (Var 0)))
      (pp_fun_prime (App (Var 0) (Var 1)))) = gb_T2a_group_member_claim G z r"
  by (simp only: gb_T2a_group_member_claim_def gi_to_book.simps gi_T2a_group_member_var_translation
    gi_T2a_fun_prime_var1_translation gi_T2a_fun_prime_application_translation; simp)

theorem gi_T2a_reversible:
  assumes rich: "sg_rich G" and zt: "G z = gb_unary" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T2a_reversible_claim G z r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have r_type: "[pp_unary_ty, Prop] \<turnstile> Var 1 : Prop"
    and z_type: "[pp_unary_ty, Prop] \<turnstile> Var 0 : pp_unary_ty"
    by (rule has_type.Var; simp add: lookup_def)+
  have chart: "map G [z, r] = [pp_unary_ty, Prop]" using zt rt by (simp add: pp_unary_ty_def)
  have distinct: "distinct [z, r]" using zt rt by auto
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [z, r] k (Imp (pp_reversible (Var 0))
      (Imp (Conj (pp_fun_prime (Var 1)) (pp_pure pp_unary_ty (Var 0)))
        (pp_fun_prime (App (Var 0) (Var 1))))))"
    by (rule gi_T2a_reversible_translated[OF rich names r_type z_type chart distinct]; simp)
  show ?thesis using translated by (simp only: gi_T2a_reversible_claim_translation[OF names])
qed

theorem gi_T2a_group_member:
  assumes rich: "sg_rich G" and zt: "G z = gb_unary" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T2a_group_member_claim G z r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have r_type: "[pp_unary_ty, Prop] \<turnstile> Var 1 : Prop"
    and z_type: "[pp_unary_ty, Prop] \<turnstile> Var 0 : pp_unary_ty"
    by (rule has_type.Var; simp add: lookup_def)+
  have chart: "map G [z, r] = [pp_unary_ty, Prop]" using zt rt by (simp add: pp_unary_ty_def)
  have distinct: "distinct [z, r]" using zt rt by auto
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [z, r] k (Imp (Conj (pp_fun_prime (Var 1)) (pp_group_member (Var 0)))
      (pp_fun_prime (App (Var 0) (Var 1)))))"
    by (rule gi_T2a_group_member_translated[OF rich names r_type z_type chart distinct]; simp)
  show ?thesis using translated by (simp only: gi_T2a_group_member_claim_translation[OF names])
qed

section \<open>The negation instance\<close>

definition gb_T2a_negation_claim where
  "gb_T2a_negation_claim G r =
    book_imp (gb_T2a_fun_prime_on_chart G [r] (NVar r))
      (gb_T2a_fun_prime_on_chart G [r] (book_not G (NVar r)))"

lemma gi_T2a_negation_claim_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (pp_fun_prime (Neg (Var 0)))) =
      gb_T2a_negation_claim G r"
  by (simp add: gb_T2a_negation_claim_def pp_fun_prime_def gb_T2a_fun_prime_on_chart_def
    gb_fun_prime_with_names_def pp_unary_ty_def gi_pure_translation Let_def shift_by_def shift_ren_def)

theorem gi_T2a_negation:
  assumes rich: "sg_rich G" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_T2a_negation_claim G r)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have r_type: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (pp_fun_prime (Neg (Var 0)))))"
    by (rule gi_T2a_negation_translated[OF rich names r_type chart]; simp)
  show ?thesis using translated by (simp only: gi_T2a_negation_claim_translation[OF names])
qed

text \<open>
  The native variable-instance formulas are separately defined and identified
  with the translated source formulas. Arbitrary-term endpoints remain labelled
  translated: replacing their binder charts by independently chosen names would
  require further α-conversion lemmas. No existence of a fun′ proposition,
  consistency result, or PP-free strengthening is claimed here.
\<close>

end
