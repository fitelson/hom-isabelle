theory Goodman_PP_Refutation_Packaging
  imports "Goodman_Integration_PP_Refutation_Theorem1.Goodman_PP_Refutation_Theorem1"
begin

text \<open>
  BEYOND THE NOTE: REPOSITORY PACKAGING.  Nothing in this theory is part of
  the hand proof.  It restates Theorem 1 of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close> over the
  application's named stocks and transfers the refutation to the native
  Goodman book calculus through the application's existing pipeline
  (\<open>gi_CEV_closed_refutation\<close>, \<open>gi_recombination_package_support\<close>,
  \<open>gi_goodman_foreign_constants_eliminate\<close>), following the template of
  \<open>gi_central_T6_refutation_transfer\<close>.
\<close>

section \<open>The note's theory \<open>\<T>\<close> and the application's stocks\<close>

text \<open>\<open>\<T>\<close> is literally the application's T6 PP core.\<close>

lemma gr_Th_eq_T6_core: "gr_Th = pp_T6_core_PP_axioms"
  by (simp add: gr_Th_def gr_T0_def pp_T6_core_PP_axioms_def)

lemma gr_Th_sub_recombination: "gr_Th \<subseteq> pp_recombination_PP_axioms"
  by (auto simp: gr_Th_def gr_T0_def pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

section \<open>Constructor calculus\<close>

text \<open>The fun' consequence over the T6 PP core.\<close>

theorem gr_T6_core_no_fun_prime:
  "[] ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ Neg pp_exists_fun_prime"
  by (rule gr_Theorem1_funp) (simp add: gr_Th_eq_T6_core)

text \<open>
  The Recombination-with-PP stock is inconsistent: its unique-fundamental
  axiom supplies \<open>\<exists>r Fun(r)\<close>, which Theorem 1 (third assertion) refutes.
  Only the existence part of unique fundamentality is used.
\<close>

theorem gr_recombination_PP_refutation:
  "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?T = "pp_recombination_PP_axioms"
  let ?U = "Conj (pp_fun Prop (Var 0))
      (Forall Prop (Imp (pp_fun Prop (Var 0)) (Eq Prop (Var 0) (Var 1))))"
  have nf: "[] ; ?T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Exists Prop (pp_fun Prop (Var 0)))"
    by (rule gr_Theorem1_Fun[OF gr_Th_sub_recombination
          pp_unary_recombination_in_recombination])
  have uf: "[] ; ?T \<turnstile>\<^sub>CEV\<^sup>+ pp_unique_fundamental Prop"
    by (rule CEV_axiom_proves.Axiom[OF pp_unique_fundamental_is_assumed_recombination
          typed_pp_unique_fundamental])
  have ut: "[Prop] \<turnstile> ?U : Prop"
    by (rule grk_ExistsD[OF typed_pp_unique_fundamental[of Prop,
          unfolded pp_unique_fundamental_def]])
  have "[Prop] ; ?T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?U (pp_fun Prop (Var 0))"
    by (rule grk_taut[OF has_type.Imp[OF ut grk_ConjD1[OF ut]]]) gr_taut
  then have ex: "[] ; ?T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_unique_fundamental Prop) (Exists Prop (pp_fun Prop (Var 0)))"
    unfolding pp_unique_fundamental_def by (rule grk_exists_mono)
  show ?thesis by (rule grk_PC3[OF nf uf ex typed_ObjFalse]) gr_taut
qed

text \<open>Hence also the full (zeroary and unary) QLN stock, by monotonicity.\<close>

theorem gr_full_QLN_PP_refutation:
  "[] ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  by (rule CEV_axiom_proves_mono[OF gr_recombination_PP_refutation
        pp_recombination_PP_axioms_subset_full_QLN])

text \<open>The application's two consistency questions are answered negatively.\<close>

theorem gr_recombination_question_negative:
  "\<not> pp_recombination_axiom_consistency_question"
  unfolding pp_recombination_axiom_consistency_question_def CEV_axiom_consistent_def
  using gr_recombination_PP_refutation by blast

theorem gr_full_QLN_question_negative:
  "\<not> pp_full_QLN_axiom_consistency_question"
  unfolding pp_full_QLN_axiom_consistency_question_def CEV_axiom_consistent_def
  using gr_full_QLN_PP_refutation by blast

section \<open>Native Goodman book calculus\<close>

text \<open>
  The native stock is literally \<open>gb_recombination_PP_axioms G\<close>: the image of
  the constructor stock under the translation is cut against it with the
  existing support lemma \<open>gi_recombination_package_support\<close>.  The only
  hypothesis is that the variable signature \<open>G\<close> is rich (\<open>sg_rich G\<close>); the
  name map \<open>k\<close> is chosen by \<open>gi_goodman_names_satisfiable\<close> and does not
  occur in the statement.
\<close>

theorem gr_native_recombination_PP_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_axioms G) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k"
    using gi_goodman_names_satisfiable by blast
  have image: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) pp_recombination_PP_axioms) (book_bottom G)"
    by (rule gi_CEV_closed_refutation[OF rich gr_recombination_PP_refutation
          pp_recombination_PP_axioms_typed])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G
      (gb_recombination_PP_axioms G) (book_bottom G)"
    by (rule goodman_book_cut[OF image])
      (auto intro: gi_recombination_package_support[OF rich names subset_refl])
  show ?thesis
  proof (rule gi_goodman_foreign_constants_eliminate[OF rich universal])
    fix B assume "B \<in> gb_recombination_PP_axioms G"
    then show "book_theory_formula gb_signature G B"
      by (rule gb_recombination_PP_language[OF rich])
  next
    show "named_in_signature gb_signature (book_bottom G)"
      by (rule book_language_signature[OF book_bottom_language[OF rich]])
  qed
qed

theorem gr_native_recombination_PP_inconsistent:
  assumes rich: "sg_rich G"
  shows "\<not> goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G)"
  unfolding goodman_book_consistent_def
  using gr_native_recombination_PP_refutation[OF rich] by blast

theorem gr_native_QLN_PP_inconsistent:
  assumes rich: "sg_rich G"
  shows "\<not> goodman_book_consistent gb_signature G (gb_zeroary_unary_QLN_PP_axioms G)"
  using gb_QLN_consistency_implies_recombination_consistency
    gr_native_recombination_PP_inconsistent[OF rich] by blast

theorem gr_native_QLN_PP_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_zeroary_unary_QLN_PP_axioms G) (book_bottom G)"
  using gr_native_QLN_PP_inconsistent[OF rich]
  unfolding goodman_book_consistent_def by blast

text \<open>
  A native statement of the fun' consequence, over the independently written
  native T6 PP core \<open>gb_T6_core G\<close> (purity schema, application schema, PP):
  it proves the negation of the native sentence \<open>gb_exists_fun_prime G\<close>.
\<close>

theorem gr_native_T6_core_no_fun_prime:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (book_not G (gb_exists_fun_prime G))"
proof -
  obtain k where names: "gi_goodman_names k"
    using gi_goodman_names_satisfiable by blast
  let ?A = "Neg pp_exists_fun_prime"
  have d: "[] ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ ?A" by (rule gr_T6_core_no_fun_prime)
  have chart: "map G [] = []" by simp
  have pres: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) pp_T6_core_PP_axioms) (gi_to_book G [] k ?A)"
    by (rule gi_CEV_axiom_preservation[OF rich d gi_T6_core_closed chart]) simp_all
  have nat: "goodman_book_proves (\<lambda>_. UNIV) G (gb_T6_core G) (gi_to_book G [] k ?A)"
    by (rule goodman_book_mono[OF pres gi_T6_core_inclusion[OF rich names]])
  have adm: "gi_constants_admitted k gb_signature ?A"
    using gi_exists_fun_prime_admitted[OF names] by simp
  have "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G [] k ?A)"
    by (rule gi_native_conclusion_restrict[OF rich d chart adm nat gb_T6_core_language[OF rich]])
  then show ?thesis by (simp add: gi_exists_fun_prime_translation[OF names])
qed

end
