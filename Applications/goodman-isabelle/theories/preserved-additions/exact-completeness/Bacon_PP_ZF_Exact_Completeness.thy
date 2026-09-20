theory Bacon_PP_ZF_Exact_Completeness
  imports 
    "Goodman_Exact_Enumeration.Bacon_PP_ZF_Exact_Enumeration"
begin

section \<open>Possibility and necessity in Bacon's exact model\<close>

lemma pp_e_ObjBox_true_iff:
  "pp_e_true_in C (\<box>\<^sub>o A) \<longleftrightarrow>
    (\<forall>w. pp_e_holds (pp_e_eval C pp_e_closed_env A) w)"
  unfolding pp_e_true_in_def
  by (simp add: pp_e_eval_ObjBox_holds pp_e_prop_eqv_truth_iff)

lemma pp_e_ObjDiamond_true_iff:
  "pp_e_true_in C (\<diamond>\<^sub>o A) \<longleftrightarrow>
    (\<exists>w. pp_e_holds (pp_e_eval C pp_e_closed_env A) w)"
  unfolding ObjDiamond_def pp_e_true_in_def
  by (simp add: pp_e_eval_ObjBox_holds pp_e_prop_eqv_truth_iff)

section \<open>Bacon's consistency representation theorem\<close>

theorem pp_e_Bacon_consistency_representation:
  assumes sentence: "pp_e_sentence S A"
  shows "pp_e_frame_consistent S A \<longleftrightarrow>
    pp_e_true_in (pp_e_complete_constants S) (\<diamond>\<^sub>o A)"
proof
  assume consistent: "pp_e_frame_consistent S A"
  have member: "A \<in> pp_e_frame_consistent_sentences S"
    using consistent
    unfolding pp_e_frame_consistent_sentences_def by simp
  have in_range: "A \<in> range (pp_e_consistent_sentence_enum S)"
    using pp_e_consistent_sentence_enum_range[of S] member by simp
  obtain n where enum: "pp_e_consistent_sentence_enum S n = A"
    using in_range by blast
  have branch:
      "pp_e_holds
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) [n]"
    using pp_e_enumerated_sentence_true_at_branch[of S n]
    unfolding enum .
  show "pp_e_true_in (pp_e_complete_constants S) (\<diamond>\<^sub>o A)"
    unfolding pp_e_ObjDiamond_true_iff using branch by blast
next
  assume possible:
      "pp_e_true_in (pp_e_complete_constants S) (\<diamond>\<^sub>o A)"
  then obtain w where at_w:
      "pp_e_holds
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) w"
    unfolding pp_e_ObjDiamond_true_iff by blast
  have complete_model: "pp_e_constants (pp_e_complete_constants S)"
    by (rule pp_e_complete_constants_model)
  have shifted_model:
      "pp_e_constants
        (pp_e_shifted_constants (pp_e_complete_constants S) w)"
    by (rule pp_e_shifted_constants_model[OF complete_model])
  have typed: "[] \<turnstile> A : Prop"
    using sentence unfolding pp_e_sentence_def by blast
  have shifted_true:
      "pp_e_true_in
        (pp_e_shifted_constants (pp_e_complete_constants S) w) A"
    using pp_e_shifted_truth_iff[OF complete_model typed, of w] at_w
    by simp
  show "pp_e_frame_consistent S A"
    unfolding pp_e_frame_consistent_iff_model
    using sentence shifted_model shifted_true by blast
qed

section \<open>Exact completeness for the frame theory\<close>

theorem pp_e_Bacon_exact_completeness:
  assumes sentence: "pp_e_sentence S A"
  shows "A \<in> pp_e_frame_theory S \<longleftrightarrow>
    pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)"
proof
  assume theory_mem: "A \<in> pp_e_frame_theory S"
  have valid:
      "\<And>C. pp_e_constants C \<Longrightarrow> pp_e_true_in C A"
    using theory_mem unfolding pp_e_frame_theory_def by blast
  have complete_model: "pp_e_constants (pp_e_complete_constants S)"
    by (rule pp_e_complete_constants_model)
  have all_worlds:
      "\<forall>w. pp_e_holds
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) w"
  proof
    fix w
    have shifted_model:
        "pp_e_constants
          (pp_e_shifted_constants (pp_e_complete_constants S) w)"
      by (rule pp_e_shifted_constants_model[OF complete_model])
    have shifted_true:
        "pp_e_true_in
          (pp_e_shifted_constants (pp_e_complete_constants S) w) A"
      by (rule valid[OF shifted_model])
    have typed: "[] \<turnstile> A : Prop"
      using sentence unfolding pp_e_sentence_def by blast
    show "pp_e_holds
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) w"
      using pp_e_shifted_truth_iff[OF complete_model typed, of w]
        shifted_true by simp
  qed
  show "pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)"
    unfolding pp_e_ObjBox_true_iff using all_worlds .
next
  assume necessary:
      "pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)"
  have all_worlds:
      "\<forall>w. pp_e_holds
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) w"
    using necessary unfolding pp_e_ObjBox_true_iff .
  show "A \<in> pp_e_frame_theory S"
  proof (unfold pp_e_frame_theory_def, intro CollectI conjI)
    show "pp_e_sentence S A" by (rule sentence)
    show "\<forall>C. pp_e_constants C \<longrightarrow> pp_e_true_in C A"
    proof (intro allI impI)
      fix C
      assume model: "pp_e_constants C"
      show "pp_e_true_in C A"
      proof (rule ccontr)
        assume not_true: "\<not> pp_e_true_in C A"
        have neg_sentence: "pp_e_sentence S (Neg A)"
          using sentence by simp
        have neg_true: "pp_e_true_in C (Neg A)"
          using not_true by simp
        have neg_consistent: "pp_e_frame_consistent S (Neg A)"
          unfolding pp_e_frame_consistent_iff_model
          using neg_sentence model neg_true by blast
        have neg_possible:
            "pp_e_true_in (pp_e_complete_constants S)
              (\<diamond>\<^sub>o (Neg A))"
          using pp_e_Bacon_consistency_representation[OF neg_sentence]
            neg_consistent by blast
        then obtain w where neg_at_w:
            "pp_e_holds
              (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env
                (Neg A)) w"
          unfolding pp_e_ObjDiamond_true_iff by blast
        have "\<not> pp_e_holds
            (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) w"
          using neg_at_w by simp
        then show False using all_worlds by blast
      qed
    qed
  qed
qed

corollary pp_e_Bacon_exact_theory_characterization:
  "pp_e_frame_theory S =
    {A. pp_e_sentence S A \<and>
      pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)}"
proof (rule set_eqI)
  fix A
  show "A \<in> pp_e_frame_theory S \<longleftrightarrow>
      A \<in> {A. pp_e_sentence S A \<and>
        pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)}"
  proof
    assume member: "A \<in> pp_e_frame_theory S"
    have sentence: "pp_e_sentence S A"
      using member unfolding pp_e_frame_theory_def by blast
    have necessary:
        "pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)"
      using pp_e_Bacon_exact_completeness[OF sentence] member by blast
    show "A \<in> {A. pp_e_sentence S A \<and>
        pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)}"
      using sentence necessary by simp
  next
    assume member:
        "A \<in> {A. pp_e_sentence S A \<and>
          pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)}"
    then have sentence: "pp_e_sentence S A"
      and necessary:
        "pp_e_true_in (pp_e_complete_constants S) (\<box>\<^sub>o A)"
      by simp_all
    show "A \<in> pp_e_frame_theory S"
      using pp_e_Bacon_exact_completeness[OF sentence] necessary by blast
  qed
qed

end
