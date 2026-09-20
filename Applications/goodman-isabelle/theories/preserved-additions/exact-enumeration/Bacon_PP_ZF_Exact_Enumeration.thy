theory Bacon_PP_ZF_Exact_Enumeration
  imports 
    "Goodman_Exact_Legacy_07.Bacon_PP_ZF_Exact_CEV_Soundness"
begin

section \<open>Bacon's enumeration of frame-consistent sentences\<close>

text \<open>
  This theory formalizes the second part of Bacon's appendix construction.
  As in the source, the result is relative to a signature and restricted to
  the fragment whose types are generated from propositions.  Bacon explicitly
  leaves the extension including type \<open>e\<close> for future work.
\<close>

fun pp_e_term_in_signature ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_e_term_in_signature S (Var n) = True"
| "pp_e_term_in_signature S (Const c \<sigma>) = S c \<sigma>"
| "pp_e_term_in_signature S (App M N) =
    (pp_e_term_in_signature S M \<and> pp_e_term_in_signature S N)"
| "pp_e_term_in_signature S (Lam \<sigma> M) = pp_e_term_in_signature S M"
| "pp_e_term_in_signature S (Eq \<sigma> M N) =
    (pp_e_term_in_signature S M \<and> pp_e_term_in_signature S N)"
| "pp_e_term_in_signature S (Neg A) = pp_e_term_in_signature S A"
| "pp_e_term_in_signature S (Conj A B) =
    (pp_e_term_in_signature S A \<and> pp_e_term_in_signature S B)"
| "pp_e_term_in_signature S (Disj A B) =
    (pp_e_term_in_signature S A \<and> pp_e_term_in_signature S B)"
| "pp_e_term_in_signature S (Imp A B) =
    (pp_e_term_in_signature S A \<and> pp_e_term_in_signature S B)"
| "pp_e_term_in_signature S (Forall \<sigma> A) = pp_e_term_in_signature S A"
| "pp_e_term_in_signature S (Exists \<sigma> A) = pp_e_term_in_signature S A"

definition pp_e_sentence ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_e_sentence S A \<longleftrightarrow>
    [] \<turnstile> A : Prop \<and>
    pp_e_propositional_term A \<and>
    pp_e_term_in_signature S A"

definition pp_e_true_in ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_e_true_in C A \<longleftrightarrow>
    pp_e_holds (pp_e_eval C pp_e_closed_env A) []"

definition pp_e_frame_theory ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> oterm set"
where
  "pp_e_frame_theory S =
    {A. pp_e_sentence S A \<and>
      (\<forall>C. pp_e_constants C \<longrightarrow> pp_e_true_in C A)}"

definition pp_e_frame_consistent ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_e_frame_consistent S A \<longleftrightarrow>
    pp_e_sentence S A \<and> Neg A \<notin> pp_e_frame_theory S"

lemma pp_e_sentence_Neg[simp]:
  "pp_e_sentence S (Neg A) \<longleftrightarrow> pp_e_sentence S A"
  unfolding pp_e_sentence_def
  by (auto elim: has_type.cases intro: has_type.Neg)

lemma pp_e_true_in_Neg[simp]:
  "pp_e_true_in C (Neg A) \<longleftrightarrow> \<not> pp_e_true_in C A"
  unfolding pp_e_true_in_def by simp

theorem pp_e_frame_consistent_iff_model:
  "pp_e_frame_consistent S A \<longleftrightarrow>
    pp_e_sentence S A \<and>
    (\<exists>C. pp_e_constants C \<and> pp_e_true_in C A)"
  unfolding pp_e_frame_consistent_def pp_e_frame_theory_def
  by auto

definition pp_e_frame_consistent_sentences ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> oterm set"
where
  "pp_e_frame_consistent_sentences S =
    {A. pp_e_frame_consistent S A}"

lemma pp_e_frame_consistent_sentences_countable:
  "countable (pp_e_frame_consistent_sentences S)"
  by simp

lemma pp_e_ObjTrue_sentence:
  "pp_e_sentence S ObjTrue"
  unfolding pp_e_sentence_def
proof (intro conjI)
  show "[] \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  show "pp_e_propositional_term ObjTrue"
    by (simp add: ObjTrue_def)
  show "pp_e_term_in_signature S ObjTrue"
    by (simp add: ObjTrue_def)
qed

lemma pp_e_ObjTrue_true_in:
  "pp_e_true_in C ObjTrue"
  unfolding pp_e_true_in_def
  by (simp add: pp_e_eval_ObjTrue)

lemma pp_e_frame_consistent_sentences_nonempty:
  "pp_e_frame_consistent_sentences S \<noteq> {}"
proof -
  have model: "pp_e_constants pp_e_default_constants"
    by (rule DefaultExactBaconConstants.pp_e_constants_axioms)
  have "pp_e_frame_consistent S ObjTrue"
    unfolding pp_e_frame_consistent_iff_model
    using pp_e_ObjTrue_sentence pp_e_ObjTrue_true_in model by blast
  then show ?thesis
    unfolding pp_e_frame_consistent_sentences_def by blast
qed

definition pp_e_consistent_sentence_enum ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> oterm"
where
  "pp_e_consistent_sentence_enum S =
    from_nat_into (pp_e_frame_consistent_sentences S)"

theorem pp_e_consistent_sentence_enum_range:
  "range (pp_e_consistent_sentence_enum S) =
    pp_e_frame_consistent_sentences S"
  unfolding pp_e_consistent_sentence_enum_def
  by (rule range_from_nat_into[
      OF pp_e_frame_consistent_sentences_nonempty
        pp_e_frame_consistent_sentences_countable])

lemma pp_e_consistent_sentence_enum_consistent:
  "pp_e_frame_consistent S (pp_e_consistent_sentence_enum S n)"
  using pp_e_consistent_sentence_enum_range[of S]
  unfolding pp_e_frame_consistent_sentences_def by blast

section \<open>Component models and their exact gluing\<close>

definition pp_e_component_constants ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_component_constants S n =
    (SOME C. pp_e_constants C \<and>
      pp_e_true_in C (pp_e_consistent_sentence_enum S n))"

lemma pp_e_component_constants_witness:
  "pp_e_constants (pp_e_component_constants S n) \<and>
   pp_e_true_in (pp_e_component_constants S n)
     (pp_e_consistent_sentence_enum S n)"
proof -
  have existence:
      "\<exists>C. pp_e_constants C \<and>
        pp_e_true_in C (pp_e_consistent_sentence_enum S n)"
    using pp_e_consistent_sentence_enum_consistent[of S n]
    unfolding pp_e_frame_consistent_iff_model by blast
  show ?thesis
    unfolding pp_e_component_constants_def
    by (rule someI_ex[OF existence])
qed

lemma pp_e_component_constants_typed:
  "Elem (pp_e_component_constants S n c \<sigma>) (pp_e_domain \<sigma>)"
proof -
  have model: "pp_e_constants (pp_e_component_constants S n)"
    using pp_e_component_constants_witness[of S n] by blast
  interpret Component: pp_e_constants "pp_e_component_constants S n"
    by (rule model)
  show ?thesis by (rule Component.C_typed)
qed

definition pp_e_complete_constants ::
    "(string \<Rightarrow> otype \<Rightarrow> bool) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_complete_constants S =
    pp_e_Bacon_glued_constants (pp_e_component_constants S)"

lemma pp_e_complete_constants_typed:
  "Elem (pp_e_complete_constants S c \<sigma>) (pp_e_domain \<sigma>)"
  unfolding pp_e_complete_constants_def
  by (rule pp_e_Bacon_glued_constants_typed)
    (rule pp_e_component_constants_typed)

lemma pp_e_complete_constants_model:
  "pp_e_constants (pp_e_complete_constants S)"
  by standard (rule pp_e_complete_constants_typed)

lemma pp_e_complete_constants_component_action:
  assumes prop_type: "pp_e_propositional_type \<sigma>"
  shows "pp_b_action \<sigma> [n] (pp_e_complete_constants S c \<sigma>) =
    pp_e_component_constants S n c \<sigma>"
  unfolding pp_e_complete_constants_def
  by (rule pp_e_Bacon_glued_constants_action[OF _ prop_type])
    (rule pp_e_component_constants_typed)

theorem pp_e_complete_term_component_action:
  assumes typed: "[] \<turnstile> A : \<sigma>"
    and fragment: "pp_e_propositional_term A"
  shows "pp_b_action \<sigma> [n]
      (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env A) =
    pp_e_eval (pp_e_component_constants S n) pp_e_closed_env A"
  unfolding pp_e_complete_constants_def
  by (rule pp_e_Bacon_10_1_term_action[OF _ typed fragment])
    (rule pp_e_component_constants_typed)

theorem pp_e_enumerated_sentence_true_at_branch:
  "pp_e_holds
    (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env
      (pp_e_consistent_sentence_enum S n)) [n]"
proof -
  have sentence:
      "pp_e_sentence S (pp_e_consistent_sentence_enum S n)"
    using pp_e_consistent_sentence_enum_consistent[of S n]
    unfolding pp_e_frame_consistent_def by blast
  have component:
      "pp_e_true_in (pp_e_component_constants S n)
        (pp_e_consistent_sentence_enum S n)"
    using pp_e_component_constants_witness[of S n] by blast
  have action:
      "pp_b_action Prop [n]
        (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env
          (pp_e_consistent_sentence_enum S n)) =
       pp_e_eval (pp_e_component_constants S n) pp_e_closed_env
          (pp_e_consistent_sentence_enum S n)"
    by (rule pp_e_complete_term_component_action)
      (use sentence in \<open>auto simp: pp_e_sentence_def\<close>)
  have acted_true:
      "pp_e_holds
        (pp_b_action Prop [n]
          (pp_e_eval (pp_e_complete_constants S) pp_e_closed_env
            (pp_e_consistent_sentence_enum S n))) []"
    using component action
    unfolding pp_e_true_in_def by simp
  show ?thesis
    using acted_true by simp
qed

section \<open>Models shifted to an arbitrary substitution\<close>

definition pp_e_shifted_constants ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow> pp_word \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_shifted_constants C w c \<sigma> =
    pp_b_action \<sigma> (rev w) (C c \<sigma>)"

lemma pp_e_shifted_constants_model:
  assumes model: "pp_e_constants C"
  shows "pp_e_constants (pp_e_shifted_constants C w)"
proof -
  interpret Source: pp_e_constants C by (rule model)
  show ?thesis
  proof
    show "Elem (pp_e_shifted_constants C w c \<sigma>)
        (pp_e_domain \<sigma>)" for c \<sigma>
      unfolding pp_e_shifted_constants_def
      by (rule pp_b_action_closed_all[OF Source.C_typed])
  qed
qed

theorem pp_e_shifted_eval:
  assumes model: "pp_e_constants C"
    and typed: "[] \<turnstile> A : \<sigma>"
  shows "pp_e_eval (pp_e_shifted_constants C w) pp_e_closed_env A =
    pp_b_action \<sigma> (rev w)
      (pp_e_eval C pp_e_closed_env A)"
proof -
  interpret Related: pp_e_action_related_constants
      C "pp_e_shifted_constants C w" "rev w"
  proof
    interpret Source: pp_e_constants C by (rule model)
    show "Elem (C c \<sigma>) (pp_e_domain \<sigma>)" for c \<sigma>
      by (rule Source.C_typed)
    show "Elem (pp_e_shifted_constants C w c \<sigma>)
        (pp_e_domain \<sigma>)" for c \<sigma>
      using pp_e_shifted_constants_model[OF model, of w]
      by (rule pp_e_constants.C_typed)
    show "pp_b_action \<sigma> (rev w) (C c \<sigma>) =
        pp_e_shifted_constants C w c \<sigma>" for \<sigma> c
      by (simp add: pp_e_shifted_constants_def)
  qed
  have source: "pp_e_env_typed [] pp_e_closed_env"
    by (rule pp_e_empty_env_typed)
  have rel: "pp_e_env_action [] (rev w)
      pp_e_closed_env pp_e_closed_env"
    by (simp add: pp_e_env_action_def lookup_def)
  show ?thesis
    using Related.pp_e_eval_action_related[OF typed source rel]
    by simp
qed

theorem pp_e_shifted_truth_iff:
  assumes model: "pp_e_constants C"
    and typed: "[] \<turnstile> A : Prop"
  shows "pp_e_true_in (pp_e_shifted_constants C w) A \<longleftrightarrow>
    pp_e_holds (pp_e_eval C pp_e_closed_env A) w"
  unfolding pp_e_true_in_def
  using pp_e_shifted_eval[OF model typed, of w]
  by simp

end
