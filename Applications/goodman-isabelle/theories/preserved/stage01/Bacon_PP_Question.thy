theory Bacon_PP_Question
  imports 
    "Bacon_Classicism.Bacon_Finite_CEV_Model"
begin

section \<open>Goodman's Purity of Pure consistency question\<close>

text \<open>
  This theory isolates the question over the active Bacon--Dorr background:
  Baconian H, Classicism, propositional Equivalence, and theorem-level vector
  Equivalence.  It assumes no contextual equivalence principle.

  There is exactly one fundamental proposition and no fundamental entities
  at other types.  The target PP instance says that the purity predicate for
  unary propositional operators is itself pure.  Purity of Fun is not assumed.

  Recombination and Exhaustion are stated separately.  This prevents the
  consistency question for the philosophically central Recombination
  direction from being silently strengthened to the full QLN biconditional.
\<close>

subsection \<open>Vocabulary\<close>

definition pp_pure_name :: string where
  "pp_pure_name = ''Pure''"

definition pp_fun_name :: string where
  "pp_fun_name = ''Fun''"

definition pp_Pure :: "otype \<Rightarrow> oterm" where
  "pp_Pure \<sigma> = Const pp_pure_name (\<sigma> \<rightarrow>\<^sub>o Prop)"

definition pp_Fun :: "otype \<Rightarrow> oterm" where
  "pp_Fun \<sigma> = Const pp_fun_name (\<sigma> \<rightarrow>\<^sub>o Prop)"

definition pp_pure :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pure \<sigma> M = App (pp_Pure \<sigma>) M"

definition pp_fun :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_fun \<sigma> M = App (pp_Fun \<sigma>) M"

lemma typed_pp_Pure:
  "\<Gamma> \<turnstile> pp_Pure \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding pp_Pure_def by (rule has_type.Const)

lemma typed_pp_Fun:
  "\<Gamma> \<turnstile> pp_Fun \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding pp_Fun_def by (rule has_type.Const)

lemma typed_pp_pure:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_pure \<sigma> M : Prop"
  unfolding pp_pure_def
  using typed_pp_Pure assms by (rule has_type.App)

lemma typed_pp_fun:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_fun \<sigma> M : Prop"
  unfolding pp_fun_def
  using typed_pp_Fun assms by (rule has_type.App)

subsection \<open>Purity and fundamentality principles\<close>

definition pp_purity_of_pure :: "otype \<Rightarrow> oterm" where
  "pp_purity_of_pure \<sigma> =
    pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (pp_Pure \<sigma>)"

definition pp_purity_of_fun :: "otype \<Rightarrow> oterm" where
  "pp_purity_of_fun \<sigma> =
    pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (pp_Fun \<sigma>)"

definition pp_application_closure :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where
  "pp_application_closure \<sigma> \<tau> =
    Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (Var 1) (Var 0)))))"

definition pp_persistence :: "otype \<Rightarrow> oterm" where
  "pp_persistence \<sigma> =
    Forall \<sigma>
      (Imp (pp_pure \<sigma> (Var 0))
        (\<box>\<^sub>o (pp_pure \<sigma> (Var 0))))"

definition pp_unique_fundamental :: "otype \<Rightarrow> oterm" where
  "pp_unique_fundamental \<sigma> =
    Exists \<sigma>
      (Conj
        (pp_fun \<sigma> (Var 0))
        (Forall \<sigma>
          (Imp (pp_fun \<sigma> (Var 0)) (Eq \<sigma> (Var 0) (Var 1)))))"

definition pp_no_fundamentals :: "otype \<Rightarrow> oterm" where
  "pp_no_fundamentals \<sigma> =
    Forall \<sigma> (Neg (pp_fun \<sigma> (Var 0)))"

definition pp_target_PP :: oterm where
  "pp_target_PP = pp_purity_of_pure (Prop \<rightarrow>\<^sub>o Prop)"

lemma typed_pp_purity_of_pure:
  "[] \<turnstile> pp_purity_of_pure \<sigma> : Prop"
  unfolding pp_purity_of_pure_def
  using typed_pp_Pure by (rule typed_pp_pure)

lemma typed_pp_purity_of_fun:
  "[] \<turnstile> pp_purity_of_fun \<sigma> : Prop"
  unfolding pp_purity_of_fun_def
  using typed_pp_Fun by (rule typed_pp_pure)

lemma typed_pp_application_closure:
  "[] \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)

lemma typed_pp_persistence:
  "[] \<turnstile> pp_persistence \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_persistence_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unique_fundamental:
  "[] \<turnstile> pp_unique_fundamental \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def lookup_def)

lemma typed_pp_no_fundamentals:
  "[] \<turnstile> pp_no_fundamentals \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def lookup_def)

lemma typed_pp_target_PP:
  "[] \<turnstile> pp_target_PP : Prop"
  unfolding pp_target_PP_def by (rule typed_pp_purity_of_pure)

subsection \<open>QLN split into its two directions\<close>

text \<open>
  Goodman requires the fundamental arguments in an instance of QLN to be
  pairwise distinct, and the present theory stipulates exactly one fundamental
  entity, a proposition.  Hence every instance of arity at least two is
  vacuous in the intended specialization.  The only substantive instances are
  therefore zeroary and unary, and those are the instances formalized here.
  Recombination is the box-to-universal direction; Exhaustion is its converse.
\<close>

definition pp_zeroary_recombination :: oterm where
  "pp_zeroary_recombination =
    Forall Prop
      (Imp (pp_pure Prop (Var 0))
        (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))"

definition pp_zeroary_exhaustion :: oterm where
  "pp_zeroary_exhaustion =
    Forall Prop
      (Imp (pp_pure Prop (Var 0))
        (Imp (Var 0) (\<box>\<^sub>o (Var 0))))"

definition pp_unary_recombination :: oterm where
  "pp_unary_recombination =
    Forall (Prop \<rightarrow>\<^sub>o Prop)
      (Forall Prop
        (Imp
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App (Var 1) (Var 0)))
            (Forall Prop (App (Var 2) (Var 0))))))"

definition pp_unary_exhaustion :: oterm where
  "pp_unary_exhaustion =
    Forall (Prop \<rightarrow>\<^sub>o Prop)
      (Forall Prop
        (Imp
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))
          (Imp
            (Forall Prop (App (Var 2) (Var 0)))
            (\<box>\<^sub>o (App (Var 1) (Var 0))))))"

definition pp_zeroary_QLN :: oterm where
  "pp_zeroary_QLN =
    Forall Prop
      (Imp (pp_pure Prop (Var 0))
        ((\<box>\<^sub>o (Var 0)) \<longleftrightarrow>\<^sub>o Var 0))"

definition pp_unary_QLN :: oterm where
  "pp_unary_QLN =
    Forall (Prop \<rightarrow>\<^sub>o Prop)
      (Forall Prop
        (Imp
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))
          ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
            Forall Prop (App (Var 2) (Var 0)))))"

lemma typed_pp_zeroary_recombination:
  "[] \<turnstile> pp_zeroary_recombination : Prop"
  by (rule infer_type_sound)
    (simp add: pp_zeroary_recombination_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_zeroary_exhaustion:
  "[] \<turnstile> pp_zeroary_exhaustion : Prop"
  by (rule infer_type_sound)
    (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unary_recombination:
  "[] \<turnstile> pp_unary_recombination : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unary_exhaustion:
  "[] \<turnstile> pp_unary_exhaustion : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unary_exhaustion_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_zeroary_QLN:
  "[] \<turnstile> pp_zeroary_QLN : Prop"
  by (rule infer_type_sound)
    (simp add: pp_zeroary_QLN_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unary_QLN:
  "[] \<turnstile> pp_unary_QLN : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unary_QLN_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)

subsection \<open>The exact axiom packages\<close>

definition pp_logical_vocabulary :: "oterm \<Rightarrow> bool" where
  "pp_logical_vocabulary M \<longleftrightarrow> consts_of M = {}"

definition pp_purity_schema :: "oterm set" where
  "pp_purity_schema =
    {A. \<exists>\<sigma> M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and>
      A = pp_pure \<sigma> M}"

definition pp_application_closure_schema :: "oterm set" where
  "pp_application_closure_schema =
    {A. \<exists>\<sigma> \<tau>. A = pp_application_closure \<sigma> \<tau>}"

definition pp_no_other_fundamentals_schema :: "oterm set" where
  "pp_no_other_fundamentals_schema =
    {A. \<exists>\<sigma>. \<sigma> \<noteq> Prop \<and> A = pp_no_fundamentals \<sigma>}"

definition pp_persistence_schema :: "oterm set" where
  "pp_persistence_schema = {A. \<exists>\<sigma>. A = pp_persistence \<sigma>}"

definition pp_background_axioms :: "oterm set" where
  "pp_background_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_unique_fundamental Prop} \<union>
    pp_no_other_fundamentals_schema"

definition pp_recombination_background_axioms :: "oterm set" where
  "pp_recombination_background_axioms =
    pp_background_axioms \<union>
    {pp_zeroary_recombination, pp_unary_recombination}"

definition pp_exhaustion_axioms :: "oterm set" where
  "pp_exhaustion_axioms =
    {pp_zeroary_exhaustion, pp_unary_exhaustion}"

definition pp_full_QLN_background_axioms :: "oterm set" where
  "pp_full_QLN_background_axioms =
    pp_recombination_background_axioms \<union> pp_exhaustion_axioms"

text \<open>
  The stable \<open>pp_full_QLN_\<close> names below mean both directions of the complete
  zeroary-and-unary package just described.  They are not names for a separate
  generic all-arity encoding.
\<close>

abbreviation pp_zeroary_unary_QLN_background_axioms :: "oterm set" where
  "pp_zeroary_unary_QLN_background_axioms \<equiv>
    pp_full_QLN_background_axioms"

definition pp_recombination_PP_axioms :: "oterm set" where
  "pp_recombination_PP_axioms =
    insert pp_target_PP pp_recombination_background_axioms"

definition pp_full_QLN_PP_axioms :: "oterm set" where
  "pp_full_QLN_PP_axioms =
    insert pp_target_PP pp_full_QLN_background_axioms"

abbreviation pp_zeroary_unary_QLN_PP_axioms :: "oterm set" where
  "pp_zeroary_unary_QLN_PP_axioms \<equiv> pp_full_QLN_PP_axioms"

definition pp_full_QLN_PP_persistence_axioms :: "oterm set" where
  "pp_full_QLN_PP_persistence_axioms =
    pp_full_QLN_PP_axioms \<union> pp_persistence_schema"

abbreviation pp_zeroary_unary_QLN_PP_persistence_axioms :: "oterm set" where
  "pp_zeroary_unary_QLN_PP_persistence_axioms \<equiv>
    pp_full_QLN_PP_persistence_axioms"

lemma pp_full_QLN_background_axioms_exact_scope:
  "pp_full_QLN_background_axioms =
    pp_background_axioms \<union>
      {pp_zeroary_recombination, pp_unary_recombination,
       pp_zeroary_exhaustion, pp_unary_exhaustion}"
  unfolding pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def pp_exhaustion_axioms_def
  by blast

lemma pp_purity_schema_typed:
  assumes "A \<in> pp_purity_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_pure
  unfolding pp_purity_schema_def by blast

lemma pp_application_closure_schema_typed:
  assumes "A \<in> pp_application_closure_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_application_closure
  unfolding pp_application_closure_schema_def by blast

lemma pp_no_other_fundamentals_schema_typed:
  assumes "A \<in> pp_no_other_fundamentals_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_no_fundamentals
  unfolding pp_no_other_fundamentals_schema_def by blast

lemma pp_recombination_PP_axioms_typed:
  assumes "A \<in> pp_recombination_PP_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed pp_application_closure_schema_typed
    pp_no_other_fundamentals_schema_typed typed_pp_target_PP
    typed_pp_unique_fundamental typed_pp_zeroary_recombination
    typed_pp_unary_recombination
  unfolding pp_recombination_PP_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
  by blast

lemma pp_full_QLN_PP_axioms_typed:
  assumes "A \<in> pp_full_QLN_PP_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed pp_application_closure_schema_typed
    pp_no_other_fundamentals_schema_typed typed_pp_target_PP
    typed_pp_unique_fundamental typed_pp_zeroary_recombination
    typed_pp_unary_recombination typed_pp_zeroary_exhaustion
    typed_pp_unary_exhaustion
  unfolding pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def pp_recombination_background_axioms_def
    pp_exhaustion_axioms_def pp_background_axioms_def
  by blast

lemma pp_target_PP_is_assumed_recombination:
  "pp_target_PP \<in> pp_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def by blast

lemma pp_target_PP_is_assumed_full_QLN:
  "pp_target_PP \<in> pp_full_QLN_PP_axioms"
  unfolding pp_full_QLN_PP_axioms_def by blast

lemma pp_unique_fundamental_is_assumed_recombination:
  "pp_unique_fundamental Prop \<in> pp_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
  by blast

lemma pp_unique_fundamental_is_assumed_full_QLN:
  "pp_unique_fundamental Prop \<in> pp_full_QLN_PP_axioms"
  unfolding pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

subsection \<open>The consistency questions\<close>

definition pp_recombination_consistency_question :: bool where
  "pp_recombination_consistency_question \<longleftrightarrow>
    CEV_consistent [] pp_recombination_PP_axioms"

definition pp_full_QLN_consistency_question :: bool where
  "pp_full_QLN_consistency_question \<longleftrightarrow>
    CEV_consistent [] pp_full_QLN_PP_axioms"

definition pp_full_QLN_persistence_consistency_question :: bool where
  "pp_full_QLN_persistence_consistency_question \<longleftrightarrow>
    CEV_consistent [] pp_full_QLN_PP_persistence_axioms"

theorem pp_recombination_negative_answer_iff_derives_false:
  "\<not> pp_recombination_consistency_question \<longleftrightarrow>
    [] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  unfolding pp_recombination_consistency_question_def CEV_consistent_def
  by blast

theorem pp_full_QLN_negative_answer_iff_derives_false:
  "\<not> pp_full_QLN_consistency_question \<longleftrightarrow>
    [] ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  unfolding pp_full_QLN_consistency_question_def CEV_consistent_def
  by blast

theorem pp_full_QLN_negative_answer_iff_finite_inconsistent_core:
  "\<not> pp_full_QLN_consistency_question \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_PP_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse)"
proof
  assume "\<not> pp_full_QLN_consistency_question"
  then have "[] ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using pp_full_QLN_negative_answer_iff_derives_false by blast
  then obtain U where "finite U" and "U \<subseteq> pp_full_QLN_PP_axioms"
    and "[] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by (rule CEV_set_derivable_finite_support)
  then show "\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_PP_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by blast
next
  assume "\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_PP_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then obtain U where U_sub: "U \<subseteq> pp_full_QLN_PP_axioms"
    and d_U: "[] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by blast
  have "[] ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_U U_sub by (rule CEV_set_derivable_mono)
  then show "\<not> pp_full_QLN_consistency_question"
    using pp_full_QLN_negative_answer_iff_derives_false by blast
qed

lemma pp_recombination_PP_axioms_subset_full_QLN:
  "pp_recombination_PP_axioms \<subseteq> pp_full_QLN_PP_axioms"
  unfolding pp_recombination_PP_axioms_def pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def
  by blast

lemma pp_full_QLN_answer_implies_recombination_answer:
  assumes "pp_full_QLN_consistency_question"
  shows "pp_recombination_consistency_question"
  using assms pp_recombination_PP_axioms_subset_full_QLN CEV_consistent_mono
  unfolding pp_full_QLN_consistency_question_def
    pp_recombination_consistency_question_def
  by blast

text \<open>
  No consistency verdict is asserted at this point.  An affirmative answer
  requires a model or a consistency proof for one of these exact packages.  A
  negative answer requires a CEV derivation of falsity, equivalently one from
  a finite subset of the relevant package.
\<close>

end
