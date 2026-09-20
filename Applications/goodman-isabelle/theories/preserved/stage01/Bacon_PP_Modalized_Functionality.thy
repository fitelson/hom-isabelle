theory Bacon_PP_Modalized_Functionality
  imports 
    "Goodman_Legacy_01.Bacon_PP_Diagonal"
begin

section \<open>Modalized Functionality: derived and assumed scopes\<close>

text \<open>
  Bacon--Dorr derive proposition-valued Modalized Functionality from
  Intensionality.  The machine-checked derivation in
  \<open>Bacon_PP_Modalized_Functionality_Derived\<close> has exactly that scope:
  arbitrary argument type \<open>\<sigma>\<close>, but result type \<open>Prop\<close>.

  The two-type formula below also permits an arbitrary result type \<open>\<tau>\<close>.
  That larger collection is retained as an explicit CEV+ axiom schema and as
  a direct model obligation.  No theorem here identifies it with the
  proposition-valued schema or claims that every instance is derivable in
  bare CEV.  The distinction matters for consistency transfer: the formal
  monotonicity results below are one-way results only.
\<close>

subsection \<open>The axiom\<close>

definition pp_modalized_functionality :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where
  "pp_modalized_functionality \<sigma> \<tau> =
    Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (Imp
          (\<box>\<^sub>o (Forall \<sigma>
            (Eq \<tau> (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))))
          (Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1) (Var 0))))"

text \<open>
  De Bruijn reading, innermost first: under the three binders \<open>Var 0\<close> is \<open>x\<close>, \<open>Var 1\<close>
  is \<open>Y\<close> and \<open>Var 2\<close> is \<open>X\<close>; in the consequent, which sits under two binders, \<open>Var 1\<close>
  is \<open>X\<close> and \<open>Var 0\<close> is \<open>Y\<close>.
\<close>

lemma typed_pp_modalized_functionality:
  "[] \<turnstile> pp_modalized_functionality \<sigma> \<tau> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_modalized_functionality_def ObjBox_def ObjTrue_def
      lookup_def)

definition pp_modalized_functionality_schema :: "oterm set" where
  "pp_modalized_functionality_schema =
    {A. \<exists>\<sigma> \<tau>. A = pp_modalized_functionality \<sigma> \<tau>}"

lemma pp_modalized_functionality_schema_typed:
  assumes "A \<in> pp_modalized_functionality_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_modalized_functionality
  unfolding pp_modalized_functionality_schema_def by blast

definition pp_proposition_valued_modalized_functionality_schema ::
    "oterm set"
where
  "pp_proposition_valued_modalized_functionality_schema =
    {A. \<exists>\<sigma>. A = pp_modalized_functionality \<sigma> Prop}"

lemma pp_proposition_valued_modalized_functionality_schema_typed:
  assumes "A \<in> pp_proposition_valued_modalized_functionality_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_modalized_functionality
  unfolding pp_proposition_valued_modalized_functionality_schema_def
  by blast

lemma pp_proposition_valued_modalized_functionality_schema_subset:
  "pp_proposition_valued_modalized_functionality_schema
    \<subseteq> pp_modalized_functionality_schema"
  unfolding pp_proposition_valued_modalized_functionality_schema_def
    pp_modalized_functionality_schema_def
  by blast

subsection \<open>The corrected axiom sets\<close>

definition pp_T0_recombination_background :: "oterm set" where
  "pp_T0_recombination_background =
    pp_recombination_background_axioms \<union>
    pp_modalized_functionality_schema"

definition pp_T0_recombination_PP_axioms :: "oterm set" where
  "pp_T0_recombination_PP_axioms =
    insert pp_target_PP pp_T0_recombination_background"

definition pp_T0_full_QLN_PP_axioms :: "oterm set" where
  "pp_T0_full_QLN_PP_axioms =
    pp_full_QLN_PP_axioms \<union> pp_modalized_functionality_schema"

lemma pp_T0_recombination_PP_axioms_typed:
  assumes "A \<in> pp_T0_recombination_PP_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms
  unfolding pp_T0_recombination_PP_axioms_def
    pp_T0_recombination_background_def
  using pp_recombination_PP_axioms_typed
    pp_modalized_functionality_schema_typed
  unfolding pp_recombination_PP_axioms_def
  by blast

subsection \<open>Everything already derived still stands, and more\<close>

lemma pp_recombination_PP_axioms_subset_T0:
  "pp_recombination_PP_axioms \<subseteq> pp_T0_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def
    pp_T0_recombination_PP_axioms_def
    pp_T0_recombination_background_def
  by blast

lemma pp_full_QLN_PP_axioms_subset_T0:
  "pp_full_QLN_PP_axioms \<subseteq> pp_T0_full_QLN_PP_axioms"
  unfolding pp_T0_full_QLN_PP_axioms_def by blast

theorem CEV_axiom_proves_transfer_to_T0:
  assumes "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; pp_T0_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms pp_recombination_PP_axioms_subset_T0
  by (rule CEV_axiom_proves_mono)

theorem CEV_axiom_proves_transfer_to_T0_full_QLN:
  assumes "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; pp_T0_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms pp_full_QLN_PP_axioms_subset_T0
  by (rule CEV_axiom_proves_mono)

text \<open>
  Thus every derivation from the smaller package survives addition of the
  arbitrary-result schema.  These monotonicity theorems do not provide the
  converse transfer needed for consistency.
\<close>

subsection \<open>The corrected question\<close>

definition pp_T0_recombination_consistency_question :: bool where
  "pp_T0_recombination_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_T0_recombination_PP_axioms"

definition pp_T0_full_QLN_consistency_question :: bool where
  "pp_T0_full_QLN_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_T0_full_QLN_PP_axioms"

theorem pp_T0_negative_answer_iff_derives_false:
  "\<not> pp_T0_recombination_consistency_question \<longleftrightarrow>
    [] ; pp_T0_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  unfolding pp_T0_recombination_consistency_question_def
    CEV_axiom_consistent_def
  by blast

theorem pp_T0_consistency_implies_old:
  assumes "pp_T0_recombination_consistency_question"
  shows "CEV_axiom_consistent [] pp_recombination_PP_axioms"
  using assms
  unfolding pp_T0_recombination_consistency_question_def
    CEV_axiom_consistent_def
  using CEV_axiom_proves_transfer_to_T0 by blast

text \<open>
  The proposition-valued instances are now derived in bare CEV and are the
  instances used by the formalized Goodman arguments.  Whether the same
  derivation extends to arbitrary result type \<open>\<tau>\<close>, and whether adding that
  larger schema is conservative for the relevant consistency question, remain
  separate open obligations.
\<close>

end
