theory Goodman_M1_Fn59_Purity
  imports "Goodman_Integration_T6.Goodman_Restricted_Signature_Transfer"
begin

section \<open>The footnote-59 diagonal: syntax, conversion, and purity\<close>

text \<open>
  Source: Bacon's footnote 59 and the object-language construction in
  theories/goodman/notes/Bacon_PP_Goodman_M1_Complete.thy of the original
  Goodman project (SHA256:
  2b29d00222e91720615ea2d76fdd9ca9132fac5a48331273f8272f0e5bc8f022).
  The definitions, beta calculations, and CEV+ purity argument below are
  preserved under gi_M1_fn59_ names, without importing that file's unrelated
  model-theoretic dependency chain. The independent named-language
  endpoint is added after this constructor-level proof.
  Purity of Fun at t is an explicit additional axiom throughout.
\<close>

definition gi_M1_fn59_liar :: oterm where
  "gi_M1_fn59_liar =
    Lam Prop
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun Prop (Var 0))
                (Eq Prop
                  (Var 2)
                  (App (Var 1) (Var 0)))))
            (Neg (App (Var 1) (Var 2))))))"

text \<open>
  Under the inner binders, this is
  \<open>D p \<longleftrightarrow> \<forall>X q.
    Pure(X) \<and> Fun(q) \<and> p = X q \<longrightarrow> \<not> X p\<close>.
  Unique proposition-level fundamentality reduces the quantified \<open>q\<close> to
  the distinguished fundamental proposition, yielding the semantic diagonal whose exact-model verification is separate.
\<close>

lemma typed_gi_M1_fn59_liar:
  "\<Gamma> \<turnstile> gi_M1_fn59_liar : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: gi_M1_fn59_liar_def pp_unary_ty_def
      pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def lookup_def)

definition gi_M1_fn59_builder :: oterm where
  "gi_M1_fn59_builder =
    Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      (Lam (Prop \<rightarrow>\<^sub>o Prop)
        (Lam Prop
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (App (Var 4) (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))))"

abbreviation gi_M1_fn59_instance :: oterm where
  "gi_M1_fn59_instance \<equiv>
    App
      (App gi_M1_fn59_builder (pp_Pure pp_unary_ty))
      (pp_Fun Prop)"

definition gi_M1_fn59_after_pure :: oterm where
  "gi_M1_fn59_after_pure =
    Lam (Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop
        (Forall pp_unary_ty
          (Forall Prop
            (Imp
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (Conj
                  (App (Var 3) (Var 0))
                  (Eq Prop
                    (Var 2)
                    (App (Var 1) (Var 0)))))
              (Neg (App (Var 1) (Var 2)))))))"

lemma gi_M1_fn59_builder_constant_free:
  "consts_of gi_M1_fn59_builder = {}"
  by (simp add: gi_M1_fn59_builder_def)

lemma typed_gi_M1_fn59_builder:
  "\<Gamma> \<turnstile> gi_M1_fn59_builder :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: gi_M1_fn59_builder_def pp_unary_ty_def lookup_def)

lemma typed_gi_M1_fn59_instance:
  "\<Gamma> \<turnstile> gi_M1_fn59_instance : pp_unary_ty"
  using typed_gi_M1_fn59_builder
    typed_pp_Pure[of \<Gamma> pp_unary_ty]
    typed_pp_Fun[of \<Gamma> Prop]
  by (intro has_type.App)

lemma typed_gi_M1_fn59_after_pure:
  "\<Gamma> \<turnstile> gi_M1_fn59_after_pure :
    (Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: gi_M1_fn59_after_pure_def pp_unary_ty_def
      pp_pure_def pp_Pure_def lookup_def)

lemma gi_M1_fn59_first_beta:
  "beta_contract
    (App gi_M1_fn59_builder (pp_Pure pp_unary_ty))
    gi_M1_fn59_after_pure"
proof -
  have "beta_contract
      (App gi_M1_fn59_builder (pp_Pure pp_unary_ty))
      (subst0 (pp_Pure pp_unary_ty)
        (Lam (Prop \<rightarrow>\<^sub>o Prop)
          (Lam Prop
            (Forall pp_unary_ty
              (Forall Prop
                (Imp
                  (Conj
                    (App (Var 4) (Var 1))
                    (Conj
                      (App (Var 3) (Var 0))
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))))
                  (Neg (App (Var 1) (Var 2)))))))))"
    unfolding gi_M1_fn59_builder_def
    by (rule beta_contract.beta)
  then show ?thesis
    by (simp add: gi_M1_fn59_after_pure_def subst0_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      eval_nat_numeral)
qed

lemma gi_M1_fn59_second_beta:
  "beta_contract
    (App gi_M1_fn59_after_pure (pp_Fun Prop))
    gi_M1_fn59_liar"
proof -
  have "beta_contract
      (App gi_M1_fn59_after_pure (pp_Fun Prop))
      (subst0 (pp_Fun Prop)
        (Lam Prop
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))))"
    unfolding gi_M1_fn59_after_pure_def
    by (rule beta_contract.beta)
  then show ?thesis
    by (simp add: gi_M1_fn59_liar_def subst0_def
      pp_fun_def pp_Fun_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def eval_nat_numeral)
qed

lemma gi_M1_fn59_instance_beta_eta:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty gi_M1_fn59_instance gi_M1_fn59_liar"
proof -
  have instance_type:
      "\<Gamma> \<turnstile> gi_M1_fn59_instance : Prop \<rightarrow>\<^sub>o Prop"
    using typed_gi_M1_fn59_instance
    by (simp add: pp_unary_ty_def)
  have liar_type:
      "\<Gamma> \<turnstile> gi_M1_fn59_liar : Prop \<rightarrow>\<^sub>o Prop"
    using typed_gi_M1_fn59_liar
    by (simp add: pp_unary_ty_def)
  have pointwise:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App (shift gi_M1_fn59_instance) (Var 0)
          \<longleftrightarrow>\<^sub>o
         App (shift gi_M1_fn59_liar) (Var 0))"
  proof -
    have left_type:
        "Prop # \<Gamma> \<turnstile>
          App gi_M1_fn59_instance (Var 0) : Prop"
      using typed_gi_M1_fn59_instance typed_var0
      unfolding pp_unary_ty_def by (rule has_type.App)
    have right_type:
        "Prop # \<Gamma> \<turnstile>
          App gi_M1_fn59_liar (Var 0) : Prop"
      using typed_gi_M1_fn59_liar typed_var0
      unfolding pp_unary_ty_def by (rule has_type.App)
    have middle_type:
        "Prop # \<Gamma> \<turnstile>
          App (App gi_M1_fn59_after_pure (pp_Fun Prop)) (Var 0) :
            Prop"
      using typed_gi_M1_fn59_after_pure typed_pp_Fun typed_var0
      unfolding pp_unary_ty_def by (intro has_type.App)
    have first_step:
        "compatible_step beta_contract
          (App gi_M1_fn59_instance (Var 0))
          (App (App gi_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))"
      by (intro compatible_step.App_left compatible_step.App_left
          compatible_step.root gi_M1_fn59_first_beta)
    have second_step:
        "compatible_step beta_contract
          (App (App gi_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))
          (App gi_M1_fn59_liar (Var 0))"
      by (intro compatible_step.App_left compatible_step.root
          gi_M1_fn59_second_beta)
    have first_beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App gi_M1_fn59_instance (Var 0))
          (App (App gi_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))"
      using left_type middle_type first_step
      by (rule beta_eta_equiv.Beta)
    have second_beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App (App gi_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))
          (App gi_M1_fn59_liar (Var 0))"
      using middle_type right_type second_step
      by (rule beta_eta_equiv.Beta)
    have beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App gi_M1_fn59_instance (Var 0))
          (App gi_M1_fn59_liar (Var 0))"
      using first_beta second_beta by (rule beta_eta_equiv.Trans)
    have
        "Prop # \<Gamma> \<turnstile>\<^sub>CEV
          (App gi_M1_fn59_instance (Var 0)
            \<longleftrightarrow>\<^sub>o
           App gi_M1_fn59_liar (Var 0))"
      using beta by (rule CEV_beta_eta_equiv)
    then show ?thesis
      by (simp add: shift_def gi_M1_fn59_builder_def
          gi_M1_fn59_liar_def pp_pure_def pp_Pure_def
          pp_fun_def pp_Fun_def shift_by_def shift_ren_def
          eval_nat_numeral)
  qed
  have
      "\<Gamma> \<turnstile>\<^sub>CEV
        Eq (Prop \<rightarrow>\<^sub>o Prop)
          gi_M1_fn59_instance gi_M1_fn59_liar"
    using instance_type liar_type pointwise
    by (rule CEV_unary_equivalence)
  then show ?thesis
    by (simp add: pp_unary_ty_def)
qed

definition gi_M1_fn59_axioms :: "oterm set" where
  "gi_M1_fn59_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_target_PP, pp_purity_of_fun Prop}"

lemma gi_M1_fn59_builder_purity_axiom:
  "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o pp_unary_ty)
      gi_M1_fn59_builder \<in> gi_M1_fn59_axioms"
  unfolding gi_M1_fn59_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
  using typed_gi_M1_fn59_builder
    gi_M1_fn59_builder_constant_free
  by blast

lemma gi_M1_fn59_application_closure:
  "pp_application_closure \<sigma> \<tau> \<in> gi_M1_fn59_axioms"
  unfolding gi_M1_fn59_axioms_def
    pp_application_closure_schema_def by blast

lemma gi_M1_fn59_PP:
  "pp_target_PP \<in> gi_M1_fn59_axioms"
  unfolding gi_M1_fn59_axioms_def by blast

lemma gi_M1_fn59_purity_of_fun:
  "pp_purity_of_fun Prop \<in> gi_M1_fn59_axioms"
  unfolding gi_M1_fn59_axioms_def by blast

theorem gi_M1_fn59_liar_pure:
  "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty gi_M1_fn59_liar"
proof -
  let ?builder_ty =
    "(pp_unary_ty \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o pp_unary_ty"
  let ?after_pure_ty =
    "(Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  have builder_pure:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure ?builder_ty gi_M1_fn59_builder"
    using gi_M1_fn59_builder_purity_axiom
      typed_pp_pure[OF typed_gi_M1_fn59_builder]
    by (rule CEV_axiom_proves.Axiom)
  have Pure_pure:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop)
          (pp_Pure pp_unary_ty)"
  proof -
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_pure_def pp_Pure_def pp_unary_ty_def lookup_def)
    have
        "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using gi_M1_fn59_PP target_type
      by (rule CEV_axiom_proves.Axiom)
    then show ?thesis
      by (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_unary_ty_def)
  qed
  have first_pure:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure ?after_pure_ty
          (App gi_M1_fn59_builder (pp_Pure pp_unary_ty))"
    using gi_M1_fn59_application_closure[
        of "pp_unary_ty \<rightarrow>\<^sub>o Prop" ?after_pure_ty]
      typed_gi_M1_fn59_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
      builder_pure Pure_pure
    by (rule pp_axiom_application_closed)
  have Fun_pure:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (Prop \<rightarrow>\<^sub>o Prop) (pp_Fun Prop)"
  proof -
    have fun_purity_type:
        "\<Gamma> \<turnstile> pp_purity_of_fun Prop : Prop"
      by (rule infer_type_sound)
        (simp add: pp_purity_of_fun_def pp_pure_def pp_Pure_def
          pp_Fun_def lookup_def)
    show ?thesis
      using gi_M1_fn59_purity_of_fun fun_purity_type
      unfolding pp_purity_of_fun_def
      by (rule CEV_axiom_proves.Axiom)
  qed
  have first_type:
      "\<Gamma> \<turnstile>
        App gi_M1_fn59_builder (pp_Pure pp_unary_ty) :
          ?after_pure_ty"
    using typed_gi_M1_fn59_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
    by (rule has_type.App)
  have instance_pure:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty gi_M1_fn59_instance"
    using gi_M1_fn59_application_closure[
        of "Prop \<rightarrow>\<^sub>o Prop" pp_unary_ty]
      first_type typed_pp_Fun first_pure Fun_pure
    by (rule pp_axiom_application_closed)
  have identity:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Eq pp_unary_ty gi_M1_fn59_instance gi_M1_fn59_liar"
    using gi_M1_fn59_instance_beta_eta
    by (rule CEV_axiom_proves.Base)
  have transfer:
      "\<Gamma> ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_pure pp_unary_ty gi_M1_fn59_instance)
          (pp_pure pp_unary_ty gi_M1_fn59_liar)"
  proof -
    have ll:
        "\<Gamma> \<turnstile>\<^sub>CEV
          Imp
            (Eq pp_unary_ty
              gi_M1_fn59_instance gi_M1_fn59_liar)
            (Imp
              (pp_pure pp_unary_ty gi_M1_fn59_instance)
              (pp_pure pp_unary_ty gi_M1_fn59_liar))"
      using typed_gi_M1_fn59_instance typed_gi_M1_fn59_liar
        typed_pp_Pure
      unfolding pp_pure_def
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
    show ?thesis
      using identity CEV_axiom_proves.Base[OF ll]
      by (rule CEV_axiom_proves.MP)
  qed
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_proves.MP)
qed


section \<open>The independently displayed native diagonal and axiom stock\<close>

definition gi_M1_native_fn59_liar :: "sgcontext \<Rightarrow> gb_term" where
  "gi_M1_native_fn59_liar G =
    NLam (gb_x G Prop)
      (book_all G (gb_y G Prop gb_unary)
        (book_all G (gb_z G Prop gb_unary Prop)
          (book_imp
            (book_and G
              (gb_pure gb_unary (NVar (gb_y G Prop gb_unary)))
              (book_and G
                (gb_fun Prop (NVar (gb_z G Prop gb_unary Prop)))
                (book_leibniz G Prop
                  (NVar (gb_x G Prop))
                  (NApp (NVar (gb_y G Prop gb_unary)) (NVar (gb_z G Prop gb_unary Prop))))))
            (book_not G (NApp (NVar (gb_y G Prop gb_unary)) (NVar (gb_x G Prop)))))))"

definition gi_M1_fn59_native_axioms :: "sgcontext \<Rightarrow> gb_term set" where
  "gi_M1_fn59_native_axioms G =
    gb_purity_schema G \<union> gb_application_schema G \<union>
      {gb_target_PP, gb_purity_of_fun Prop}"

lemma gi_M1_fn59_liar_vocabulary:
  "consts_of gi_M1_fn59_liar = {pp_pure_name, pp_fun_name}"
  by (simp add: gi_M1_fn59_liar_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def insert_commute)

lemma gi_M1_fn59_liar_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature gi_M1_fn59_liar"
  by (simp add: gi_M1_fn59_liar_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
      gi_goodman_names_def gb_signature_def pp_unary_ty_def)

theorem gi_M1_fn59_native_shape:
  assumes names: "gi_goodman_names k"
  shows "gi_to_book G [] k gi_M1_fn59_liar = gi_M1_native_fn59_liar G"
  by (simp add: gi_M1_fn59_liar_def gi_M1_native_fn59_liar_def
      gi_pure_translation[OF names] gi_fun_translation[OF names]
      pp_unary_ty_def gb_x_def gb_y_def gb_z_def Let_def
      named_chart_fresh_def insert_commute)

lemma gi_M1_native_fn59_liar_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV gb_signature G
    (gi_M1_native_fn59_liar G) gb_unary"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have translated: "book_in_language book_minimal_logical_type UNIV gb_signature G
      (gi_to_book G [] k gi_M1_fn59_liar) pp_unary_ty"
    by (rule gi_to_book_language[OF rich typed_gi_M1_fn59_liar _
      gi_M1_fn59_liar_admitted[OF names]]; simp)
  show ?thesis using translated
    by (simp only: gi_M1_fn59_native_shape[OF names] pp_unary_ty_def)
qed

lemma gi_M1_native_fn59_liar_closed:
  "named_fv (gi_M1_native_fn59_liar G) = {}"
  by (auto simp: gi_M1_native_fn59_liar_def book_all_fv book_imp_fv
      book_and_fv gb_pure_fv gb_fun_fv book_leibniz_fv book_not_fv)

lemma gi_M1_fn59_purity_of_fun_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k (pp_purity_of_fun Prop) = gb_purity_of_fun Prop"
  by (simp add: pp_purity_of_fun_def gb_purity_of_fun_def
      gi_pure_translation gi_Fun_translation)

lemma gi_M1_fn59_axioms_closed:
  "A \<in> gi_M1_fn59_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_M1_fn59_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed
      typed_pp_target_PP typed_pp_purity_of_fun)

theorem gi_M1_fn59_native_stock_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) gi_M1_fn59_axioms \<subseteq> gi_M1_fn59_native_axioms G"
  unfolding gi_M1_fn59_axioms_def gi_M1_fn59_native_axioms_def image_Un
  using gi_purity_schema_inclusion[OF rich names]
    gi_application_schema_equality[OF names, where G=G]
    gi_PP_translation[OF names, where G=G]
    gi_M1_fn59_purity_of_fun_translation[OF names, where G=G]
  by auto

lemma gi_M1_fn59_native_axioms_language:
  assumes rich: "sg_rich G" and member: "A \<in> gi_M1_fn59_native_axioms G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gi_M1_fn59_native_axioms_def gb_application_schema_def
  by (auto intro: gb_purity_schema_language
      gb_application_closure_language[OF rich] gb_target_PP_language gb_purity_of_fun_language)

theorem gi_M1_native_fn59_liar_pure:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gi_M1_fn59_native_axioms G)
    (gb_pure gb_unary (gi_M1_native_fn59_liar G))"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "[] ; gi_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty gi_M1_fn59_liar"
    by (rule gi_M1_fn59_liar_pure)
  have image_proof: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) gi_M1_fn59_axioms)
      (gi_to_book G [] k (pp_pure pp_unary_ty gi_M1_fn59_liar))"
    by (rule gi_CEV_axiom_preservation[OF rich original gi_M1_fn59_axioms_closed]; simp)
  have native_stock_proof: "goodman_book_proves (\<lambda>_. UNIV) G
      (gi_M1_fn59_native_axioms G)
      (gi_to_book G [] k (pp_pure pp_unary_ty gi_M1_fn59_liar))"
    by (rule goodman_book_mono[OF image_proof gi_M1_fn59_native_stock_inclusion[OF rich names]])
  have native_proof: "goodman_book_proves (\<lambda>_. UNIV) G (gi_M1_fn59_native_axioms G)
      (gb_pure gb_unary (gi_M1_native_fn59_liar G))"
    using native_stock_proof
    by (simp only: gi_pure_translation[OF names] gi_M1_fn59_native_shape[OF names] pp_unary_ty_def)
  show ?thesis
  proof (rule gi_goodman_foreign_constants_eliminate[OF rich native_proof])
    fix A assume member: "A \<in> gi_M1_fn59_native_axioms G"
    show "book_theory_formula gb_signature G A"
      by (rule gi_M1_fn59_native_axioms_language[OF rich member])
  next
    show "named_in_signature gb_signature (gb_pure gb_unary (gi_M1_native_fn59_liar G))"
      by (rule book_language_signature[OF gb_pure_language[OF gi_M1_native_fn59_liar_language[OF rich]]])
  qed
qed

corollary gi_M1_fn59_translated_liar_pure:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_M1_fn59_native_axioms G)
    (gb_pure gb_unary (gi_to_book G [] k gi_M1_fn59_liar))"
  by (simp only: gi_M1_fn59_native_shape[OF names]; rule gi_M1_native_fn59_liar_pure[OF rich])

text \<open>
  The final endpoint is an actual derivation in the source-language
  axiom extension, not a semantic-validity argument. Its stock consists
  exactly of logical purity, application closure, PP for the unary
  classifier, and Purity of Fun at t. Unique fundamentality and QSS are
  not used to prove purity; they belong to the separate diagonal
  contradiction. Removing Purity of Fun would change the theorem and
  has not been justified here.
\<close>

end
