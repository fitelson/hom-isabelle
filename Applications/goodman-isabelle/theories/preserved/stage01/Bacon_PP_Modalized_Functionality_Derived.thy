theory Bacon_PP_Modalized_Functionality_Derived
  imports 
    "Goodman_Legacy_01.Bacon_PP_Intensionality"
    "Goodman_Legacy_01.Bacon_PP_Modalized_Functionality"
begin

section \<open>Proposition-valued Modalized Functionality is a theorem of CEV\<close>

text \<open>
  The proposition-valued unary instance of Modalized Functionality follows
  from unary Intensionality.  The only nonmodal bridge needed is that identity
  between propositions implies their material biconditional.  We prove that
  bridge inside the object logic and then lift its universal closure through
  necessity by modal \<open>K\<close>.
\<close>

subsection \<open>Small implication combinators\<close>

lemma CEV_imp_trans:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
    and BC: "\<Gamma> \<turnstile>\<^sub>CEV Imp B C"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A C"
proof -
  have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp A B) (Imp (Imp B C) (Imp A C))"
  proof -
    have "prop_tautology \<Gamma>
        (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
      unfolding prop_tautology_def
      using A_type B_type C_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have tail: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp B C) (Imp A C)"
    using AB taut by (rule CEV_proves.MP)
  show ?thesis
    using BC tail by (rule CEV_proves.MP)
qed

lemma CEV_eq_prop_implication:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq Prop A B) (Imp A B)"
proof -
  let ?E = "Eq Prop A B"
  let ?IA = "App prop_id A"
  let ?IB = "App prop_id B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type B_type by (rule has_type.Eq)
  have id_type: "\<Gamma> \<turnstile> prop_id : Prop \<rightarrow>\<^sub>o Prop"
    by (rule typed_prop_id)
  have IA_type: "\<Gamma> \<turnstile> ?IA : Prop"
    using id_type A_type by (rule has_type.App)
  have IB_type: "\<Gamma> \<turnstile> ?IB : Prop"
    using id_type B_type by (rule has_type.App)
  have ll:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (Imp ?IA ?IB)"
    using A_type B_type id_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have A_IA: "\<Gamma> \<turnstile>\<^sub>CEV Imp A ?IA"
    using A_type by (rule CEV_imp_app_prop_id)
  have IB_B: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?IB B"
    using B_type by (rule CEV_app_prop_id_imp)
  have compose:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp A ?IA)
          (Imp (Imp ?IA ?IB)
            (Imp (Imp ?IB B) (Imp A B)))"
  proof -
    have "prop_tautology \<Gamma>
        (Imp (Imp A ?IA)
          (Imp (Imp ?IA ?IB)
            (Imp (Imp ?IB B) (Imp A B))))"
      unfolding prop_tautology_def
      using A_type B_type IA_type IB_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have after_A:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp ?IA ?IB) (Imp (Imp ?IB B) (Imp A B))"
    using A_IA compose by (rule CEV_proves.MP)
  have local_E: "CEV_from \<Gamma> ?E ?E"
    by (rule CEV_from.Assumption[OF E_type])
  have local_IA_IB: "CEV_from \<Gamma> ?E (Imp ?IA ?IB)"
    using local_E
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF ll]])
  have local_after_IB:
      "CEV_from \<Gamma> ?E (Imp (Imp ?IB B) (Imp A B))"
    using local_IA_IB
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF after_A]])
  have local_A_B: "CEV_from \<Gamma> ?E (Imp A B)"
    using local_after_IB
    by (rule CEV_from.MP[OF CEV_from.Theorem[OF IB_B]])
  show ?thesis
    using local_A_B E_type by (rule CEV_from_deduction)
qed

lemma CEV_eq_prop_biconditional_imp:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Eq Prop A B) (A \<longleftrightarrow>\<^sub>o B)"
proof -
  let ?E = "Eq Prop A B"
  let ?E' = "Eq Prop B A"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type B_type by (rule has_type.Eq)
  have AB: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (Imp A B)"
    using A_type B_type by (rule CEV_eq_prop_implication)
  have symmetry: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E ?E'"
    using A_type B_type by (rule CEV_eq_sym)
  have reverse: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E' (Imp B A)"
    using B_type A_type by (rule CEV_eq_prop_implication)
  have BA: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (Imp B A)"
    using E_type
      has_type.Eq[OF B_type A_type]
      has_type.Imp[OF B_type A_type]
      symmetry reverse
    by (rule CEV_imp_trans)
  have intro:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp A B)
          (Imp (Imp B A) (A \<longleftrightarrow>\<^sub>o B))"
  proof -
    have "prop_tautology \<Gamma>
        (Imp (Imp A B)
          (Imp (Imp B A) (A \<longleftrightarrow>\<^sub>o B)))"
      unfolding prop_tautology_def
      using A_type B_type by auto
    then show ?thesis by (rule CEV_prop_tautology)
  qed
  have local_E: "CEV_from \<Gamma> ?E ?E"
    by (rule CEV_from.Assumption[OF E_type])
  have local_AB: "CEV_from \<Gamma> ?E (Imp A B)"
    using local_E
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF AB]])
  have local_intro:
      "CEV_from \<Gamma> ?E
        (Imp (Imp B A) (A \<longleftrightarrow>\<^sub>o B))"
    using local_AB
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF intro]])
  have local_BA: "CEV_from \<Gamma> ?E (Imp B A)"
    using local_E
    by (rule CEV_from.MP[OF _ CEV_from.Theorem[OF BA]])
  have local_iff: "CEV_from \<Gamma> ?E (A \<longleftrightarrow>\<^sub>o B)"
    using local_BA local_intro by (rule CEV_from.MP)
  show ?thesis
    using local_iff E_type by (rule CEV_from_deduction)
qed

subsection \<open>Pointwise identity entails the Intensionality condition\<close>

definition mf_condition ::
    "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "mf_condition \<sigma> X Y =
    Forall \<sigma>
      (Eq Prop
        (App (shift X) (Var 0))
        (App (shift Y) (Var 0)))"

lemma typed_mf_condition:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> mf_condition \<sigma> X Y : Prop"
  unfolding mf_condition_def
  using typed_shift_app[OF X_type] typed_shift_app[OF Y_type]
  by (intro has_type.Forall has_type.Eq)

lemma CEV_mf_condition_UI:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (mf_condition \<sigma> X Y))
      (Eq Prop
        (App (shift X) (Var 0))
        (App (shift Y) (Var 0)))"
proof -
  let ?body =
    "Eq Prop
      (App (shift X) (Var 0))
      (App (shift Y) (Var 0))"
  have E_type: "\<Gamma> \<turnstile> mf_condition \<sigma> X Y : Prop"
    using X_type Y_type by (rule typed_mf_condition)
  have shifted_E_type:
      "\<sigma> # \<Gamma> \<turnstile> shift (mf_condition \<sigma> X Y) : Prop"
    using E_type by (rule typed_shift_ctx)
  have shifted_E:
      "shift (mf_condition \<sigma> X Y) =
        Forall \<sigma> (rename (lift_ren Suc) ?body)"
    unfolding mf_condition_def shift_def by simp
  have forall_type:
      "\<sigma> # \<Gamma> \<turnstile>
        Forall \<sigma> (rename (lift_ren Suc) ?body) : Prop"
    using shifted_E_type shifted_E by simp
  have lifted_body_type:
      "\<sigma> # \<sigma> # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?body : Prop"
    using forall_type by (cases rule: has_type.cases) auto
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule typed_var0)
  have ui:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Forall \<sigma> (rename (lift_ren Suc) ?body))
          (subst0 (Var 0) (rename (lift_ren Suc) ?body))"
    using lifted_body_type var_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have subst:
      "subst0 (Var 0) (rename (lift_ren Suc) ?body) = ?body"
    by (rule subst0_var0_lift_ren_Suc)
  show ?thesis
    using ui shifted_E subst by simp
qed

lemma CEV_mf_implies_intens_condition:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (mf_condition \<sigma> X Y) (intens_condition \<sigma> X Y)"
proof -
  let ?A = "App (shift X) (Var 0)"
  let ?B = "App (shift Y) (Var 0)"
  let ?E = "mf_condition \<sigma> X Y"
  let ?Q = "?A \<longleftrightarrow>\<^sub>o ?B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type by (rule typed_mf_condition)
  have A_type: "\<sigma> # \<Gamma> \<turnstile> ?A : Prop"
    using X_type by (rule typed_shift_app)
  have B_type: "\<sigma> # \<Gamma> \<turnstile> ?B : Prop"
    using Y_type by (rule typed_shift_app)
  have Q_type: "\<sigma> # \<Gamma> \<turnstile> ?Q : Prop"
    using A_type B_type by (intro has_type.Conj has_type.Imp)
  have ui:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift ?E) (Eq Prop ?A ?B)"
    using X_type Y_type by (rule CEV_mf_condition_UI)
  have eq_iff:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq Prop ?A ?B) ?Q"
    using A_type B_type by (rule CEV_eq_prop_biconditional_imp)
  have lifted:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift ?E) ?Q"
    using typed_shift_ctx[OF E_type]
      has_type.Eq[OF A_type B_type] Q_type ui eq_iff
    by (rule CEV_imp_trans)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (Forall \<sigma> ?Q)"
    using E_type Q_type lifted by (rule CEV_proves.Gen)
  then show ?thesis
    unfolding intens_condition_def .
qed

subsection \<open>Unary Modalized Functionality\<close>

theorem CEV_unary_modalized_functionality:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (\<box>\<^sub>o (mf_condition \<sigma> X Y))
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X Y)"
proof -
  let ?E = "mf_condition \<sigma> X Y"
  let ?C = "intens_condition \<sigma> X Y"
  let ?XY = "Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X Y"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type by (rule typed_mf_condition)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using X_type Y_type by (rule typed_intens_condition)
  have XY_type: "\<Gamma> \<turnstile> ?XY : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have E_C: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E ?C"
    using X_type Y_type by (rule CEV_mf_implies_intens_condition)
  have box_E_C: "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o (Imp ?E ?C)"
    using E_C by (rule CEV_necessitation)
  have K:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (\<box>\<^sub>o (Imp ?E ?C))
          (Imp (\<box>\<^sub>o ?E) (\<box>\<^sub>o ?C))"
    using CEV_modal_K[OF E_type C_type]
    unfolding modal_K_def .
  have box_E_box_C:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o ?E) (\<box>\<^sub>o ?C)"
    using box_E_C K by (rule CEV_proves.MP)
  have intens:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o ?C) ?XY"
    using X_type Y_type by (rule CEV_unary_intensionality)
  show ?thesis
    using typed_ObjBox[OF E_type] typed_ObjBox[OF C_type] XY_type
      box_E_box_C intens
    by (rule CEV_imp_trans)
qed

subsection \<open>The closed proposition-valued Modalized Functionality schema\<close>

lemma CEV_generalize_theorem:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and dA: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Forall \<sigma> A"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have shifted_true: "shift ObjTrue = (ObjTrue :: oterm)"
    by (simp add: ObjTrue_def shift_def)
  have d_imp: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift ObjTrue) A"
  proof -
    have "\<sigma> # \<Gamma> \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    then have "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp ObjTrue A"
      using dA CEV_taut_imp[OF A_type]
      by (blast intro: CEV_proves.MP)
    then show ?thesis by (simp add: shifted_true)
  qed
  have d_gen:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjTrue (Forall \<sigma> A)"
    using true_type A_type d_imp by (rule CEV_proves.Gen)
  show ?thesis
    using CEV_proves_ObjTrue d_gen by (rule CEV_proves.MP)
qed

theorem CEV_proves_pp_modalized_functionality_Prop:
  "[] \<turnstile>\<^sub>CEV pp_modalized_functionality \<sigma> Prop"
proof -
  let ?fun = "\<sigma> \<rightarrow>\<^sub>o Prop"
  let ?X = "Var 1 :: oterm"
  let ?Y = "Var 0 :: oterm"
  let ?body =
    "Imp (\<box>\<^sub>o (mf_condition \<sigma> ?X ?Y))
      (Eq ?fun ?X ?Y)"
  have X_type: "[?fun, ?fun] \<turnstile> ?X : ?fun"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "[?fun, ?fun] \<turnstile> ?Y : ?fun"
    by (rule has_type.Var) (simp add: lookup_def)
  have body_type: "[?fun, ?fun] \<turnstile> ?body : Prop"
    using typed_mf_condition[OF X_type Y_type] X_type Y_type
    by (intro has_type.Imp typed_ObjBox has_type.Eq)
  have d_body: "[?fun, ?fun] \<turnstile>\<^sub>CEV ?body"
    using X_type Y_type by (rule CEV_unary_modalized_functionality)
  have inner_type:
      "[?fun] \<turnstile> Forall ?fun ?body : Prop"
    using body_type by (rule has_type.Forall)
  have d_inner: "[?fun] \<turnstile>\<^sub>CEV Forall ?fun ?body"
    using body_type d_body by (rule CEV_generalize_theorem)
  have d_closed:
      "[] \<turnstile>\<^sub>CEV Forall ?fun (Forall ?fun ?body)"
    using inner_type d_inner by (rule CEV_generalize_theorem)
  show ?thesis
    using d_closed
    by (simp add: pp_modalized_functionality_def mf_condition_def shift_def
        numeral_2_eq_2)
qed

theorem CEV_proves_proposition_valued_modalized_functionality_schema:
  assumes "A \<in>
    pp_proposition_valued_modalized_functionality_schema"
  shows "[] \<turnstile>\<^sub>CEV A"
  using assms CEV_proves_pp_modalized_functionality_Prop
  unfolding pp_proposition_valued_modalized_functionality_schema_def
  by blast

text \<open>
  Thus every proposition-valued member of the schema is derivable in bare
  \<open>CEV\<close>.  This theorem does not extend the result type from \<open>Prop\<close> to an
  arbitrary object-language type.
\<close>

end
