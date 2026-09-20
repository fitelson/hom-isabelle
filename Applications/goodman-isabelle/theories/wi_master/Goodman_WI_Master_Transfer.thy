theory Goodman_WI_Master_Transfer
  imports
    "Goodman_Legacy_WI_Master.Bacon_PP_Goodman_T6_WI_Master"
    "Goodman_Integration_Native_Extras.Goodman_Native_T6_Extras"
begin

section \<open>Direct WI master equations: exact hypotheses and translated conclusions\<close>

text \<open>
  Write d = Dr and a_A = D(d ↔ A). The advertised equation is
  a_A ↔ ∀C(Pure(C) → (a_C ↔ ¬A)). These theorems transfer the direct
  derivations of that equation, not the later ex-falso proof from T6.
  Parameter results retain fun′(r), and pointwise results additionally
  retain Pure(A), as object-language antecedents. Their stock contains
  logical purity, application closure, PP, L2, and WI; no existence
  assumption is needed for the parameter conditionals.

  The extras L2 and WI in the stock are independently defined native
  formulas. Conclusions explicitly marked translated retain gi_to_book;
  no independent named definition of the master family is asserted here.
\<close>

definition gi_WI_master_source_stock :: "oterm set" where
  "gi_WI_master_source_stock = pp_T6_core_PP_axioms \<union> {pp_L2, pp_WI}"

definition gb_WI_master_stock where
  "gb_WI_master_stock G = gb_T6_core G \<union> {gb_L2 G, gb_WI G}"

lemma gi_WI_master_source_closed:
  "B \<in> gi_WI_master_source_stock \<Longrightarrow> [] \<turnstile> B : Prop"
  unfolding gi_WI_master_source_stock_def
  by (auto intro: gi_T6_core_closed typed_pp_L2 typed_pp_WI)

lemma gb_WI_master_stock_language:
  "sg_rich G \<Longrightarrow> B \<in> gb_WI_master_stock G \<Longrightarrow>
    book_theory_formula gb_signature G B"
  unfolding gb_WI_master_stock_def
  by (auto intro: gb_T6_core_language gb_L2_language_closed(1) gb_WI_language_closed(1))

lemma gi_WI_master_stock_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) gi_WI_master_source_stock \<subseteq> gb_WI_master_stock G"
  using gi_T6_core_inclusion[OF rich names]
  by (auto simp: gi_WI_master_source_stock_def gb_WI_master_stock_def
      gi_L2_native_translation[OF names] gi_WI_native_translation[OF names])

lemma gi_WI_master_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; gi_WI_master_source_stock \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_WI_master_stock G)
    (gi_to_book G ns k A)"
proof -
  have image_proof: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) gi_WI_master_source_stock) (gi_to_book G ns k A)"
    by (rule gi_CEV_axiom_preservation[OF rich derivation gi_WI_master_source_closed chart distinct])
  have native_proof: "goodman_book_proves (\<lambda>_. UNIV) G
      (gb_WI_master_stock G) (gi_to_book G ns k A)"
    by (rule goodman_book_mono[OF image_proof gi_WI_master_stock_inclusion[OF rich names]])
  show ?thesis
    by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
        native_proof gb_WI_master_stock_language[OF rich]])
qed

section \<open>Signature checks are occurrence-sensitive, including arbitrary parameters\<close>

lemma gi_WI_master_a_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature A \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T6_WI_a r A)"
  by (simp add: pp_T6_WI_a_def pp_T6_liar_def pp_biconditional_operator_def
      pp_biconditional_builder_def gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
      gi_goodman_names_def gb_signature_def)

lemma gi_WI_master_operator_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T6_WI_a_operator r)"
  by (simp add: pp_T6_WI_a_operator_def gi_WI_master_a_admitted
      shift_def gi_constants_rename)

lemma gi_WI_master_at_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature a \<Longrightarrow>
    gi_constants_admitted k gb_signature A \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T6_WI_master_at a A)"
  by (simp add: pp_T6_WI_master_at_def pp_pure_def pp_Pure_def
      gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

lemma gi_WI_master_family_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature a \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T6_WI_master_family a)"
  by (simp add: pp_T6_WI_master_family_def gi_WI_master_at_admitted
      pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def
      shift_def gi_constants_rename)

lemma gi_WI_advertised_master_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature r \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T6_WI_advertised_master r)"
  by (simp add: pp_T6_WI_advertised_master_def
      gi_WI_master_family_admitted gi_WI_master_operator_admitted)

lemma gi_WI_advertised_claim_admitted:
  "gi_goodman_names k \<Longrightarrow>
    gi_constants_admitted k gb_signature pp_T6_WI_advertised_master_claim"
  by (simp add: pp_T6_WI_advertised_master_claim_def
      gi_T2_fun_prime_admitted gi_WI_advertised_master_admitted)

section \<open>Pointwise and family derivations, without an existential axiom\<close>

theorem gi_WI_master_pointwise_direct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and at: "\<Gamma> \<turnstile> A : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and aa: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_WI_master_stock G)
    (gi_to_book G ns k
      (Imp (Conj (pp_fun_prime r) (pp_pure Prop A))
        (pp_T6_WI_a r A \<longleftrightarrow>\<^sub>o
          Forall Prop (Imp (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0) \<longleftrightarrow>\<^sub>o Neg (shift A))))))"
proof -
  have source: "\<Gamma> ; gi_WI_master_source_stock \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_fun_prime r) (pp_pure Prop A))
        (pp_T6_WI_a r A \<longleftrightarrow>\<^sub>o
          Forall Prop (Imp (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0) \<longleftrightarrow>\<^sub>o Neg (shift A))))"
    by (rule CEV_T6_WI_master_at_direct[OF _ _ _ rt at];
        auto simp: gi_WI_master_source_stock_def)
  show ?thesis
    by (rule gi_WI_master_preservation[OF rich names source chart distinct];
        use names ra aa in \<open>simp add: gi_T2_fun_prime_admitted gi_WI_master_a_admitted
          pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def
          shift_def gi_constants_rename\<close>)
qed

theorem gi_WI_master_operator_pointwise_direct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and at: "\<Gamma> \<turnstile> A : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
    and aa: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_WI_master_stock G)
    (gi_to_book G ns k
      (Imp (Conj (pp_fun_prime r) (pp_pure Prop A))
        (pp_T6_WI_master_at (pp_T6_WI_a_operator r) A)))"
proof -
  have source: "\<Gamma> ; gi_WI_master_source_stock \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj (pp_fun_prime r) (pp_pure Prop A))
        (pp_T6_WI_master_at (pp_T6_WI_a_operator r) A)"
    by (rule CEV_T6_WI_master_at_operator_direct[OF _ _ _ rt at];
        auto simp: gi_WI_master_source_stock_def)
  show ?thesis
    by (rule gi_WI_master_preservation[OF rich names source chart distinct];
        use names ra aa in \<open>simp add: gi_T2_fun_prime_admitted
          gi_WI_master_at_admitted gi_WI_master_operator_admitted
          pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def\<close>)
qed

theorem gi_WI_master_family_direct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_WI_master_stock G)
    (gi_to_book G ns k
      (Imp (pp_fun_prime r)
        (Forall Prop (Imp (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0) \<longleftrightarrow>\<^sub>o
            Forall Prop (Imp (pp_pure Prop (Var 0))
              (pp_T6_WI_a (shift (shift r)) (Var 0)
                \<longleftrightarrow>\<^sub>o Neg (Var 1))))))))"
proof -
  have source: "\<Gamma> ; gi_WI_master_source_stock \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime r)
        (Forall Prop (Imp (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0) \<longleftrightarrow>\<^sub>o
            Forall Prop (Imp (pp_pure Prop (Var 0))
              (pp_T6_WI_a (shift (shift r)) (Var 0)
                \<longleftrightarrow>\<^sub>o Neg (Var 1))))))"
    by (rule CEV_T6_WI_master_family_direct[OF _ _ _ rt];
        auto simp: gi_WI_master_source_stock_def)
  show ?thesis
    by (rule gi_WI_master_preservation[OF rich names source chart distinct];
        use names ra in \<open>simp add: gi_T2_fun_prime_admitted gi_WI_master_a_admitted
          pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def
          shift_def gi_constants_rename\<close>)
qed

theorem gi_WI_advertised_family_direct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_WI_master_stock G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_T6_WI_advertised_master r)))"
proof -
  have source: "\<Gamma> ; gi_WI_master_source_stock \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime r) (pp_T6_WI_advertised_master r)"
    by (rule CEV_T6_WI_advertised_master_direct[OF _ _ _ rt];
        auto simp: gi_WI_master_source_stock_def)
  show ?thesis
    by (rule gi_WI_master_preservation[OF rich names source chart distinct];
        use names ra in \<open>simp add: gi_T2_fun_prime_admitted gi_WI_advertised_master_admitted\<close>)
qed

section \<open>The closed advertised claim: retain its original source stock\<close>

theorem gi_WI_advertised_closed_claim_direct_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_WI G})
    (gi_to_book G [] k pp_T6_WI_advertised_master_claim)"
proof -
  let ?U = "gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_WI G}"
  have image_proof: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) pp_T6_WI_axioms)
      (gi_to_book G [] k pp_T6_WI_advertised_master_claim)"
    by (rule gi_CEV_axiom_preservation[OF rich
          CEV_Goodman_T6_WI_advertised_master_claim_direct gi_T6_WI_closed]; simp)
  have inclusion: "image (gi_to_book G [] k) pp_T6_WI_axioms \<subseteq> ?U"
    using gi_T6_core_inclusion[OF rich names]
    by (auto simp: pp_T6_WI_axioms_def gi_exists_fun_prime_translation[OF names]
        gi_L2_native_translation[OF names] gi_WI_native_translation[OF names])
  have native_proof: "goodman_book_proves (\<lambda>_. UNIV) G ?U
      (gi_to_book G [] k pp_T6_WI_advertised_master_claim)"
    by (rule goodman_book_mono[OF image_proof inclusion])
  have existence_language: "book_theory_formula gb_signature G (gb_exists_fun_prime G)"
  proof -
    have "book_theory_formula gb_signature G (gi_to_book G [] k pp_exists_fun_prime)"
      by (rule gi_to_book_language[OF rich typed_pp_exists_fun_prime _
            gi_exists_fun_prime_admitted[OF names]]; simp)
    then show ?thesis by (simp only: gi_exists_fun_prime_translation[OF names])
  qed
  show ?thesis
  proof (rule gi_native_conclusion_restrict[OF rich
        CEV_Goodman_T6_WI_advertised_master_claim_direct _
        gi_WI_advertised_claim_admitted[OF names] native_proof])
    show "map G [] = []" by simp
  next
    fix B assume "B \<in> ?U"
    then show "book_theory_formula gb_signature G B"
      by (auto intro: gb_T6_core_language[OF rich]
          existence_language
          gb_L2_language_closed(1)[OF rich] gb_WI_language_closed(1)[OF rich])
  qed
qed

section \<open>Inconsistency of the master family itself\<close>

text \<open>
  For every closed unary operator a, Pure(⊤) together with its full master
  family is inconsistent. This result does not require WI, L2, PP, or a
  fundamental proposition. It is a separate logical calculation, not a
  proof of the master family. The displayed input stock is its exact
  translated image; arbitrary source constants require explicit admission.
\<close>

theorem gi_WI_master_family_inconsistent_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and at: "[] \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and aa: "gi_constants_admitted k gb_signature a"
  shows "goodman_book_proves gb_signature G
    (image (gi_to_book G [] k) {pp_pure Prop ObjTrue, pp_T6_WI_master_family a})
    (book_bottom G)"
proof -
  let ?T = "{pp_pure Prop ObjTrue, pp_T6_WI_master_family a}"
  have family_type: "[] \<turnstile> pp_T6_WI_master_family a : Prop"
    by (rule typed_pp_T6_WI_master_family[OF at])
  have pure_type: "[] \<turnstile> pp_pure Prop ObjTrue : Prop"
    by (rule typed_pp_pure[OF typed_ObjTrue])
  have family: "[] ; ?T \<turnstile>\<^sub>CEV\<^sup>+ pp_T6_WI_master_family a"
    by (rule CEV_axiom_proves.Axiom[OF _ family_type]; simp)
  have source: "[] ; ?T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    by (rule CEV_T6_WI_master_family_inconsistent[OF at _ family]; simp)
  show ?thesis
  proof (rule gi_CEV_closed_refutation_in_signature[OF rich source])
    fix B assume "B \<in> ?T"
    then show "[] \<turnstile> B : Prop" using pure_type family_type by auto
  next
    fix B assume "B \<in> ?T"
    then show "gi_constants_admitted k gb_signature B"
      using names aa gi_WI_master_family_admitted[OF names aa]
      by (auto simp: pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def ObjTrue_def)
  qed
qed

end
