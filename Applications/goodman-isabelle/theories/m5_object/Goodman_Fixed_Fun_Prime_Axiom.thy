theory Goodman_Fixed_Fun_Prime_Axiom
  imports Goodman_M5_Object_Transfer
begin

section \<open>A fixed fun′ witness cannot be an axiom of this background\<close>

lemma gi_fixed_fun_prime_truth_pure:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjTrue"
proof -
  have axiom: "pp_pure Prop ObjTrue \<in> pp_purity_schema"
    unfolding pp_purity_schema_def pp_logical_vocabulary_def
  proof (intro CollectI exI conjI)
    show "[] \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
    show "consts_of ObjTrue = {}" by (simp add: ObjTrue_def)
  qed simp
  have member: "pp_pure Prop ObjTrue \<in> T" using core axiom unfolding pp_T2_min_axioms_def by blast
  show ?thesis by (rule CEV_axiom_proves.Axiom[OF member typed_pp_pure[OF typed_ObjTrue]])
qed

theorem gi_fixed_fun_prime_theorem_collapses_minimal_stock:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
    and fp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_fun_prime r"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?E = "Eq Prop r ObjTrue"
  have et: "\<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Eq[OF rt typed_ObjTrue])
  have not_equal: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?E"
    by (rule CEV_axiom_proves.MP[OF fp CEV_fun_prime_neq_ObjTrue[OF core rt]])
  have necessary: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjBox (Neg ?E)"
    by (rule CEV_axiom_necessitation[OF not_equal])
  have attain: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Imp (pp_pure Prop ObjTrue) (ObjDiamond ?E))"
    by (rule CEV_Goodman_T2c_parameter[OF core rt typed_ObjTrue])
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_pure Prop ObjTrue) (ObjDiamond ?E)"
    by (rule CEV_axiom_proves.MP[OF fp attain])
  have possible: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjDiamond ?E"
    by (rule CEV_axiom_proves.MP[OF gi_fixed_fun_prime_truth_pure[OF core] step])
  have opposite: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (ObjBox (Neg ?E))"
    using possible by (simp only: ObjDiamond_def)
  have bt: "\<Gamma> \<turnstile> ObjBox (Neg ?E) : Prop" by (rule typed_ObjBox, rule has_type.Neg[OF et])
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (ObjBox (Neg ?E)) (Imp (Neg (ObjBox (Neg ?E))) ObjFalse)"
    by (rule CEVp_M5_propositional) (use bt typed_ObjFalse in auto)
  have contradiction: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg (ObjBox (Neg ?E))) ObjFalse"
    by (rule CEV_axiom_proves.MP[OF necessary taut])
  show ?thesis by (rule CEV_axiom_proves.MP[OF opposite contradiction])
qed

corollary gi_fixed_fun_prime_axiom_collapses_minimal_stock:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
    and fp: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  by (rule gi_fixed_fun_prime_theorem_collapses_minimal_stock[OF core rt],
    rule CEV_axiom_proves.Axiom[OF fp typed_pp_fun_prime[OF rt]])

theorem gi_fixed_fun_prime_axiom_native_refutation:
  assumes rich: "sg_rich G" and core: "pp_T2_min_axioms \<subseteq> T"
    and rt: "[] \<turnstile> r : Prop" and fp: "pp_fun_prime r \<in> T"
    and closed: "\<And>A. A \<in> T \<Longrightarrow> [] \<turnstile> A : Prop"
    and admitted: "\<And>A. A \<in> T \<Longrightarrow> gi_constants_admitted k \<Sigma> A"
  shows "goodman_book_proves \<Sigma> G (gi_to_book G [] k ` T) (book_bottom G)"
  by (rule gi_CEV_closed_refutation_in_signature[OF rich
    gi_fixed_fun_prime_axiom_collapses_minimal_stock[OF core rt fp] closed admitted])

text \<open>
  This sharpens the older PP-core collapse proof to logical purity and
  application closure alone. Nontriviality gives r≠⊤ as a theorem, hence
  □(r≠⊤); attainment gives ◇(r=⊤). Their contradiction uses Necessitation
  above the axiom stock. It does not refute a merely local fun′(r), or
  ∃r.fun′(r), and does not answer the PP consistency question.

  In particular the inherited M5 collision theorem's axiom stock is
  already inconsistent. Its derivation must not be advertised as evidence
  for a nonexplosive local collision statement without a separate proof.
\<close>

end
