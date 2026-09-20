theory Goodman_M5_Object_Transfer
  imports Goodman_Legacy_M5_Invertibles.Bacon_PP_Goodman_M5_Existential_Invertibles
    Goodman_Integration_Individual.Goodman_T45_Transfer
begin

section \<open>M5: inverse witnesses and collision proofs have different scopes\<close>

text \<open>
  Reversibility implies injectivity without added Goodman axioms. By
  contrast the historical collision calculation takes fun′(r) as an
  AXIOM, and uses Equivalence above that axiom. We preserve that exact
  consequence relation. We do not silently discharge it to a local
  implication fun′(r) → collision over the smaller background.
\<close>

definition gi_M5_collision_result where
  "gi_M5_collision_result r = Conj
    (Neg (Eq Prop (pp_noncontingent r) ObjTrue))
    (Eq Prop (App pp_M5_collision_operator (pp_noncontingent r))
      (App pp_M5_collision_operator ObjTrue))"

lemma gi_M5_collision_source:
  "pp_T2_min_axioms \<subseteq> T \<Longrightarrow> \<Gamma> \<turnstile> r : Prop \<Longrightarrow>
    pp_fun_prime r \<in> T \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_M5_collision_result r"
  unfolding gi_M5_collision_result_def by (rule CEV_Goodman_M5_collision)

theorem gi_M5_collision_in_signature:
  assumes rich: "sg_rich G" and core: "pp_T2_min_axioms \<subseteq> T"
    and rt: "\<Gamma> \<turnstile> r : Prop" and fp_axiom: "pp_fun_prime r \<in> T"
    and closed: "\<And>A. A \<in> T \<Longrightarrow> [] \<turnstile> A : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and axioms: "\<And>A. A \<in> T \<Longrightarrow> gi_constants_admitted k \<Sigma> A"
    and conclusion: "gi_constants_admitted k \<Sigma> (gi_M5_collision_result r)"
  shows "goodman_book_proves \<Sigma> G (gi_to_book G [] k ` T)
    (gi_to_book G ns k (gi_M5_collision_result r))"
  by (rule gi_CEV_axiom_preservation_in_signature[OF rich gi_M5_collision_source[OF core rt fp_axiom]
    closed chart distinct axioms conclusion])

theorem gi_M5_nonreversible_in_signature:
  assumes rich: "sg_rich G" and core: "pp_T2_min_axioms \<subseteq> T"
    and rt: "\<Gamma> \<turnstile> r : Prop" and fp_axiom: "pp_fun_prime r \<in> T"
    and closed: "\<And>A. A \<in> T \<Longrightarrow> [] \<turnstile> A : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and axioms: "\<And>A. A \<in> T \<Longrightarrow> gi_constants_admitted k \<Sigma> A"
    and conclusion: "gi_constants_admitted k \<Sigma> (Neg (pp_reversible pp_M5_collision_operator))"
  shows "goodman_book_proves \<Sigma> G (gi_to_book G [] k ` T)
    (gi_to_book G ns k (Neg (pp_reversible pp_M5_collision_operator)))"
  by (rule gi_CEV_axiom_preservation_in_signature[OF rich
    CEV_Goodman_M5_collision_operator_not_reversible[OF core rt fp_axiom]
    closed chart distinct axioms conclusion])

section \<open>Injectivity is an actual implication in the empty extension\<close>

theorem gi_M5_inverse_witness_injective:
  assumes rich: "sg_rich G" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and wt: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and pt: "\<Gamma> \<turnstile> p : Prop" and qt: "\<Gamma> \<turnstile> q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k \<Sigma>
      (Imp (pp_inverse_witness Z W) (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q)))"
  shows "goodman_book_proves \<Sigma> G {}
    (gi_to_book G ns k (Imp (pp_inverse_witness Z W)
      (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))))"
proof -
  have source: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_inverse_witness Z W) (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))"
    by (rule CEV_M5_inverse_witness_injective[OF zt wt pt qt])
  have image: "goodman_book_proves \<Sigma> G (gi_to_book G [] k ` {})
    (gi_to_book G ns k (Imp (pp_inverse_witness Z W)
      (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))))"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich source _ chart distinct _ admitted]; simp)
  show ?thesis using image by simp
qed

theorem gi_M5_reversible_injective:
  assumes rich: "sg_rich G" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pt: "\<Gamma> \<turnstile> p : Prop" and qt: "\<Gamma> \<turnstile> q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k \<Sigma>
      (Imp (pp_reversible Z) (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q)))"
  shows "goodman_book_proves \<Sigma> G {}
    (gi_to_book G ns k (Imp (pp_reversible Z)
      (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))))"
proof -
  have source: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_reversible Z) (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))"
    by (rule CEV_M5_reversible_injective[OF zt pt qt])
  have image: "goodman_book_proves \<Sigma> G (gi_to_book G [] k ` {})
    (gi_to_book G ns k (Imp (pp_reversible Z)
      (Imp (Eq Prop (App Z p) (App Z q)) (Eq Prop p q))))"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich source _ chart distinct _ admitted]; simp)
  show ?thesis using image by simp
qed

text \<open>
  All target signatures are arbitrary subject to the displayed admission
  guards. No universal-signature restriction, PP, QSS, Recombination or
  existence of a fundamental proposition enters the inverse implication.
  The other two results retain their image stock and closed-added-axiom
  premise. A root counterexample or separate native antecedent theorem is
  required before resolving stronger prose claims about the collision.
\<close>

end
