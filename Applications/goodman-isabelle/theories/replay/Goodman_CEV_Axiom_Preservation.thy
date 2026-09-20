theory Goodman_CEV_Axiom_Preservation
  imports Goodman_Integration_Vector.Goodman_Classicist_Preservation
    Goodman_Legacy_01.Bacon_CEV_Axiom_Extension
begin

section \<open>Whole-proof preservation of CEV+ with a closed added stock\<close>

theorem gi_CEV_axiom_preservation:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and closed: "\<And>B. B \<in> T \<Longrightarrow> [] \<turnstile> B : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T) (gi_to_book G ns k A)"
  using derivation closed chart distinct
proof (induction arbitrary: ns rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  have empty: "[] \<turnstile> A : Prop" by (rule Axiom.prems(1)[OF Axiom.hyps(1)])
  show ?case by (rule gi_goodman_closed_axiom[OF rich Axiom.hyps(1) empty Axiom.prems(3) gi_constants_universal])
next
  case Base
  show ?case by (rule gi_CEV_base_preservation[OF rich Base.hyps Base.prems(2,3)])
next
  case (VectorEquivalence \<Gamma> F \<sigma>s H T)
  let ?ps = "gi_prefix G \<sigma>s ns"
  have ext: "map G (?ps @ ns) = \<sigma>s @ \<Gamma>"
    by (simp add: gi_prefix_types[OF rich] VectorEquivalence.prems(2))
  have d: "distinct (?ps @ ns)" by (rule gi_prefix_distinct[OF rich VectorEquivalence.prems(3)])
  have original: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G (?ps @ ns) k (zeta_body \<sigma>s F H))"
    by (rule VectorEquivalence.IH[OF VectorEquivalence.prems(1) ext d])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G (?ps @ ns) k (gi_vec_body False \<sigma>s F H))"
    using original by (simp only: gi_zeta_body_order)
  have f: "\<Gamma> \<turnstile> F : arrow_type (gi_order False \<sigma>s) Prop"
    and h: "\<Gamma> \<turnstile> H : arrow_type (gi_order False \<sigma>s) Prop"
    using VectorEquivalence.hyps(1,2) by (simp_all add: gi_order_def)
  have result: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G ns k (Eq (arrow_type (gi_order False \<sigma>s) Prop) F H))"
    by (rule gi_ordered_vector_rule[OF rich f h VectorEquivalence.prems(2,3)
      gi_constants_universal gi_constants_universal premise])
  show ?case using result by (simp only: gi_order_def if_False)
next
  case (MP \<Gamma> T A B)
  have bt: "\<Gamma> \<turnstile> B : Prop" by (rule CEV_axiom_proves_formula, rule CEV_axiom_proves.MP[OF MP.hyps])
  have bl: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns k B)"
    by (rule gi_to_book_language[OF rich bt MP.prems(2) gi_constants_universal])
  have first: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T) (gi_to_book G ns k A)"
    by (rule MP.IH(1)[OF MP.prems])
  have second: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (book_imp (gi_to_book G ns k A) (gi_to_book G ns k B))"
    using MP.IH(2)[OF MP.prems] by (simp only: gi_to_book.simps)
  show ?case by (rule goodman_book_proves.MP[OF first second bl])
next
  case (Gen \<Gamma> P \<sigma> Q T)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have ext: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Gen.prems(2)])
  have d: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Gen.prems(3)])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G (?n # ns) k (Imp (shift P) Q))"
    by (rule Gen.IH[OF Gen.prems(1) ext d])
  show ?case by (rule gi_goodman_translated_Gen[OF rich Gen.hyps(1,2) Gen.prems(2,3)
    gi_constants_universal gi_constants_universal premise])
next
  case (Inst \<sigma> \<Gamma> P Q T)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have ext: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Inst.prems(2)])
  have d: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Inst.prems(3)])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G (?n # ns) k (Imp P (shift Q)))"
    by (rule Inst.IH[OF Inst.prems(1) ext d])
  show ?case by (rule gi_goodman_translated_Inst[OF rich Inst.hyps(1,2) Inst.prems(2,3)
    gi_constants_universal gi_constants_universal premise])
qed

section \<open>Translate a refutation to the book's actual bottom formula\<close>

lemma gi_H_translated_false_elim:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (book_imp (gi_to_book G [] k ObjFalse) (book_bottom G))"
proof -
  let ?B = "Forall Prop (Var 0)"
  have typed: "[] \<turnstile> Imp ObjTrue (Imp ObjFalse ?B) : Prop"
    by (rule infer_type_sound; simp add: ObjTrue_def ObjFalse_def lookup_def)
  have taut: "[] \<turnstile>\<^sub>H Imp ObjTrue (Imp ObjFalse ?B)"
    by (rule H_proves.PC; unfold prop_tautology_def; rule conjI[OF typed]; simp add: ObjFalse_def)
  have old: "[] \<turnstile>\<^sub>H Imp ObjFalse ?B"
    by (rule H_proves.MP[OF H_proves_ObjTrue taut])
  have constants: "gi_constants_admitted k \<Sigma> (Imp ObjFalse ?B)"
    by (simp add: ObjFalse_def ObjTrue_def)
  have transferred: "book_H \<Sigma> G (gi_to_book G [] k (Imp ObjFalse ?B))"
    by (rule gi_H_closed_preservation[OF rich old constants])
  show ?thesis using transferred
    by (simp only: gi_to_book.simps Let_def nth_Cons_0 book_all_def
      named_chart_fresh_type[OF rich] book_bottom_def book_prop_name_def)
qed

theorem gi_CEV_closed_refutation:
  assumes rich: "sg_rich G" and refutation: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    and closed: "\<And>A. A \<in> T \<Longrightarrow> [] \<turnstile> A : Prop"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T) (book_bottom G)"
proof -
  have translated: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (gi_to_book G [] k ObjFalse)"
    by (rule gi_CEV_axiom_preservation[OF rich refutation closed]; simp)
  have implication: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) T)
    (book_imp (gi_to_book G [] k ObjFalse) (book_bottom G))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule gi_H_translated_false_elim[OF rich])
  show ?thesis by (rule goodman_book_proves.MP[OF translated implication book_bottom_language[OF rich]])
qed

text \<open>
  The image stock is fixed, all source axioms are closed, and every
  CEV+ proof constructor is covered. The target signature is universal.
  This is forward preservation, not converse consistency or a claim that
  the image stock equals every independently written source axiom package.
\<close>

end
