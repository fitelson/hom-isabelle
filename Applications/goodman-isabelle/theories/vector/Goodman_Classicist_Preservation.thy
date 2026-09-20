theory Goodman_Classicist_Preservation
  imports Goodman_Vector_Translation
begin

theorem gi_HLE_preservation:
  assumes rich: "sg_rich G" and derivation: "HLE_proves \<Gamma> A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G ns k A)"
  using derivation chart distinct
proof (induction arbitrary: ns rule: HLE_proves.induct)
  case H
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
    rule gi_H_universal_preservation[OF rich H.hyps H.prems])
next
  case (LogicalEquivalence \<Gamma> F \<Delta> H)
  let ?ps = "gi_prefix G \<Delta> ns"
  have f: "\<Gamma> \<turnstile> F : arrow_type (gi_order True \<Delta>) Prop"
    using LogicalEquivalence.hyps(1) by (simp add: H_rule_arrow_bridge gi_order_def)
  have h: "\<Gamma> \<turnstile> H : arrow_type (gi_order True \<Delta>) Prop"
    using LogicalEquivalence.hyps(2) by (simp add: H_rule_arrow_bridge gi_order_def)
  have ext: "map G (?ps @ ns) = \<Delta> @ \<Gamma>"
    by (simp add: gi_prefix_types[OF rich] LogicalEquivalence.prems(1))
  have d: "distinct (?ps @ ns)" by (rule gi_prefix_distinct[OF rich LogicalEquivalence.prems(2)])
  have premise_H: "book_H (\<lambda>_. UNIV) G (gi_to_book G (?ps @ ns) k (H_rule_body \<Delta> F H))"
    by (rule gi_H_universal_preservation[OF rich LogicalEquivalence.hyps(3) ext d])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G T
    (gi_to_book G (?ps @ ns) k (gi_vec_body True \<Delta> F H))"
    using goodman_book_proves.Base[OF book_full_C_proves.H[OF premise_H]]
    by (simp only: gi_H_body_order)
  have result: "goodman_book_proves (\<lambda>_. UNIV) G T
    (gi_to_book G ns k (Eq (arrow_type (gi_order True \<Delta>) Prop) F H))"
    by (rule gi_ordered_vector_rule[OF rich f h LogicalEquivalence.prems
      gi_constants_universal gi_constants_universal premise])
  show ?case using result by (simp only: H_rule_arrow_bridge gi_order_def if_True)
next
  case (MP \<Gamma> A B)
  have bt: "\<Gamma> \<turnstile> B : Prop" by (rule HLE_proves_formula, rule HLE_proves.MP[OF MP.hyps])
  have bl: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns k B)"
    by (rule gi_to_book_language[OF rich bt MP.prems(1) gi_constants_universal])
  have first: "goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G ns k A)" by (rule MP.IH(1)[OF MP.prems])
  have second: "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_imp (gi_to_book G ns k A) (gi_to_book G ns k B))"
    using MP.IH(2)[OF MP.prems] by (simp only: gi_to_book.simps)
  show ?case by (rule goodman_book_proves.MP[OF first second bl])
next
  case (Gen \<Gamma> P \<sigma> Q)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have ext: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Gen.prems(1)])
  have d: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Gen.prems(2)])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G (?n # ns) k (Imp (shift P) Q))"
    by (rule Gen.IH[OF ext d])
  show ?case by (rule gi_goodman_translated_Gen[OF rich Gen.hyps(1,2) Gen.prems
    gi_constants_universal gi_constants_universal premise])
next
  case (Inst \<sigma> \<Gamma> P Q)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have ext: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Inst.prems(1)])
  have d: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Inst.prems(2)])
  have premise: "goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G (?n # ns) k (Imp P (shift Q)))"
    by (rule Inst.IH[OF ext d])
  show ?case by (rule gi_goodman_translated_Inst[OF rich Inst.hyps(1,2) Inst.prems
    gi_constants_universal gi_constants_universal premise])
qed

theorem gi_C_preservation:
  "sg_rich G \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C A \<Longrightarrow> map G ns = \<Gamma> \<Longrightarrow> distinct ns \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G ns k A)"
  by (rule gi_HLE_preservation; (assumption | rule C_proves_to_HLE); assumption)

theorem gi_CEV_base_preservation:
  "sg_rich G \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> map G ns = \<Gamma> \<Longrightarrow> distinct ns \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G T (gi_to_book G ns k A)"
  by (rule gi_C_preservation; (assumption | rule CEV_proves_to_C); assumption)

corollary gi_CEV_to_book_full_C:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> \<turnstile>\<^sub>CEV A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "book_full_C_proves (\<lambda>_. UNIV) G (gi_to_book G ns k A)"
  using gi_CEV_base_preservation[OF rich derivation chart distinct, where T="{}"]
  by (simp only: goodman_book_empty_iff)

text \<open>
  This is forward preservation into the universal target signature. The
  represented C↔HLE and CEV→C bridges are explicitly invoked, not assumed.
  No reflection or signature-conservativity theorem for C+[T] is inferred.
\<close>

end
