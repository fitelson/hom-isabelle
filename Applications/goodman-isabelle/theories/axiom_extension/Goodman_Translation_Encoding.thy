theory Goodman_Translation_Encoding
  imports Goodman_Logical_Expansion
begin

section \<open>The named translation re-encodes to the logical expansion\<close>

theorem gi_to_book_relative_encoding:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "named_to_source G ns (gi_to_book G ns k A) = gi_expand G k A"
  using typed chart distinct
proof (induction arbitrary: ns rule: has_type.induct)
  case Var
  have bound: "n < length ns" if "lookup \<Gamma> n = Some \<sigma>" and "map G ns = \<Gamma>" for \<Gamma> n \<sigma>
    using that by (auto simp: lookup_def split: if_splits)
  show ?case using named_index_nth_distinct[OF Var.prems(2) bound[OF Var.hyps Var.prems(1)]]
    by simp
next
  case Const
  show ?case by simp
next
  case App
  then show ?case by simp
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have body: "named_to_source G (?n # ns) (gi_to_book G (?n # ns) k A) = gi_expand G k A"
    by (rule Lam.IH[OF gi_chart_extension[OF rich Lam.prems(1)]
      gi_binder_chart_distinct[OF rich Lam.prems(2)]])
  show ?case by (simp add: Let_def named_chart_fresh_type[OF rich] body)
next
  case Eq
  show ?case by (simp only: gi_to_book.simps gi_expand.simps book_leibniz_def named_to_source.simps
    gi_closed_code_stack[OF book_leibniz_const_closed, where ns=ns]
    Eq.IH(1)[OF Eq.prems] Eq.IH(2)[OF Eq.prems])
next
  case Neg
  show ?case by (simp only: gi_to_book.simps gi_expand.simps book_not_def named_to_source.simps
    gi_closed_code_stack[OF book_not_const_closed, where ns=ns] Neg.IH[OF Neg.prems])
next
  case Conj
  show ?case by (simp only: gi_to_book.simps gi_expand.simps book_and_def named_to_source.simps
    gi_closed_code_stack[OF book_and_const_closed, where ns=ns]
    Conj.IH(1)[OF Conj.prems] Conj.IH(2)[OF Conj.prems])
next
  case Disj
  show ?case by (simp only: gi_to_book.simps gi_expand.simps book_or_def named_to_source.simps
    gi_closed_code_stack[OF book_or_const_closed, where ns=ns]
    Disj.IH(1)[OF Disj.prems] Disj.IH(2)[OF Disj.prems])
next
  case Imp
  then show ?case by (simp add: book_imp_def)
next
  case (Forall \<sigma> \<Gamma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have body: "named_to_source G (?n # ns) (gi_to_book G (?n # ns) k A) = gi_expand G k A"
    by (rule Forall.IH[OF gi_chart_extension[OF rich Forall.prems(1)]
      gi_binder_chart_distinct[OF rich Forall.prems(2)]])
  show ?case by (simp add: Let_def book_all_def named_chart_fresh_type[OF rich] body)
next
  case (Exists \<sigma> \<Gamma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have body: "named_to_source G (?n # ns) (gi_to_book G (?n # ns) k A) = gi_expand G k A"
    by (rule Exists.IH[OF gi_chart_extension[OF rich Exists.prems(1)]
      gi_binder_chart_distinct[OF rich Exists.prems(2)]])
  show ?case by (simp only: gi_to_book.simps gi_expand.simps Let_def book_exists_def
    named_to_source.simps named_chart_fresh_type[OF rich] body
    gi_closed_code_stack[OF book_exists_const_closed, where ns=ns])
qed

lemma gi_chart_is_named_chart:
  assumes distinct: "distinct ns" and chart: "map G ns = \<Gamma>"
  shows "named_chart G \<Gamma> ns"
  using distinct unfolding chart[symmetric] named_chart_def
  by (induction ns) auto

lemma gi_chart_nth_index:
  assumes distinct: "distinct ns" and member: "n \<in> set ns"
  shows "ns ! named_index ns n = n"
proof -
  obtain i where bound: "i < length ns" and at_i: "ns ! i = n"
    using member by (auto simp: in_set_conv_nth)
  have index: "named_index ns n = i"
    using named_index_nth_distinct[OF distinct bound] by (simp only: at_i)
  show ?thesis by (simp only: index at_i)
qed

theorem gi_to_book_empty_encoding:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "named_to_source G [] (gi_to_book G ns k A) = srename (\<lambda>i. ns ! i) (gi_expand G k A)"
proof -
  let ?N = "gi_to_book G ns k A"
  let ?E = "named_to_source G [] ?N"
  have roundtrip: "named_to_source G ns ?N = gi_expand G k A"
    by (rule gi_to_book_relative_encoding[OF rich typed chart distinct])
  have stacked: "srename (named_index ns) ?E = gi_expand G k A"
    using named_to_source_stack_from_empty[where G=G and ns=ns and A="?N"] roundtrip by simp
  have support: "named_fv ?N \<subseteq> set ns" by (rule gi_to_book_fv_subset[OF rich typed chart])
  have nc: "named_chart G \<Gamma> ns" by (rule gi_chart_is_named_chart[OF distinct chart])
  have restored: "srename ((\<lambda>i. ns ! i) \<circ> named_index ns) ?E = srename id ?E"
  proof (rule srename_fv_agreement)
    fix n
    assume free: "n \<in> sfv ?E"
    have member: "n \<in> set ns" using support free by (simp add: named_to_source_empty_fv; blast)
    show "((\<lambda>i. ns ! i) \<circ> named_index ns) n = id n"
      by (simp add: gi_chart_nth_index[OF distinct member])
  qed
  have "srename (\<lambda>i. ns ! i) (srename (named_index ns) ?E) = ?E"
    using restored by (simp add: srename_comp srename_identity)
  then show ?thesis using stacked by simp
qed

text \<open>
  The two encoding equations connect the new expansion to the existing
  named translator, rather than introducing an unrelated replacement.
  Distinctness of the chart is essential for recovery of de Bruijn slots.
  No injectivity of the nonlogical-name map is required by these equations.
\<close>

end
