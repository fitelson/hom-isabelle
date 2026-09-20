theory Goodman_Translated_Extension_Rules
  imports Goodman_Axiom_Extension_Quantifiers
begin

section \<open>The old changing-context rules above the fixed axiom stock\<close>

text \<open>
  These are the Gen and Inst rule obligations for the prospective CEV+
  proof induction. Premises are derivable in C+[T], not necessarily in H.
  The bound-name alignment is reused, while Inst uses the extension-level
  result rather than applying H soundness to an added-axiom theorem.
\<close>

theorem gi_goodman_translated_Gen:
  assumes rich: "sg_rich G" and p: "\<Gamma> \<turnstile> P : Prop" and q: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and pc: "gi_constants_admitted k \<Sigma> P" and qc: "gi_constants_admitted k \<Sigma> Q"
    and premise: "goodman_book_proves \<Sigma> G T
      (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k (Imp (shift P) Q))"
  shows "goodman_book_proves \<Sigma> G T (gi_to_book G ns k (Imp P (Forall \<sigma> Q)))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?P = "gi_to_book G ns k P"
  let ?Q = "gi_to_book G (?n # ns) k Q"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have shift_alpha: "named_alpha G (gi_to_book G (?n # ns) k (shift P)) ?P"
    by (rule gi_to_book_shift_alpha[OF rich p chart distinct fresh nt])
  have aligned: "goodman_book_proves \<Sigma> G T (book_imp ?P ?Q)"
    by (rule gi_goodman_alpha_transport[OF rich gi_alpha_imp_left[OF shift_alpha]];
      use premise in \<open>simp only: gi_to_book.simps\<close>)
  have pl: "book_theory_formula \<Sigma> G ?P" by (rule gi_to_book_language[OF rich p chart pc])
  have ql: "book_theory_formula \<Sigma> G ?Q"
    by (rule gi_to_book_language[OF rich q gi_chart_extension[OF rich chart] qc])
  have absent: "?n \<notin> named_fv ?P" using fresh gi_to_book_fv_subset[OF rich p chart] by blast
  have result: "goodman_book_proves \<Sigma> G T (book_imp ?P (book_all G ?n ?Q))"
    by (rule goodman_book_proves.Gen[OF aligned pl ql absent])
  show ?thesis using result by (simp only: gi_to_book.simps Let_def)
qed

theorem gi_goodman_translated_Inst:
  assumes rich: "sg_rich G" and p: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and q: "\<Gamma> \<turnstile> Q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and pc: "gi_constants_admitted k \<Sigma> P" and qc: "gi_constants_admitted k \<Sigma> Q"
    and premise: "goodman_book_proves \<Sigma> G T
      (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k (Imp P (shift Q)))"
  shows "goodman_book_proves \<Sigma> G T (gi_to_book G ns k (Imp (Exists \<sigma> P) Q))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?P = "gi_to_book G (?n # ns) k P"
  let ?Q = "gi_to_book G ns k Q"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have shift_alpha: "named_alpha G (gi_to_book G (?n # ns) k (shift Q)) ?Q"
    by (rule gi_to_book_shift_alpha[OF rich q chart distinct fresh nt])
  have aligned: "goodman_book_proves \<Sigma> G T (book_imp ?P ?Q)"
    by (rule gi_goodman_alpha_transport[OF rich gi_alpha_imp_right[OF shift_alpha]];
      use premise in \<open>simp only: gi_to_book.simps\<close>)
  have pl: "book_theory_formula \<Sigma> G ?P"
    by (rule gi_to_book_language[OF rich p gi_chart_extension[OF rich chart] pc])
  have ql: "book_theory_formula \<Sigma> G ?Q" by (rule gi_to_book_language[OF rich q chart qc])
  have absent: "?n \<notin> named_fv ?Q" using fresh gi_to_book_fv_subset[OF rich q chart] by blast
  have result: "goodman_book_proves \<Sigma> G T (book_imp (book_exists G ?n ?P) ?Q)"
    by (rule gi_goodman_Inst[OF rich pl ql absent aligned])
  show ?thesis using result by (simp only: gi_to_book.simps Let_def)
qed


end
