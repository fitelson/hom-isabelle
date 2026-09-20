theory Goodman_H_Quantifier_Rules
  imports Goodman_H_Quantifier_Certificates
begin

section \<open>Existential generalization in the translated constructor language\<close>

theorem gi_H_EG:
  assumes rich: "sg_rich G" and body: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
    and argument: "\<Gamma> \<turnstile> N : \<sigma>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and mc: "gi_constants_admitted k \<Sigma> M" and nc: "gi_constants_admitted k \<Sigma> N"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp (subst0 N M) (Exists \<sigma> M)))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?M = "gi_to_book G (?n # ns) k M"
  let ?N = "gi_to_book G ns k N"
  let ?F = "NLam ?n ?M"
  let ?R = "gi_to_book G ns k (App (Lam \<sigma> M) N)"
  let ?Y = "gi_to_book G ns k (subst0 N M)"
  let ?E = "gi_to_book G ns k (Exists \<sigma> M)"
  have ml: "book_theory_formula \<Sigma> G ?M"
    by (rule gi_to_book_language[OF rich body gi_chart_extension[OF rich chart] mc])
  have nl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?N \<sigma>"
    by (rule gi_to_book_language[OF rich argument chart nc])
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?F (Arr \<sigma> Prop)"
    using book_language_Lam[OF ml, where n="?n"] by (simp only: named_chart_fresh_type[OF rich])
  have el: "book_theory_formula \<Sigma> G ?E"
    by (simp only: gi_to_book.simps Let_def; rule book_exists_language[OF rich ml])
  have conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop ?R ?Y"
    by (rule gi_to_book_beta_root[OF rich body argument chart distinct mc nc])
  have rl: "book_theory_formula \<Sigma> G ?R" and yl: "book_theory_formula \<Sigma> G ?Y"
    using named_beta_eta_languages[OF conversion] by (auto simp only: book_language_UNIV)
  have backward: "book_H \<Sigma> G (book_imp ?Y ?R)"
    using gi_H_conversion_pair[OF rich conversion] by blast
  have introduction: "book_H \<Sigma> G (book_imp ?R ?E)"
    using gi_book_H_EG[OF rich fl nl]
    by (simp only: gi_to_book.simps Let_def book_exists_def named_chart_fresh_type[OF rich])
  have result: "book_H \<Sigma> G (book_imp ?Y ?E)"
    by (rule gi_H_imp_trans[OF rich yl rl el backward introduction])
  show ?thesis using result by (simp only: gi_to_book.simps)
qed

section \<open>The changing-context Gen and Inst rules\<close>

theorem gi_H_Gen:
  assumes rich: "sg_rich G" and p: "\<Gamma> \<turnstile> P : Prop" and q: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and pc: "gi_constants_admitted k \<Sigma> P" and qc: "gi_constants_admitted k \<Sigma> Q"
    and premise: "book_H \<Sigma> G
      (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k (Imp (shift P) Q))"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp P (Forall \<sigma> Q)))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?P = "gi_to_book G ns k P"
  let ?Q = "gi_to_book G (?n # ns) k Q"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have shift_alpha: "named_alpha G (gi_to_book G (?n # ns) k (shift P)) ?P"
    by (rule gi_to_book_shift_alpha[OF rich p chart distinct fresh nt])
  have aligned: "book_H \<Sigma> G (book_imp ?P ?Q)"
    by (rule gi_H_alpha_transport[OF rich gi_alpha_imp_left[OF shift_alpha]];
      use premise in \<open>simp only: gi_to_book.simps\<close>)
  have pl: "book_theory_formula \<Sigma> G ?P" by (rule gi_to_book_language[OF rich p chart pc])
  have ql: "book_theory_formula \<Sigma> G ?Q"
    by (rule gi_to_book_language[OF rich q gi_chart_extension[OF rich chart] qc])
  have absent: "?n \<notin> named_fv ?P" using fresh gi_to_book_fv_subset[OF rich p chart] by blast
  have implication: "book_theory_derivable \<Sigma> G {} (book_imp ?P ?Q)"
    using aligned by (simp only: book_H_iff_theory[OF rich])
  have result: "book_theory_derivable \<Sigma> G {} (book_imp ?P (book_all G ?n ?Q))"
    by (rule book_theory_derivable.Gen[OF implication pl ql absent])
  show ?thesis using result by (simp only: gi_to_book.simps Let_def book_H_iff_theory[OF rich])
qed

theorem gi_H_Inst:
  assumes rich: "sg_rich G" and p: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and q: "\<Gamma> \<turnstile> Q : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and pc: "gi_constants_admitted k \<Sigma> P" and qc: "gi_constants_admitted k \<Sigma> Q"
    and premise: "book_H \<Sigma> G
      (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k (Imp P (shift Q)))"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp (Exists \<sigma> P) Q))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?P = "gi_to_book G (?n # ns) k P"
  let ?Q = "gi_to_book G ns k Q"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have shift_alpha: "named_alpha G (gi_to_book G (?n # ns) k (shift Q)) ?Q"
    by (rule gi_to_book_shift_alpha[OF rich q chart distinct fresh nt])
  have aligned: "book_H \<Sigma> G (book_imp ?P ?Q)"
    by (rule gi_H_alpha_transport[OF rich gi_alpha_imp_right[OF shift_alpha]];
      use premise in \<open>simp only: gi_to_book.simps\<close>)
  have pl: "book_theory_formula \<Sigma> G ?P"
    by (rule gi_to_book_language[OF rich p gi_chart_extension[OF rich chart] pc])
  have ql: "book_theory_formula \<Sigma> G ?Q" by (rule gi_to_book_language[OF rich q chart qc])
  have absent: "?n \<notin> named_fv ?Q" using fresh gi_to_book_fv_subset[OF rich q chart] by blast
  have result: "book_H \<Sigma> G (book_imp (book_exists G ?n ?P) ?Q)"
    by (rule gi_book_H_Inst[OF rich pl ql absent aligned])
  show ?thesis using result by (simp only: gi_to_book.simps Let_def)
qed

end
