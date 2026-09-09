theory Bacon_Source_Relational_Local_Inst
  imports Bacon_Source_Relational_Local_Exchange
begin

section \<open>The existential binder used by the native Inst rule\<close>

lemma paper_R_local_exists_binder_language:
  assumes body: "paper_R_in_language \<Sigma> G P Prop" and nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam n P)) Prop"
proof -
  have bt: "paper_R_has_type G P Prop" and names: "named_in_signature \<Sigma> P"
    using body unfolding paper_R_in_language_def by blast+
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have lam: "paper_R_has_type G (NLam n P) (Arr (G n) Prop)"
    by (rule paper_R_has_type.Lam[OF bt nr]; simp)
  have predicate: "paper_R_has_type G (NLam n P) (Arr \<sigma> Prop)" using lam by (simp only: nt)
  have qr: "paper_R_type (paper_logical_type (SEx \<sigma>))" using rt by simp
  have quantifier: "paper_R_has_type G (NLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SEx \<sigma>", OF qr] by simp
  have typed: "paper_R_has_type G (named_paper_ex \<sigma> (NLam n P)) Prop"
    unfolding named_paper_ex_def by (rule paper_R_has_type.App[OF quantifier predicate])
  show ?thesis using typed names by (simp add: paper_R_in_language_def named_paper_ex_def)
qed

section \<open>Admissibility for finitely many n-fresh premises\<close>

text \<open>
  To move Inst past an assumption C, discharge C, exchange antecedents,
  apply the induction hypothesis to P→(C→Q), exchange back, and use MP
  with C. Freshness of C and Q makes the new consequent n-fresh.
  Only the empty-premise case invokes the native theorem-level Inst.
  This is admissibility, not a new constructor of local consequence.
\<close>

lemma paper_R_named_derivable_Inst_finite:
  assumes finite: "finite S" and rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh_Q: "n \<notin> named_fv Q"
    and source_premises: "\<And>C. C \<in> S \<Longrightarrow> paper_R_in_language \<Sigma> G C Prop \<and> n \<notin> named_fv C"
    and derivation: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G P Q)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
  using finite pl ql fresh_Q source_premises derivation
proof (induction arbitrary: P Q rule: finite_induct)
  case empty
  have premise: "paper_R_named_H \<Sigma> G (named_paper_imp G P Q)"
    by (rule iffD1[OF paper_R_named_derivable_empty_iff empty.prems(5)])
  have existential: "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam n P)) Prop"
    by (rule paper_R_local_exists_binder_language[OF empty.prems(1) nt rt])
  have language: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich existential empty.prems(2)])
  show ?case by (rule paper_R_named_derivable.Theorem[
    OF paper_R_named_H.Inst[OF premise nt empty.prems(3) language]])
next
  case (insert C S)
  have cp: "paper_R_in_language \<Sigma> G C Prop \<and> n \<notin> named_fv C" by (rule insert.prems(4)[OF insertI1])
  have cl: "paper_R_in_language \<Sigma> G C Prop" by (rule conjunct1[OF cp])
  have cf: "n \<notin> named_fv C" by (rule conjunct2[OF cp])
  have tail: "paper_R_in_language \<Sigma> G B Prop \<and> n \<notin> named_fv B" if "B \<in> S" for B
    by (rule insert.prems(4); rule insertI2; rule that)
  have discharged: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G C (named_paper_imp G P Q))"
    by (rule paper_R_named_derivable_deduction[OF rich cl insert.prems(5)])
  have exchanged: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G P (named_paper_imp G C Q))"
    by (rule paper_R_named_derivable_imp_exchange[OF rich cl insert.prems(1,2) discharged])
  have inner_language: "paper_R_in_language \<Sigma> G (named_paper_imp G C Q) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich cl insert.prems(2)])
  have inner_fresh: "n \<notin> named_fv (named_paper_imp G C Q)"
    using cf insert.prems(3) by (simp only: named_paper_defined_fv; blast)
  let ?E = "named_paper_ex \<sigma> (NLam n P)"
  have instantiated: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G ?E (named_paper_imp G C Q))"
    by (rule insert.IH[OF insert.prems(1) inner_language inner_fresh tail exchanged])
  have el: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_local_exists_binder_language[OF insert.prems(1) nt rt])
  have restored: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G C (named_paper_imp G ?E Q))"
    by (rule paper_R_named_derivable_imp_exchange[OF rich el cl insert.prems(2) instantiated])
  have moved: "paper_R_named_derivable \<Sigma> G (insert C S) (named_paper_imp G C (named_paper_imp G ?E Q))"
    by (rule paper_R_named_derivable_mono[OF restored subset_insertI])
  have assumption_C: "paper_R_named_derivable \<Sigma> G (insert C S) C"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 cl])
  have result_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?E Q) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich el insert.prems(2)])
  show ?case by (rule paper_R_named_derivable.MP[OF assumption_C moved result_language])
qed

section \<open>Finite proof support removes the finiteness restriction\<close>

theorem paper_R_named_derivable_Inst:
  assumes rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh_Q: "n \<notin> named_fv Q"
    and source_premises: "\<And>C. C \<in> S \<Longrightarrow> paper_R_in_language \<Sigma> G C Prop \<and> n \<notin> named_fv C"
    and derivation: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G P Q)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
proof -
  obtain U where finite: "finite U" and subset: "U \<subseteq> S"
    and supported: "paper_R_named_derivable \<Sigma> G U (named_paper_imp G P Q)"
    using paper_R_named_derivable_finite_support[OF derivation] by blast
  have local_premises: "paper_R_in_language \<Sigma> G C Prop \<and> n \<notin> named_fv C" if "C \<in> U" for C
    by (rule source_premises[OF subsetD[OF subset that]])
  have result: "paper_R_named_derivable \<Sigma> G U (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
    by (rule paper_R_named_derivable_Inst_finite[OF finite rich pl ql nt rt fresh_Q local_premises supported])
  show ?thesis by (rule paper_R_named_derivable_mono[OF result subset])
qed

end
