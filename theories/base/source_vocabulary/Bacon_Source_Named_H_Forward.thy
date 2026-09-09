theory Bacon_Source_Named_H_Forward
  imports Bacon_Source_Named_H Bacon_Source_Named_Alpha_Representation
begin

section \<open>Every native named-H proof encodes to a source-global H proof\<close>

text \<open>
  If ⊢H A in the independently defined named calculus, then its
  empty-stack encoding is a theorem of the source-global calculus.
  Source: the ten clauses of Bacon–Dorr Figure 2, p.8, and the
  binding-context convention on p.7.

  Representation: induction follows exactly PC, UI, EG, Ref, LL, β,
  η, MP, Gen and Inst. Literal →/↔ encoding requires rich G.
  Named λn.Q encodes by closing the existing free slot n; the stock
  remains G. Contextual β/η steps use their existing encoding theorems.
  Status: one-way syntactic proof preservation only. No semantic premise,
  injectivity assumption, α constructor, or extra H rule is introduced.
\<close>

lemma paper_named_H_encoding_language:
  assumes language: "named_in_language paper_logical_type \<Sigma> G A \<tau>"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) \<tau>"
  using named_to_source_global_language[where ns="[]", OF language]
  by (simp only: named_stack_stock.simps)

lemma named_H_Lam_encoding:
  assumes n_type: "G n = \<sigma>"
  shows "named_to_source G [] (NLam n A) = SLam \<sigma> (sclose n (named_to_source G [] A))"
  by (simp only: named_to_source.simps named_to_source_close n_type)

theorem paper_named_H_encoding:
  assumes derivation: "paper_named_H \<Sigma> G A" and rich: "sg_rich G"
  shows "paper_global_H \<Sigma> G (named_to_source G [] A)"
  using derivation
proof (induction rule: paper_named_H.induct)
  case (PC A)
  show ?case by (rule paper_global_H.PC[OF named_PC_encoding[OF rich PC.hyps]])
next
  case (UI \<sigma> F A)
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SLogical (SAll \<sigma>)) (named_to_source G [] F))
      (SApp (named_to_source G [] F) (named_to_source G [] A))) Prop"
    using paper_named_H_encoding_language[OF UI.hyps]
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_all_encoding named_to_source.simps)
  show ?case
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_all_encoding named_to_source.simps;
      rule paper_global_H.UI[OF guard])
next
  case (EG F A \<sigma>)
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (named_to_source G [] F) (named_to_source G [] A))
      (SApp (SLogical (SEx \<sigma>)) (named_to_source G [] F))) Prop"
    using paper_named_H_encoding_language[OF EG.hyps]
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_ex_encoding named_to_source.simps)
  show ?case
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_ex_encoding named_to_source.simps;
      rule paper_global_H.EG[OF guard])
next
  case (Ref \<sigma> A)
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (SApp (SApp (SLogical (SEq \<sigma>)) (named_to_source G [] A)) (named_to_source G [] A)) Prop"
    using paper_named_H_encoding_language[OF Ref.hyps] by (simp only: named_paper_eq_encoding)
  show ?case by (simp only: named_paper_eq_encoding; rule paper_global_H.Ref[OF guard])
next
  case (LL \<sigma> A B F)
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) (named_to_source G [] A)) (named_to_source G [] B))
      (paper_imp (SApp (named_to_source G [] F) (named_to_source G [] A))
        (SApp (named_to_source G [] F) (named_to_source G [] B)))) Prop"
    using paper_named_H_encoding_language[OF LL.hyps]
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_eq_encoding named_to_source.simps)
  show ?case
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_eq_encoding named_to_source.simps;
      rule paper_global_H.LL[OF guard])
next
  case (Beta A B)
  have left: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) Prop"
    by (rule paper_named_H_encoding_language[OF Beta.hyps(1)])
  have right: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] B) Prop"
    by (rule paper_named_H_encoding_language[OF Beta.hyps(2)])
  have step: "scompatible_step sbeta_contract (named_to_source G [] A) (named_to_source G [] B)"
    by (rule named_beta_step_encoding[OF Beta.hyps(3)])
  have whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_iff (named_to_source G [] A) (named_to_source G [] B)) Prop"
    using paper_named_H_encoding_language[OF Beta.hyps(4)]
    by (simp only: named_paper_iff_encoding[OF rich])
  show ?case by (simp only: named_paper_iff_encoding[OF rich];
    rule paper_global_H.Beta[OF left right step whole])
next
  case (Eta A B)
  have left: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) Prop"
    by (rule paper_named_H_encoding_language[OF Eta.hyps(1)])
  have right: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] B) Prop"
    by (rule paper_named_H_encoding_language[OF Eta.hyps(2)])
  have step: "scompatible_step seta_contract (named_to_source G [] A) (named_to_source G [] B)"
    by (rule named_eta_step_encoding[OF Eta.hyps(3)])
  have whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_iff (named_to_source G [] A) (named_to_source G [] B)) Prop"
    using paper_named_H_encoding_language[OF Eta.hyps(4)]
    by (simp only: named_paper_iff_encoding[OF rich])
  show ?case by (simp only: named_paper_iff_encoding[OF rich];
    rule paper_global_H.Eta[OF left right step whole])
next
  case (MP A B)
  have implication: "paper_global_H \<Sigma> G
    (paper_imp (named_to_source G [] A) (named_to_source G [] B))"
    using MP.IH(2) by (simp only: named_paper_imp_encoding[OF rich])
  have conclusion: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] B) Prop"
    by (rule paper_named_H_encoding_language[OF MP.hyps(3)])
  show ?case by (rule paper_global_H.MP[OF MP.IH(1) implication conclusion])
next
  case (Gen P Q n \<sigma>)
  have premise: "paper_global_H \<Sigma> G
    (paper_imp (named_to_source G [] P) (named_to_source G [] Q))"
    using Gen.IH by (simp only: named_paper_imp_encoding[OF rich])
  have fresh: "n \<notin> sfv (named_to_source G [] P)"
    by (simp only: named_to_source_empty_fv; rule Gen.hyps(3))
  have whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (named_to_source G [] P)
      (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n (named_to_source G [] Q))))) Prop"
    using paper_named_H_encoding_language[OF Gen.hyps(4)]
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_all_encoding
      named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF Gen.hyps(2)])
  have result: "paper_global_H \<Sigma> G
    (paper_imp (named_to_source G [] P)
      (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n (named_to_source G [] Q)))))"
    by (rule paper_global_H.Gen[OF premise Gen.hyps(2) fresh whole])
  show ?case using result by (simp only: named_paper_imp_encoding[OF rich]
    named_paper_all_encoding named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF Gen.hyps(2)])
next
  case (Inst P Q n \<sigma>)
  have premise: "paper_global_H \<Sigma> G
    (paper_imp (named_to_source G [] P) (named_to_source G [] Q))"
    using Inst.IH by (simp only: named_paper_imp_encoding[OF rich])
  have fresh: "n \<notin> sfv (named_to_source G [] Q)"
    by (simp only: named_to_source_empty_fv; rule Inst.hyps(3))
  have whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n (named_to_source G [] P))))
      (named_to_source G [] Q)) Prop"
    using paper_named_H_encoding_language[OF Inst.hyps(4)]
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_ex_encoding
      named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF Inst.hyps(2)])
  have result: "paper_global_H \<Sigma> G
    (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n (named_to_source G [] P))))
      (named_to_source G [] Q))"
    by (rule paper_global_H.Inst[OF premise Inst.hyps(2) fresh whole])
  show ?case using result by (simp only: named_paper_imp_encoding[OF rich]
    named_paper_ex_encoding named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF Inst.hyps(2)])
qed

end
