theory Bacon_Source_Named_H_Reverse_Rules
  imports Bacon_Source_Named_H_Alpha Bacon_Source_Named_Representation_Reflection
    Bacon_Source_Named_H_Forward Bacon_Source_Global_Connective_Language
begin

section \<open>Reconstructing named MP, Gen and Inst\<close>

text \<open>
  Given named theorem representatives of the source premises, reconstruct
  the three inference rules of Bacon–Dorr Figure 2, p.8. Equal encodings
  align named representatives by the derived α theorem, not by treating
  different raw named terms as literally equal. Gen and Inst keep G fixed
  and transfer their exact free-variable provisos.

  No source-H theorem or model is used as a proof rule here. Source
  language guards are syntax premises; the induction supplying the named
  theorem representatives belongs to the subsequent assembly theorem.
\<close>

lemma paper_named_imp_preimage_operands:
  assumes premise: "\<exists>I. paper_named_H \<Sigma> G I \<and> named_to_source G [] I = paper_imp P Q"
    and rich: "sg_rich G"
  obtains A B where "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    and "named_in_language paper_logical_type \<Sigma> G A Prop"
    and "named_in_language paper_logical_type \<Sigma> G B Prop"
    and "named_to_source G [] A = P" and "named_to_source G [] B = Q"
proof -
  obtain I where ih: "paper_named_H \<Sigma> G I" and ie: "named_to_source G [] I = paper_imp P Q"
    using premise by (elim exE conjE)
  have il: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp P Q) Prop"
    using paper_named_H_encoding_language[OF paper_named_H_language[OF ih]] by (simp only: ie)
  have operands: "sgterm_in_language paper_logical_type \<Sigma> G P Prop \<and>
    sgterm_in_language paper_logical_type \<Sigma> G Q Prop"
    by (rule iffD1[OF paper_global_imp_language_iff il])
  obtain A where al: "named_in_language paper_logical_type \<Sigma> G A Prop" and ae: "named_to_source G [] A = P"
    using source_named_representation_exists[OF conjunct1[OF operands] rich] by (elim exE conjE)
  obtain B where bl: "named_in_language paper_logical_type \<Sigma> G B Prop" and be: "named_to_source G [] B = Q"
    using source_named_representation_exists[OF conjunct2[OF operands] rich] by (elim exE conjE)
  have same: "named_to_source G [] I = named_to_source G [] (named_paper_imp G A B)"
    by (simp only: ie named_paper_imp_encoding[OF rich] ae be)
  have native: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    by (rule paper_named_H_same_encoding[OF ih same rich])
  show thesis by (rule that[OF native al bl ae be])
qed

theorem paper_named_MP_preimage:
  assumes left: "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = P"
    and right: "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = paper_imp P Q"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = Q"
proof -
  obtain I where ih: "paper_named_H \<Sigma> G I" and ie: "named_to_source G [] I = P"
    using left by (elim exE conjE)
  obtain A B where implication: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    and al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and ae: "named_to_source G [] A = P" and be: "named_to_source G [] B = Q"
    using paper_named_imp_preimage_operands[OF right rich] by blast
  have same: "named_to_source G [] I = named_to_source G [] A" by (simp only: ie ae)
  have ah: "paper_named_H \<Sigma> G A" by (rule paper_named_H_same_encoding[OF ih same rich])
  have bh: "paper_named_H \<Sigma> G B" by (rule paper_named_H.MP[OF ah implication bl])
  show ?thesis by (rule exI[where x=B], rule conjI[OF bh be])
qed

theorem paper_named_Gen_preimage:
  assumes premise: "\<exists>I. paper_named_H \<Sigma> G I \<and> named_to_source G [] I = paper_imp P Q"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> sfv P"
    and whole: "sgterm_in_language paper_logical_type \<Sigma> G
      (paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))"
proof -
  obtain A B where implication: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    and al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and ae: "named_to_source G [] A = P" and be: "named_to_source G [] B = Q"
    using paper_named_imp_preimage_operands[OF premise rich] by blast
  let ?N = "named_paper_imp G A (named_paper_all \<sigma> (NLam n B))"
  have encoded: "named_to_source G [] ?N = paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))"
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_all_encoding
      named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF nt] ae be)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoded; rule whole)
  have language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have fv: "named_fv A = sfv P"
    using arg_cong[where f=sfv, OF ae] by (simp only: named_to_source_empty_fv)
  have named_fresh: "n \<notin> named_fv A" by (simp only: fv; rule fresh)
  have native: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.Gen[OF implication nt named_fresh language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF native encoded])
qed

theorem paper_named_Inst_preimage:
  assumes premise: "\<exists>I. paper_named_H \<Sigma> G I \<and> named_to_source G [] I = paper_imp P Q"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> sfv Q"
    and whole: "sgterm_in_language paper_logical_type \<Sigma> G
      (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q"
proof -
  obtain A B where implication: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    and al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and ae: "named_to_source G [] A = P" and be: "named_to_source G [] B = Q"
    using paper_named_imp_preimage_operands[OF premise rich] by blast
  let ?N = "named_paper_imp G (named_paper_ex \<sigma> (NLam n A)) B"
  have encoded: "named_to_source G [] ?N = paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q"
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_ex_encoding
      named_H_Lam_encoding[where G=G and n=n and \<sigma>=\<sigma>, OF nt] ae be)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoded; rule whole)
  have language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have fv: "named_fv B = sfv Q"
    using arg_cong[where f=sfv, OF be] by (simp only: named_to_source_empty_fv)
  have named_fresh: "n \<notin> named_fv B" by (simp only: fv; rule fresh)
  have native: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.Inst[OF implication nt named_fresh language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF native encoded])
qed

end
