theory Bacon_Source_Reverse_Quantifier_Rules
  imports Bacon_Source_Fresh_Embedding Bacon_Source_Reverse_Binding
    Bacon_Source_Reverse_Identity_Axioms
begin

section \<open>Reverse Gen and Inst choose a fresh variable in the source stock\<close>

text \<open>
  To translate a target Gen or Inst step, choose a source vₙ:σ outside
  the finite image of Γ.  Extend its representation r by sending the new
  slot to n.  The supplied induction hypothesis gives the represented
  rule premise in the fixed stock G.  The actual source Gen/Inst rule then
  closes n; freshness and the closing equation recover the translation of
  the target conclusion.  Source: Bacon–Dorr §1.1 and Figure 2, pp.5–8.

  Isabelle representation.  The meta-level IH below concerns only the
  immediate rule premise, under every type-respecting representation of
  σ # Γ.  It is not an assumption of general proof reflection.  The rich
  stock supplies n, with no injectivity assumption on the old map.  Every
  whole-formula source language guard is obtained from target P/Q language
  guards and paper_back_embedding_language, not postulated separately.
  Literal paper_imp and first-class quantifier applications are retained.
\<close>

lemma paper_back_Gen_conclusion_language:
  assumes P: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    and Q: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PImp P (PForall \<sigma> Q)) Prop"
proof -
  have pt: "has_ptype \<Gamma> P Prop" and ps: "pterm_in_signature \<Sigma> P"
    using P unfolding pterm_in_language_def by blast+
  have qt: "has_ptype (\<sigma> # \<Gamma>) Q Prop" and qs: "pterm_in_signature \<Sigma> Q"
    using Q unfolding pterm_in_language_def by blast+
  have typed: "has_ptype \<Gamma> (PImp P (PForall \<sigma> Q)) Prop"
    by (rule has_ptype.PImp[OF pt has_ptype.PForall[OF qt]])
  have sig: "pterm_in_signature \<Sigma> (PImp P (PForall \<sigma> Q))" using ps qs by simp
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed sig])
qed

lemma paper_back_Inst_conclusion_language:
  assumes P: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    and Q: "pterm_in_language \<Sigma> \<Gamma> Q Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PImp (PExists \<sigma> P) Q) Prop"
proof -
  have pt: "has_ptype (\<sigma> # \<Gamma>) P Prop" and ps: "pterm_in_signature \<Sigma> P"
    using P unfolding pterm_in_language_def by blast+
  have qt: "has_ptype \<Gamma> Q Prop" and qs: "pterm_in_signature \<Sigma> Q"
    using Q unfolding pterm_in_language_def by blast+
  have typed: "has_ptype \<Gamma> (PImp (PExists \<sigma> P) Q) Prop"
    by (rule has_ptype.PImp[OF has_ptype.PExists[OF pt] qt])
  have sig: "pterm_in_signature \<Sigma> (PImp (PExists \<sigma> P) Q)" using ps qs by simp
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed sig])
qed

theorem paper_back_Gen_translation:
  assumes rich: "sg_rich G"
    and P: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    and Q: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
    and map: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> G (r k) = \<rho>"
    and IH: "\<And>s. (\<And>k \<rho>. lookup (\<sigma> # \<Gamma>) k = Some \<rho> \<Longrightarrow> G (s k) = \<rho>) \<Longrightarrow>
      paper_global_H \<Sigma> G (srename s (pterm_to_paper (PImp (pshift P) Q)))"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PImp P (PForall \<sigma> Q))))"
proof -
  obtain n where selected: "G n = \<sigma>" and fresh_image: "n \<notin> r ` {..<length \<Gamma>}"
    by (rule source_embedding_fresh_variable[where \<Gamma>=\<Gamma> and r=r and \<sigma>=\<sigma>, OF rich])
  let ?s = "source_extend_map n r"
  let ?P = "srename r (pterm_to_paper P)"
  let ?Q = "srename ?s (pterm_to_paper Q)"
  have extended_map: "G (?s k) = \<rho>" if "lookup (\<sigma> # \<Gamma>) k = Some \<rho>" for k \<rho>
    by (rule source_extend_map_type[OF selected map that])
  have premise_raw: "paper_global_H \<Sigma> G (srename ?s (pterm_to_paper (PImp (pshift P) Q)))"
    by (rule IH[where s="?s", OF extended_map])
  have premise: "paper_global_H \<Sigma> G (paper_imp ?P ?Q)"
    using premise_raw by (simp only: pterm_to_paper.simps pterm_to_paper_shift srename_paper_imp source_extend_sshift)
  have pt: "has_ptype \<Gamma> P Prop" using P unfolding pterm_in_language_def by (rule conjunct1)
  have qt: "has_ptype (\<sigma> # \<Gamma>) Q Prop" using Q unfolding pterm_in_language_def by (rule conjunct1)
  have backP: "has_stype paper_logical_type \<Gamma> (pterm_to_paper P) Prop" by (rule pterm_to_paper_type[OF pt])
  have backQ: "has_stype paper_logical_type (\<sigma> # \<Gamma>) (pterm_to_paper Q) Prop" by (rule pterm_to_paper_type[OF qt])
  have fresh: "n \<notin> sfv ?P" by (rule source_embedding_fresh_term[OF backP fresh_image])
  have close: "sclose n ?Q = srename (lift_ren r) (pterm_to_paper Q)"
    by (rule source_fresh_close_embedding[OF backQ fresh_image])
  let ?result = "paper_imp ?P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n ?Q)))"
  have result_eq: "?result = srename r (pterm_to_paper (PImp P (PForall \<sigma> Q)))"
    by (simp only: pterm_to_paper.simps srename_paper_imp srename.simps close)
  have target_language: "pterm_in_language \<Sigma> \<Gamma> (PImp P (PForall \<sigma> Q)) Prop"
    by (rule paper_back_Gen_conclusion_language[OF P Q])
  have mapped_language: "sgterm_in_language paper_logical_type \<Sigma> G
    (srename r (pterm_to_paper (PImp P (PForall \<sigma> Q)))) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF target_language map])
  have source_guard: "sgterm_in_language paper_logical_type \<Sigma> G ?result Prop"
    using mapped_language by (simp only: result_eq)
  have derived: "paper_global_H \<Sigma> G ?result"
    by (rule paper_global_H.Gen[where P="?P" and Q="?Q" and n=n and \<sigma>=\<sigma>,
      OF premise selected fresh source_guard])
  show ?thesis using derived by (simp only: result_eq)
qed

theorem paper_back_Inst_translation:
  assumes rich: "sg_rich G"
    and P: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    and Q: "pterm_in_language \<Sigma> \<Gamma> Q Prop"
    and map: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> G (r k) = \<rho>"
    and IH: "\<And>s. (\<And>k \<rho>. lookup (\<sigma> # \<Gamma>) k = Some \<rho> \<Longrightarrow> G (s k) = \<rho>) \<Longrightarrow>
      paper_global_H \<Sigma> G (srename s (pterm_to_paper (PImp P (pshift Q))))"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PImp (PExists \<sigma> P) Q)))"
proof -
  obtain n where selected: "G n = \<sigma>" and fresh_image: "n \<notin> r ` {..<length \<Gamma>}"
    by (rule source_embedding_fresh_variable[where \<Gamma>=\<Gamma> and r=r and \<sigma>=\<sigma>, OF rich])
  let ?s = "source_extend_map n r"
  let ?P = "srename ?s (pterm_to_paper P)"
  let ?Q = "srename r (pterm_to_paper Q)"
  have extended_map: "G (?s k) = \<rho>" if "lookup (\<sigma> # \<Gamma>) k = Some \<rho>" for k \<rho>
    by (rule source_extend_map_type[OF selected map that])
  have premise_raw: "paper_global_H \<Sigma> G (srename ?s (pterm_to_paper (PImp P (pshift Q))))"
    by (rule IH[where s="?s", OF extended_map])
  have premise: "paper_global_H \<Sigma> G (paper_imp ?P ?Q)"
    using premise_raw by (simp only: pterm_to_paper.simps pterm_to_paper_shift srename_paper_imp source_extend_sshift)
  have pt: "has_ptype (\<sigma> # \<Gamma>) P Prop" using P unfolding pterm_in_language_def by (rule conjunct1)
  have qt: "has_ptype \<Gamma> Q Prop" using Q unfolding pterm_in_language_def by (rule conjunct1)
  have backP: "has_stype paper_logical_type (\<sigma> # \<Gamma>) (pterm_to_paper P) Prop" by (rule pterm_to_paper_type[OF pt])
  have backQ: "has_stype paper_logical_type \<Gamma> (pterm_to_paper Q) Prop" by (rule pterm_to_paper_type[OF qt])
  have fresh: "n \<notin> sfv ?Q" by (rule source_embedding_fresh_term[OF backQ fresh_image])
  have close: "sclose n ?P = srename (lift_ren r) (pterm_to_paper P)"
    by (rule source_fresh_close_embedding[OF backP fresh_image])
  let ?result = "paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n ?P))) ?Q"
  have result_eq: "?result = srename r (pterm_to_paper (PImp (PExists \<sigma> P) Q))"
    by (simp only: pterm_to_paper.simps srename_paper_imp srename.simps close)
  have target_language: "pterm_in_language \<Sigma> \<Gamma> (PImp (PExists \<sigma> P) Q) Prop"
    by (rule paper_back_Inst_conclusion_language[OF P Q])
  have mapped_language: "sgterm_in_language paper_logical_type \<Sigma> G
    (srename r (pterm_to_paper (PImp (PExists \<sigma> P) Q))) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF target_language map])
  have source_guard: "sgterm_in_language paper_logical_type \<Sigma> G ?result Prop"
    using mapped_language by (simp only: result_eq)
  have derived: "paper_global_H \<Sigma> G ?result"
    by (rule paper_global_H.Inst[where P="?P" and Q="?Q" and n=n and \<sigma>=\<sigma>,
      OF premise selected fresh source_guard])
  show ?thesis using derived by (simp only: result_eq)
qed

end
