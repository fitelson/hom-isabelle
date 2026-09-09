theory Bacon_Source_Global_Existence
  imports Bacon_Source_Global_H Bacon_Source_Global_Substitution
begin

section \<open>Existence is derived, not added to Figure 2\<close>

text \<open>
  ⊢H ∃x:σ.x =σ x, for every type σ.
  Bacon–Dorr p. 7 derives this from y =σ y (Ref),
  (λx:σ.x =σ x)y ↔ y =σ y (β), and
  (λx:σ.x =σ x)y → ∃x:σ.x =σ x (EG), using PC and MP.

  Isabelle representation: choose a global free slot n of type σ.  A
  finite prefix of G is used only to reuse typing lemmas for the displayed
  terms.  Every logical proof step remains in paper_global_H Σ G; the
  proof stock is never restricted to the conclusion's free variables.

  Status: a derivation from the existing ten constructors.  No target pH
  theorem, IndividualExistence axiom, semantic model, or source proof
  reflection is used.
\<close>

lemma source_prefix_global_language:
  assumes typed: "has_stype L (map G [0..<N]) A \<tau>"
    and names: "sterm_in_signature \<Sigma> A"
  shows "sgterm_in_language L \<Sigma> G A \<tau>"
proof -
  have global: "has_sgtype L G A \<tau>"
  proof (rule source_finite_to_global_typing[where G=G, OF typed])
    fix n \<rho>
    assume index: "lookup (map G [0..<N]) n = Some \<rho>"
    show "G n = \<rho>" using index by (auto simp: lookup_def split: if_splits)
  qed
  show ?thesis unfolding sgterm_in_language_def by (rule conjI[OF global names])
qed

lemma paper_global_existence_from_variable:
  assumes variable: "G n = \<sigma>"
  shows "paper_global_H \<Sigma> G
    (SApp (SLogical (SEx \<sigma>))
      (SLam \<sigma> (SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0))))"
proof -
  let ?\<Gamma> = "map G [0..<Suc n]"
  let ?y = "SVar n"
  let ?R = "SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0)"
  let ?F = "SLam \<sigma> ?R"
  let ?Fy = "SApp ?F ?y"
  let ?yy = "SApp (SApp (SLogical (SEq \<sigma>)) ?y) ?y"
  let ?E = "SApp (SLogical (SEx \<sigma>)) ?F"
  have yt: "has_stype paper_logical_type ?\<Gamma> ?y \<sigma>"
    by (rule has_stype.Var) (simp add: lookup_def nth_append variable)
  have rt: "has_stype paper_logical_type (\<sigma> # ?\<Gamma>) ?R Prop"
  proof (rule paper_binary_logical_type)
    show "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)" by simp
    show "has_stype paper_logical_type (\<sigma> # ?\<Gamma>) (SVar 0) \<sigma>"
      by (rule has_stype.Var[OF lookup_Cons_0])
    show "has_stype paper_logical_type (\<sigma> # ?\<Gamma>) (SVar 0) \<sigma>"
      by (rule has_stype.Var[OF lookup_Cons_0])
  qed
  have ft: "has_stype paper_logical_type ?\<Gamma> ?F (Arr \<sigma> Prop)"
    by (rule has_stype.Lam[OF rt])
  have fyt: "has_stype paper_logical_type ?\<Gamma> ?Fy Prop"
    by (rule has_stype.App[OF ft yt])
  have yyt: "has_stype paper_logical_type ?\<Gamma> ?yy Prop"
    by (rule paper_binary_logical_type[OF _ yt yt]) simp
  have et: "has_stype paper_logical_type ?\<Gamma> ?E Prop"
    by (rule paper_unary_logical_type[OF _ ft]) simp
  have fyl: "sgterm_in_language paper_logical_type \<Sigma> G ?Fy Prop"
    by (rule source_prefix_global_language[OF fyt]) simp
  have yyl: "sgterm_in_language paper_logical_type \<Sigma> G ?yy Prop"
    by (rule source_prefix_global_language[OF yyt]) simp
  have el: "sgterm_in_language paper_logical_type \<Sigma> G ?E Prop"
    by (rule source_prefix_global_language[OF et]) simp

  have ref: "paper_global_H \<Sigma> G ?yy" by (rule paper_global_H.Ref[OF yyl])
  have beta_root: "sbeta_contract ?Fy ?yy"
    using sbeta_contract.beta[where \<sigma>=\<sigma> and M="?R" and N="?y"]
    by (simp add: ssubst0_def)
  have beta_step: "scompatible_step sbeta_contract ?Fy ?yy"
    by (rule scompatible_step.root[where R=sbeta_contract and M="?Fy" and N="?yy", OF beta_root])
  have iff_t: "has_stype paper_logical_type ?\<Gamma> (paper_iff ?Fy ?yy) Prop"
    by (rule paper_iff_type[OF fyt yyt])
  have iff_l: "sgterm_in_language paper_logical_type \<Sigma> G (paper_iff ?Fy ?yy) Prop"
    by (rule source_prefix_global_language[OF iff_t]) simp
  have beta: "paper_global_H \<Sigma> G (paper_iff ?Fy ?yy)"
    by (rule paper_global_H.Beta[OF fyl yyl beta_step iff_l])
  have eg_t: "has_stype paper_logical_type ?\<Gamma> (paper_imp ?Fy ?E) Prop"
    by (rule paper_imp_type[OF fyt et])
  have eg_l: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp ?Fy ?E) Prop"
    by (rule source_prefix_global_language[OF eg_t]) simp
  have eg: "paper_global_H \<Sigma> G (paper_imp ?Fy ?E)"
    by (rule paper_global_H.EG[OF eg_l])

  let ?bridge = "paper_imp ?yy (paper_imp (paper_iff ?Fy ?yy) ?Fy)"
  let ?P = "SPImp (SPAtom 0) (SPImp (SPIff (SPAtom 1) (SPAtom 0)) (SPAtom 1)) :: nat sprop_template"
  let ?v = "\<lambda>k :: nat. if k = 0 then ?yy else ?Fy"
  have bridge_t: "has_stype paper_logical_type ?\<Gamma> ?bridge Prop"
    by (rule paper_imp_type[OF yyt paper_imp_type[OF iff_t fyt]])
  have bridge_l: "sgterm_in_language paper_logical_type \<Sigma> G ?bridge Prop"
    by (rule source_prefix_global_language[OF bridge_t]) simp
  have taut: "sprop_tautology ?P"
    by (simp only: sprop_tautology_def sprop_eval.simps; blast)
  have bridge_pc: "paper_global_PC \<Sigma> G ?bridge"
    unfolding paper_global_PC_def
  proof (rule conjI[OF bridge_l])
    show "\<exists>P :: nat sprop_template. \<exists>v. sprop_tautology P \<and> ?bridge = paper_prop_instance v P"
    proof (rule exI[where x="?P"], rule exI[where x="?v"], rule conjI[OF taut])
      show "?bridge = paper_prop_instance ?v ?P" by simp
    qed
  qed
  have pc: "paper_global_H \<Sigma> G ?bridge" by (rule paper_global_H.PC[OF bridge_pc])
  have intermediate_t: "has_stype paper_logical_type ?\<Gamma> (paper_imp (paper_iff ?Fy ?yy) ?Fy) Prop"
    by (rule paper_imp_type[OF iff_t fyt])
  have intermediate_l: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp (paper_iff ?Fy ?yy) ?Fy) Prop"
    by (rule source_prefix_global_language[OF intermediate_t]) simp
  have intermediate: "paper_global_H \<Sigma> G (paper_imp (paper_iff ?Fy ?yy) ?Fy)"
    by (rule paper_global_H.MP[OF ref pc intermediate_l])
  have applied: "paper_global_H \<Sigma> G ?Fy"
    by (rule paper_global_H.MP[OF beta intermediate fyl])
  show ?thesis by (rule paper_global_H.MP[OF applied eg el])
qed

theorem paper_global_type_existence:
  assumes rich: "sg_rich G"
  shows "paper_global_H \<Sigma> G
    (SApp (SLogical (SEx \<sigma>))
      (SLam \<sigma> (SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0))))"
proof -
  obtain n where variable: "G n = \<sigma>"
    by (rule sg_rich_variable[where \<sigma>=\<sigma>, OF rich]; rule that; assumption)
  show ?thesis by (rule paper_global_existence_from_variable[where G=G and n=n, OF variable])
qed

corollary paper_standard_stock_type_existence:
  "paper_global_H \<Sigma> sg_standard_stock
    (SApp (SLogical (SEx \<sigma>))
      (SLam \<sigma> (SApp (SApp (SLogical (SEq \<sigma>)) (SVar 0)) (SVar 0))))"
  by (rule paper_global_type_existence[OF sg_standard_stock_rich])

end
