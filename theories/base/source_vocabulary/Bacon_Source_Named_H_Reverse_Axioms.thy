theory Bacon_Source_Named_H_Reverse_Axioms
  imports Bacon_Source_Named_H Bacon_Source_Named_Representation_Reflection
    Bacon_Source_Axiom_Guards
begin

section \<open>Native named preimages of UI, EG, Ref and LL\<close>

text \<open>
  Each well-formed source instance of UI, EG, Ref or LL is the literal
  encoding of a theorem obtained with the corresponding native named-H
  constructor. Source: Bacon–Dorr Figure 2, p.8.

  Representation: first type the entire source axiom in its finite
  support prefix. The existing guard-extraction lemmas recover its
  operands' language judgments. Typed source surjectivity supplies named
  representatives. Their complete named axiom has the source axiom as
  its exact encoding, so language reflection supplies its native guard.

  Status: assumptions are the whole source-formula language guard and
  rich G only. No source-H theorem, reverse-proof induction hypothesis,
  model, capture restriction for primitive UI/EG, or new H rule is used.
\<close>

lemma named_reverse_prefix_global_language:
  assumes language: "sterm_in_language L \<Sigma> (source_prefix G m) A \<tau>"
  shows "sgterm_in_language L \<Sigma> G A \<tau>"
proof -
  have typed: "has_stype L (source_prefix G m) A \<tau>"
    and names: "sterm_in_signature \<Sigma> A"
    using language unfolding sterm_in_language_def by auto
  have agreement: "\<And>n \<rho>. lookup (source_prefix G m) n = Some \<rho> \<Longrightarrow> G n = \<rho>"
    by (auto simp: source_prefix_def lookup_def split: if_splits)
  have global_type: "has_sgtype L G A \<tau>"
    by (rule source_finite_to_global_typing[OF typed agreement])
  show ?thesis unfolding sgterm_in_language_def by (rule conjI[OF global_type names])
qed

lemma named_reverse_prefix_representation:
  assumes language: "sterm_in_language L \<Sigma> (source_prefix G m) A \<tau>"
    and rich: "sg_rich G"
  shows "\<exists>N. named_in_language L \<Sigma> G N \<tau> \<and> named_to_source G [] N = A"
  by (rule source_named_representation_exists[OF named_reverse_prefix_global_language[OF language] rich])

theorem paper_named_UI_preimage:
  assumes whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)"
proof -
  let ?W = "paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)"
  have finite_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) ?W Prop"
    by (rule source_language_in_prefix[OF whole]) (rule order_refl)
  have f_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) F (Arr \<sigma> Prop)"
    by (rule paper_UI_guard_operands(1)[OF finite_guard])
  have a_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) A \<sigma>"
    by (rule paper_UI_guard_operands(2)[OF finite_guard])
  obtain F' where f_language: "named_in_language paper_logical_type \<Sigma> G F' (Arr \<sigma> Prop)"
    and f_encoding: "named_to_source G [] F' = F"
    using named_reverse_prefix_representation[OF f_guard rich] by (elim exE conjE)
  obtain A' where a_language: "named_in_language paper_logical_type \<Sigma> G A' \<sigma>"
    and a_encoding: "named_to_source G [] A' = A"
    using named_reverse_prefix_representation[OF a_guard rich] by (elim exE conjE)
  let ?N = "named_paper_imp G (named_paper_all \<sigma> F') (NApp F' A')"
  have encoding: "named_to_source G [] ?N = ?W"
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_all_encoding
      named_to_source.simps f_encoding a_encoding)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoding; rule whole)
  have native_language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have theorem_N: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.UI[OF native_language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF theorem_N encoding])
qed

theorem paper_named_EG_preimage:
  assumes whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)"
proof -
  let ?W = "paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)"
  have finite_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) ?W Prop"
    by (rule source_language_in_prefix[OF whole]) (rule order_refl)
  have f_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) F (Arr \<sigma> Prop)"
    by (rule paper_EG_guard_operands(1)[OF finite_guard])
  have a_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) A \<sigma>"
    by (rule paper_EG_guard_operands(2)[OF finite_guard])
  obtain F' where f_language: "named_in_language paper_logical_type \<Sigma> G F' (Arr \<sigma> Prop)"
    and f_encoding: "named_to_source G [] F' = F"
    using named_reverse_prefix_representation[OF f_guard rich] by (elim exE conjE)
  obtain A' where a_language: "named_in_language paper_logical_type \<Sigma> G A' \<sigma>"
    and a_encoding: "named_to_source G [] A' = A"
    using named_reverse_prefix_representation[OF a_guard rich] by (elim exE conjE)
  let ?N = "named_paper_imp G (NApp F' A') (named_paper_ex \<sigma> F')"
  have encoding: "named_to_source G [] ?N = ?W"
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_ex_encoding
      named_to_source.simps f_encoding a_encoding)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoding; rule whole)
  have native_language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have theorem_N: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.EG[OF native_language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF theorem_N encoding])
qed

theorem paper_named_Ref_preimage:
  assumes whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (SApp (SApp (SLogical (SEq \<sigma>)) A) A) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    SApp (SApp (SLogical (SEq \<sigma>)) A) A"
proof -
  let ?W = "SApp (SApp (SLogical (SEq \<sigma>)) A) A"
  have finite_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) ?W Prop"
    by (rule source_language_in_prefix[OF whole]) (rule order_refl)
  have a_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) A \<sigma>"
    by (rule paper_Ref_guard_operand[OF finite_guard])
  obtain A' where a_language: "named_in_language paper_logical_type \<Sigma> G A' \<sigma>"
    and a_encoding: "named_to_source G [] A' = A"
    using named_reverse_prefix_representation[OF a_guard rich] by (elim exE conjE)
  let ?N = "named_paper_eq \<sigma> A' A'"
  have encoding: "named_to_source G [] ?N = ?W"
    by (simp only: named_paper_eq_encoding a_encoding)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoding; rule whole)
  have native_language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have theorem_N: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.Ref[OF native_language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF theorem_N encoding])
qed

theorem paper_named_LL_preimage:
  assumes whole: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B) (paper_imp (SApp F A) (SApp F B))) Prop"
    and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N =
    paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B) (paper_imp (SApp F A) (SApp F B))"
proof -
  let ?W = "paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B) (paper_imp (SApp F A) (SApp F B))"
  have finite_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) ?W Prop"
    by (rule source_language_in_prefix[OF whole]) (rule order_refl)
  have a_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) A \<sigma>"
    by (rule paper_LL_guard_operands(1)[OF finite_guard])
  have b_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) B \<sigma>"
    by (rule paper_LL_guard_operands(2)[OF finite_guard])
  have f_guard: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound ?W)) F (Arr \<sigma> Prop)"
    by (rule paper_LL_guard_operands(3)[OF finite_guard])
  obtain A' where a_language: "named_in_language paper_logical_type \<Sigma> G A' \<sigma>"
    and a_encoding: "named_to_source G [] A' = A"
    using named_reverse_prefix_representation[OF a_guard rich] by (elim exE conjE)
  obtain B' where b_language: "named_in_language paper_logical_type \<Sigma> G B' \<sigma>"
    and b_encoding: "named_to_source G [] B' = B"
    using named_reverse_prefix_representation[OF b_guard rich] by (elim exE conjE)
  obtain F' where f_language: "named_in_language paper_logical_type \<Sigma> G F' (Arr \<sigma> Prop)"
    and f_encoding: "named_to_source G [] F' = F"
    using named_reverse_prefix_representation[OF f_guard rich] by (elim exE conjE)
  let ?N = "named_paper_imp G (named_paper_eq \<sigma> A' B')
    (named_paper_imp G (NApp F' A') (NApp F' B'))"
  have encoding: "named_to_source G [] ?N = ?W"
    by (simp only: named_paper_imp_encoding[OF rich] named_paper_eq_encoding
      named_to_source.simps a_encoding b_encoding f_encoding)
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    by (simp only: encoding; rule whole)
  have native_language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have theorem_N: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.LL[OF native_language])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF theorem_N encoding])
qed

end
