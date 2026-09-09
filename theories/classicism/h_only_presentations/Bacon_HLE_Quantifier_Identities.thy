theory Bacon_HLE_Quantifier_Identities
  imports Bacon_H_Equivalence_Syntax_Bridge
    Bacon_H_Forall_Distribution Bacon_H_Exists_Distribution
begin

section \<open>The four quantified Classical Identities from H plus Logical Equivalence\<close>

text \<open>
  The absorption and distribution bodies in Figure 4 are materially
  equivalent in H. Logical Equivalence therefore identifies the displayed
  λ-operations (Bacon–Dorr Appendix A introduction, p.65; Bacon
  Theorem 6.1, pp.126–127).

  Isabelle representation: absorption uses Δ = [σ,pred_ty σ], yielding
  outer-to-inner binders λF:σ → t.λy:σ. Distribution uses
  Δ = [t,pred_ty σ], yielding λF:σ → t.λp:t. The context prefix is
  reversed exactly once by C_abstract_prefix.

  Status: HLE_proves conclusions obtained from H-only biconditionals via
  HLE_abstraction. C-prefixed structural syntax is reused through the checked
  bridge, but no C, CE, CEV theorem, model, or operation identity is used as
  a premise. These are the represented full-F, unrestricted-string schemas;
  literal named-source correspondence remains a separate obligation.
\<close>

theorem HLE_absorb_disj_forall:
  "HLE_proves \<Gamma> (classic_absorb_disj_forall \<sigma>)"
proof -
  let ?\<Delta> = "[\<sigma>, pred_ty \<sigma>]"
  let ?B = "App (shift (Var 1)) (Var 0)"
  let ?R = "App (Var 1) (Var 0)"
  let ?L = "Disj ?R (Forall \<sigma> ?B)"
  have F: "?\<Delta> @ \<Gamma> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: pred_ty_def lookup_def)
  have T: "?\<Delta> @ \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  have rt: "?\<Delta> @ \<Gamma> \<turnstile> ?R : Prop" by (rule has_type.App[OF F T])
  have qt: "?\<Delta> @ \<Gamma> \<turnstile> Forall \<sigma> ?B : Prop"
    by (rule has_type.Forall[OF Hq_predicate_body_type[OF F]])
  have lt: "?\<Delta> @ \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Disj[OF rt qt])
  have equivalent: "?\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?L \<longleftrightarrow>\<^sub>o ?R)"
    by (rule Hq_absorb_disj_forall[OF F T])
  note lifted = HLE_abstraction[where \<Delta>="?\<Delta>" and \<Gamma>=\<Gamma>, OF lt rt equivalent]
  show ?thesis using lifted
    by (simp add: classic_absorb_disj_forall_def C_abstract_prefix_def shift_def numeral_2_eq_2)
qed

theorem HLE_absorb_conj_exists:
  "HLE_proves \<Gamma> (classic_absorb_conj_exists \<sigma>)"
proof -
  let ?\<Delta> = "[\<sigma>, pred_ty \<sigma>]"
  let ?B = "App (shift (Var 1)) (Var 0)"
  let ?R = "App (Var 1) (Var 0)"
  let ?L = "Conj ?R (Exists \<sigma> ?B)"
  have F: "?\<Delta> @ \<Gamma> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: pred_ty_def lookup_def)
  have T: "?\<Delta> @ \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  have rt: "?\<Delta> @ \<Gamma> \<turnstile> ?R : Prop" by (rule has_type.App[OF F T])
  have qt: "?\<Delta> @ \<Gamma> \<turnstile> Exists \<sigma> ?B : Prop"
    by (rule has_type.Exists[OF Hq_predicate_body_type[OF F]])
  have lt: "?\<Delta> @ \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Conj[OF rt qt])
  have equivalent: "?\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?L \<longleftrightarrow>\<^sub>o ?R)"
    by (rule Hq_absorb_conj_exists[OF F T])
  note lifted = HLE_abstraction[where \<Delta>="?\<Delta>" and \<Gamma>=\<Gamma>, OF lt rt equivalent]
  show ?thesis using lifted
    by (simp add: classic_absorb_conj_exists_def C_abstract_prefix_def shift_def numeral_2_eq_2)
qed

theorem HLE_dist_disj_forall:
  "HLE_proves \<Gamma> (classic_dist_disj_forall \<sigma>)"
proof -
  let ?\<Delta> = "[Prop, pred_ty \<sigma>]"
  let ?B = "App (shift (Var 1)) (Var 0)"
  let ?L = "Disj (Var 0) (Forall \<sigma> ?B)"
  let ?R = "Forall \<sigma> (Disj (shift (Var 0)) ?B)"
  have F: "?\<Delta> @ \<Gamma> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: pred_ty_def lookup_def)
  have P: "?\<Delta> @ \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have bt: "\<sigma> # (?\<Delta> @ \<Gamma>) \<turnstile> ?B : Prop" by (rule Hq_predicate_body_type[OF F])
  have qt: "?\<Delta> @ \<Gamma> \<turnstile> Forall \<sigma> ?B : Prop" by (rule has_type.Forall[OF bt])
  have lt: "?\<Delta> @ \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Disj[OF P qt])
  have rt: "?\<Delta> @ \<Gamma> \<turnstile> ?R : Prop"
    by (rule has_type.Forall[OF has_type.Disj[OF weakening_front[OF P] bt]])
  have equivalent: "?\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?L \<longleftrightarrow>\<^sub>o ?R)"
    by (rule Hq_dist_disj_forall_predicate[OF F P])
  note lifted = HLE_abstraction[where \<Delta>="?\<Delta>" and \<Gamma>=\<Gamma>, OF lt rt equivalent]
  show ?thesis using lifted
    by (simp add: classic_dist_disj_forall_def C_abstract_prefix_def shift_def numeral_2_eq_2)
qed

theorem HLE_dist_conj_exists:
  "HLE_proves \<Gamma> (classic_dist_conj_exists \<sigma>)"
proof -
  let ?\<Delta> = "[Prop, pred_ty \<sigma>]"
  let ?B = "App (shift (Var 1)) (Var 0)"
  let ?L = "Conj (Var 0) (Exists \<sigma> ?B)"
  let ?R = "Exists \<sigma> (Conj (shift (Var 0)) ?B)"
  have F: "?\<Delta> @ \<Gamma> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: pred_ty_def lookup_def)
  have P: "?\<Delta> @ \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have bt: "\<sigma> # (?\<Delta> @ \<Gamma>) \<turnstile> ?B : Prop" by (rule Hq_predicate_body_type[OF F])
  have qt: "?\<Delta> @ \<Gamma> \<turnstile> Exists \<sigma> ?B : Prop" by (rule has_type.Exists[OF bt])
  have lt: "?\<Delta> @ \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Conj[OF P qt])
  have rt: "?\<Delta> @ \<Gamma> \<turnstile> ?R : Prop"
    by (rule has_type.Exists[OF has_type.Conj[OF weakening_front[OF P] bt]])
  have equivalent: "?\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?L \<longleftrightarrow>\<^sub>o ?R)"
    by (rule Hq_dist_conj_exists_predicate[OF F P])
  note lifted = HLE_abstraction[where \<Delta>="?\<Delta>" and \<Gamma>=\<Gamma>, OF lt rt equivalent]
  show ?thesis using lifted
    by (simp add: classic_dist_conj_exists_def C_abstract_prefix_def shift_def numeral_2_eq_2)
qed

end
