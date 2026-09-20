theory Goodman_Named_Root_Conversion
  imports Goodman_Named_Substitution
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Conversion
begin

section \<open>Typed named β and η conversion for translated root redexes\<close>

lemma gi_to_book_named_language:
  "sg_rich G \<Longrightarrow> \<Gamma> \<turnstile> A : \<tau> \<Longrightarrow> map G ns = \<Gamma> \<Longrightarrow>
    gi_constants_admitted k \<Sigma> A \<Longrightarrow>
    named_in_language book_minimal_logical_type \<Sigma> G (gi_to_book G ns k A) \<tau>"
  by (rule book_language_named, rule gi_to_book_language; assumption)

lemma gi_constants_rename:
  "gi_constants_admitted k \<Sigma> (rename r A) = gi_constants_admitted k \<Sigma> A"
  by (induction A arbitrary: r) simp_all

theorem gi_to_book_beta_root:
  assumes rich: "sg_rich G" and body: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and argument: "\<Gamma> \<turnstile> N : \<sigma>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and body_constants: "gi_constants_admitted k \<Sigma> M"
    and argument_constants: "gi_constants_admitted k \<Sigma> N"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    (gi_to_book G ns k (App (Lam \<sigma> M) N)) (gi_to_book G ns k (subst0 N M))"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?B = "gi_to_book G ns k N"
  let ?A = "gi_to_book G (?n # ns) k M"
  let ?R = "named_subst ?n ?B ?A"
  let ?L = "gi_to_book G ns k (App (Lam \<sigma> M) N)"
  have typed: "\<Gamma> \<turnstile> App (Lam \<sigma> M) N : \<tau>"
    by (rule has_type.App[OF has_type.Lam[OF body] argument])
  have constants: "gi_constants_admitted k \<Sigma> (App (Lam \<sigma> M) N)"
    using body_constants argument_constants by simp
  have left: "named_in_language book_minimal_logical_type \<Sigma> G ?L \<tau>"
    by (rule gi_to_book_named_language[OF rich typed chart constants])
  have body_language: "named_in_language book_minimal_logical_type \<Sigma> G ?A \<tau>"
    by (rule gi_to_book_named_language[OF rich body gi_chart_extension[OF rich chart] body_constants])
  have argument_language: "named_in_language book_minimal_logical_type \<Sigma> G ?B (G ?n)"
    using gi_to_book_named_language[OF rich argument chart argument_constants]
    by (simp only: named_chart_fresh_type[OF rich])
  have intermediate: "named_in_language book_minimal_logical_type \<Sigma> G ?R \<tau>"
    by (rule named_subst_language[OF body_language argument_language])
  have support: "named_fv ?B \<subseteq> set (?n # ns)"
    using gi_to_book_fv_subset[OF rich argument chart] by auto
  have free: "named_free_for ?B ?n ?A" by (rule gi_translation_free_for[OF rich support])
  have root: "named_beta_contract ?L ?R"
    by (simp only: gi_to_book.simps Let_def; rule named_beta_contract.beta[OF free])
  have step: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau> ?L ?R"
    by (rule named_beta_eta_in_language.Beta[OF left intermediate], rule named_compatible_step.root, rule root)
  have alpha: "named_alpha G ?R (gi_to_book G ns k (subst0 N M))"
    by (rule gi_to_book_subst0_alpha[OF rich body argument chart distinct])
  have tail: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau>
    ?R (gi_to_book G ns k (subst0 N M))"
    by (rule named_alpha_implies_beta_eta[OF alpha intermediate])
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF step tail])
qed

theorem gi_to_book_eta_root:
  assumes rich: "sg_rich G" and fn: "\<Gamma> \<turnstile> F : Arr \<sigma> \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants: "gi_constants_admitted k \<Sigma> F"
  shows "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G (Arr \<sigma> \<tau>)
    (gi_to_book G ns k (Lam \<sigma> (App (shift F) (Var 0)))) (gi_to_book G ns k F)"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?F = "gi_to_book G ns k F"
  let ?L = "gi_to_book G ns k (Lam \<sigma> (App (shift F) (Var 0)))"
  let ?R = "NLam ?n (NApp ?F (NVar ?n))"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have name_type: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have shifted_alpha: "named_alpha G (gi_to_book G (?n # ns) k (shift F)) ?F"
    by (rule gi_to_book_shift_alpha[OF rich fn chart distinct fresh name_type])
  have alpha: "named_alpha G ?L ?R"
    by (simp only: gi_to_book.simps Let_def nth_Cons_0;
      rule named_alpha.Lam, rule named_alpha.App[OF shifted_alpha named_alpha.Refl])
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift F : Arr \<sigma> \<tau>" by (rule weakening_front[OF fn])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by simp
  have redex_type: "\<Gamma> \<turnstile> Lam \<sigma> (App (shift F) (Var 0)) : Arr \<sigma> \<tau>"
    by (rule has_type.Lam[OF has_type.App[OF shifted variable]])
  have redex_constants: "gi_constants_admitted k \<Sigma> (Lam \<sigma> (App (shift F) (Var 0)))"
    using constants by (simp add: shift_def gi_constants_rename)
  have left: "named_in_language book_minimal_logical_type \<Sigma> G ?L (Arr \<sigma> \<tau>)"
    by (rule gi_to_book_named_language[OF rich redex_type chart redex_constants])
  have intermediate: "named_in_language book_minimal_logical_type \<Sigma> G ?R (Arr \<sigma> \<tau>)"
    using left named_alpha_language_iff[OF alpha] by blast
  have right: "named_in_language book_minimal_logical_type \<Sigma> G ?F (Arr \<sigma> \<tau>)"
    by (rule gi_to_book_named_language[OF rich fn chart constants])
  have absent: "?n \<notin> named_fv ?F"
    using fresh gi_to_book_fv_subset[OF rich fn chart] by blast
  have eta: "named_eta_contract ?R ?F" by (rule named_eta_contract.eta[OF absent])
  have step: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G (Arr \<sigma> \<tau>) ?R ?F"
    by (rule named_beta_eta_in_language.Eta[OF intermediate right], rule named_compatible_step.root, rule eta)
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF named_alpha_implies_beta_eta[OF alpha left] step])
qed

text \<open>
  Both conclusions use the core's independently generated, typed and
  signature-guarded named βη relation. Every intermediate term has a
  checked language witness. This closes the ROOT-redex correspondence,
  not contextual named conversion or H/CEV+ proof preservation.
\<close>

end
