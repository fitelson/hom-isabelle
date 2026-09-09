theory Bacon_Book_Modal_Term_Inhabitation
  imports Bacon_Book_Proposition_Representation
    Bacon_Book_Environment_Development.Bacon_Book_Minimal_Existential_Truth
begin

section \<open>Witness completeness gives a constant, and a domain value, at every type\<close>

definition book_inhabitation_predicate where
  "book_inhabitation_predicate G \<sigma> = NLam (named_chart_fresh G [] \<sigma>) (book_top G)"

lemma book_inhabitation_predicate_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_inhabitation_predicate G \<sigma>) (Arr \<sigma> Prop)"
  unfolding book_inhabitation_predicate_def
  using book_language_Lam[where n="named_chart_fresh G [] \<sigma>", OF book_top_language[OF rich]]
  by (simp only: named_chart_fresh_type[OF rich])

lemma book_inhabitation_predicate_closed:
  "named_fv (book_inhabitation_predicate G \<sigma>) = {}"
  by (simp add: book_inhabitation_predicate_def book_top_closed)

theorem book_H_exists_inhabitation_predicate:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (NApp (book_exists_const G \<sigma>) (book_inhabitation_predicate G \<sigma>))"
proof (rule book_H_from_pointwise_models[OF rich book_exists_application_language[
  OF rich book_inhabitation_predicate_language[OF rich]]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
  assume model: "book_full_minimal_model D app \<Sigma> G J V k" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
  let ?n = "named_chart_fresh G [] \<sigma>"
  let ?F = "book_inhabitation_predicate G \<sigma>"
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have gm: "g ?n \<in> D (G ?n)" using typed unfolding book_env_typed_def by blast
  have sm: "g ?n \<in> D \<sigma>" using gm by (simp only: nt)
  have evaluated: "app \<sigma> Prop (J g ?F) (g ?n) = J g (book_top G)"
    using M.book_full_lambda_application[where n="?n", OF book_top_language[OF rich] typed gm]
    by (simp add: book_inhabitation_predicate_def nt)
  have truth: "V (app \<sigma> Prop (J g ?F) (g ?n))"
    by (simp only: evaluated; rule M.book_top_true[OF rich typed])
  have witness: "\<exists>a\<in>D \<sigma>. V (app \<sigma> Prop (J g ?F) a)"
    by (rule bexI[where x="g ?n"], rule truth, rule sm)
  show "V (J g (NApp (book_exists_const G \<sigma>) ?F))"
    by (simp only: M.book_exists_application_truth[OF rich typed book_inhabitation_predicate_language[OF rich]]; rule witness)
qed

theorem book_C_canonical_signature_inhabited:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
  shows "\<exists>c. c \<in> fst w \<sigma>"
proof -
  let ?F = "book_inhabitation_predicate G \<sigma>"
  let ?E = "NApp (book_exists_const G \<sigma>) ?F"
  have maximal: "book_C_closed_maximal_extension (fst w) G {} (snd w)" by (rule book_C_canonical_world_data(4)[OF world])
  have Hmax: "book_closed_maximal_extension (fst w) G (book_C_closed_theorems (fst w) G \<union> {}) (snd w)"
    using maximal unfolding book_C_closed_maximal_extension_def .
  have fl: "book_in_language book_minimal_logical_type UNIV (fst w) G ?F (Arr \<sigma> Prop)"
    by (rule book_inhabitation_predicate_language[OF rich])
  have fc: "named_fv ?F = {}" by (rule book_inhabitation_predicate_closed)
  have el: "book_theory_formula (fst w) G ?E" by (rule book_exists_application_language[OF rich fl])
  have ec: "named_fv ?E = {}" by (simp only: book_exists_application_fv fc)
  have original: "book_C_proves (fst w) G ?E" by (rule book_C_proves.H[OF book_H_exists_inhabitation_predicate[OF rich]])
  have positive: "?E \<in> snd w" by (rule book_C_closed_maximal_original_theorem[OF rich maximal original ec])
  have not_negative: "book_not G ?E \<notin> snd w"
    using book_closed_maximal_negation_iff[OF rich Hmax el ec] positive by blast
  have witness_complete: "book_closed_constant_witness_complete (fst w) G (snd w)"
    by (rule book_C_canonical_world_data(5)[OF world])
  have alternatives: "book_not G ?E \<in> snd w \<or> (\<exists>c\<in>fst w \<sigma>. NApp ?F (NConst c \<sigma>) \<in> snd w)"
    using witness_complete fl fc unfolding book_closed_constant_witness_complete_def by blast
  show ?thesis using alternatives not_negative by blast
qed

theorem book_C_canonical_identity_domain_nonempty:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
  shows "book_C_identity_domain (fst w) G (snd w) \<sigma> \<noteq> {}"
proof -
  obtain c where cm: "c \<in> fst w \<sigma>" using book_C_canonical_signature_inhabited[OF rich world] by blast
  have cl: "book_in_language book_minimal_logical_type UNIV (fst w) G (NConst c \<sigma>) \<sigma>"
    by (simp only: book_language_const_iff; rule conjI[OF refl cm])
  have closed_term: "NConst c \<sigma> \<in> book_closed_terms (fst w) G \<sigma>" by (rule book_closed_termsI[OF cl]; simp)
  have value_member: "book_C_identity_class (fst w) G (snd w) \<sigma> (NConst c \<sigma>) \<in>
    book_C_identity_domain (fst w) G (snd w) \<sigma>"
    unfolding book_C_identity_domain_def by (rule imageI[OF closed_term])
  show ?thesis using value_member by blast
qed

text \<open>
  H proves ∃σ(λxσ.⊤). At each canonical world its negation is excluded
  by consistency, and constant-witness completeness supplies a declared
  c:σ. Hence the closed term domain, and its identity-class domain, are
  nonempty at every type. This is proved for every canonical world, not
  just for worlds obtained by one particular Henkin-stage construction.
  It adds no domain-inhabitation axiom or semantic model premise.
\<close>

end
