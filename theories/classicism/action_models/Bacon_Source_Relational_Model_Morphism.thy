theory Bacon_Source_Relational_Model_Morphism
  imports Bacon_Source_Relational_Homomorphism Bacon_Source_Relational_BBK_Interface
begin

section \<open>Homomorphisms with specified BBK-model endpoints\<close>

text \<open>
  For M=⟨D,J,V⟩ and N=⟨E,K,W⟩, the assertion h:M→N
  requires M and N to be independent R BBK models and h to preserve their typed
  interpretations. Source: Bacon–Dorr §3.3, p.49, especially footnote 71.
  The valuations V and W validate the two endpoint models but impose
  NO additional equation on h. Truth preservation is not asserted.

  Isabelle representation: this is a relation with explicitly specified
  endpoint data, not a record of arrows or a category construction.
  The two endpoint carriers, and the three carriers in composition,
  are independent HOL types. Nothing here claims that an arbitrary
  category of source models fits into one fixed carrier type.
  Status: identities and composition for R model-aware morphisms. No F
  model, F conversion, total assignment, model extension, or converse
  R↔F transport theorem is assumed.
\<close>

definition paper_R_bbk_model_morphism ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    ('v \<Rightarrow> bool) \<Rightarrow>
    (otype \<Rightarrow> 'w set) \<Rightarrow>
    ('w named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'w) \<Rightarrow>
    ('w \<Rightarrow> bool) \<Rightarrow>
    (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h \<longleftrightarrow>
    paper_R_bbk_model \<Sigma> G D J V \<and>
    paper_R_bbk_model \<Sigma> G E K W \<and>
    paper_R_bbk_homomorphism \<Sigma> G D J E K h"

lemma paper_R_bbk_model_morphismI:
  assumes source_model: "paper_R_bbk_model \<Sigma> G D J V"
    and target_model: "paper_R_bbk_model \<Sigma> G E K W"
    and hom: "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
  shows "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
  unfolding paper_R_bbk_model_morphism_def
  by (rule conjI[OF source_model conjI[OF target_model hom]])

lemma paper_R_bbk_model_morphism_source:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_R_bbk_model \<Sigma> G D J V"
  using morphism unfolding paper_R_bbk_model_morphism_def by (rule conjunct1)

lemma paper_R_bbk_model_morphism_target:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_R_bbk_model \<Sigma> G E K W"
  using morphism unfolding paper_R_bbk_model_morphism_def
  by (rule conjunct1[OF conjunct2])

lemma paper_R_bbk_model_morphism_raw:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
  using morphism unfolding paper_R_bbk_model_morphism_def
  by (rule conjunct2[OF conjunct2])

section \<open>Endpoint-aware identity and composition\<close>

text \<open>
  Each model M has 1M:M→M. Given h:M→N and k:N→P,
  the family (k∘h)σ=kσ∘hσ is a morphism M→P.
  Source: Bacon–Dorr §3.3, pp.49–50. The middle model data,
  including its valuation, are the same in the two premises; the
  three valuations are otherwise unrelated.
\<close>

theorem paper_R_bbk_model_morphism_identity:
  assumes model: "paper_R_bbk_model \<Sigma> G D J V"
  shows "paper_R_bbk_model_morphism \<Sigma> G D J V D J V (\<lambda>\<sigma> a. a)"
  by (rule paper_R_bbk_model_morphismI[OF model model paper_R_bbk_homomorphism_identity])

theorem paper_R_bbk_model_morphism_compose:
  fixes D :: "otype \<Rightarrow> 'v set"
    and E :: "otype \<Rightarrow> 'w set"
    and F :: "otype \<Rightarrow> 'u set"
  assumes first: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and second: "paper_R_bbk_model_morphism \<Sigma> G E K W F L U k"
  shows "paper_R_bbk_model_morphism \<Sigma> G D J V F L U (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
proof -
  have source_model: "paper_R_bbk_model \<Sigma> G D J V"
    by (rule paper_R_bbk_model_morphism_source[OF first])
  have target_model: "paper_R_bbk_model \<Sigma> G F L U"
    by (rule paper_R_bbk_model_morphism_target[OF second])
  have first_raw: "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
    by (rule paper_R_bbk_model_morphism_raw[OF first])
  have second_raw: "paper_R_bbk_homomorphism \<Sigma> G E K F L k"
    by (rule paper_R_bbk_model_morphism_raw[OF second])
  have composite: "paper_R_bbk_homomorphism \<Sigma> G D J F L (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
    by (rule paper_R_bbk_homomorphism_compose[OF first_raw second_raw])
  show ?thesis by (rule paper_R_bbk_model_morphismI[OF source_model target_model composite])
qed

section \<open>Off-domain changes do not alter a model-aware morphism\<close>

text \<open>
  Only hσ on Dσ for σ∈R matters. Source-model typing ensures
  that every interpreted input to h lies in such a domain. The
  represented empty domains outside R discharge the remaining indices.
\<close>

theorem paper_R_bbk_model_morphism_cong:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and agree: "\<And>\<sigma> a. paper_R_type \<sigma> \<Longrightarrow> a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a = k \<sigma> a"
  shows "paper_R_bbk_model_morphism \<Sigma> G D J V E K W k"
proof -
  have source_model: "paper_R_bbk_model \<Sigma> G D J V"
    by (rule paper_R_bbk_model_morphism_source[OF morphism])
  have target_model: "paper_R_bbk_model \<Sigma> G E K W"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  interpret Source: paper_R_bbk_model \<Sigma> G D J V by (rule source_model)
  have all_agree: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a = k \<sigma> a"
  proof -
    fix \<sigma> a
    assume member: "a \<in> D \<sigma>"
    have rt: "paper_R_type \<sigma>" by (rule Source.paper_R_domain_member_type[OF member])
    show "h \<sigma> a = k \<sigma> a" by (rule agree[OF rt member])
  qed
  have raw: "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
    by (rule paper_R_bbk_model_morphism_raw[OF morphism])
  have replacement: "paper_R_bbk_homomorphism \<Sigma> G D J E K k"
    by (rule paper_R_bbk_homomorphism_cong[OF raw Source.denote_type all_agree])
  show ?thesis by (rule paper_R_bbk_model_morphismI[OF source_model target_model replacement])
qed

end
