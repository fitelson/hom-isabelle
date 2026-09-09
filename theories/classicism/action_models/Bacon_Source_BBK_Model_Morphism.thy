theory Bacon_Source_BBK_Model_Morphism
  imports Bacon_Source_BBK_Homomorphism
begin

section \<open>Homomorphisms with specified BBK-model endpoints\<close>

text \<open>
  For M=⟨D,J,V⟩ and N=⟨E,K,W⟩, the assertion h:M→N
  requires M and N to be BBK models and h to preserve their typed
  interpretations. Source: Bacon–Dorr §3.3, p.49, especially footnote 71.
  The valuations V and W validate the two endpoint models but impose
  NO additional equation on h. Truth preservation is not asserted.

  Isabelle representation: this is a relation with explicitly specified
  endpoint data, not a record of arrows or a category construction.
  The two endpoint carriers, and the three carriers in composition,
  are independent HOL types. Nothing here claims that an arbitrary
  category of source models fits into one fixed carrier type.
\<close>

definition paper_bbk_model_morphism ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    ('v \<Rightarrow> bool) \<Rightarrow>
    (otype \<Rightarrow> 'w set) \<Rightarrow>
    ('w named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'w) \<Rightarrow>
    ('w \<Rightarrow> bool) \<Rightarrow>
    (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "paper_bbk_model_morphism \<Sigma> G D J V E K W h \<longleftrightarrow>
    paper_named_bbk_model \<Sigma> G D J V \<and>
    paper_named_bbk_model \<Sigma> G E K W \<and>
    paper_bbk_homomorphism \<Sigma> G D J E K h"

lemma paper_bbk_model_morphismI:
  assumes source_model: "paper_named_bbk_model \<Sigma> G D J V"
    and target_model: "paper_named_bbk_model \<Sigma> G E K W"
    and hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
  shows "paper_bbk_model_morphism \<Sigma> G D J V E K W h"
  unfolding paper_bbk_model_morphism_def
  by (rule conjI[OF source_model conjI[OF target_model hom]])

lemma paper_bbk_model_morphism_source:
  assumes morphism: "paper_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_named_bbk_model \<Sigma> G D J V"
  using morphism unfolding paper_bbk_model_morphism_def by (rule conjunct1)

lemma paper_bbk_model_morphism_target:
  assumes morphism: "paper_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_named_bbk_model \<Sigma> G E K W"
  using morphism unfolding paper_bbk_model_morphism_def
  by (rule conjunct1[OF conjunct2])

lemma paper_bbk_model_morphism_raw:
  assumes morphism: "paper_bbk_model_morphism \<Sigma> G D J V E K W h"
  shows "paper_bbk_homomorphism \<Sigma> G D J E K h"
  using morphism unfolding paper_bbk_model_morphism_def
  by (rule conjunct2[OF conjunct2])

section \<open>Endpoint-aware identity and composition\<close>

text \<open>
  Each model M has 1M:M→M. Given h:M→N and k:N→P,
  the family (k∘h)σ=kσ∘hσ is a morphism M→P.
  Source: Bacon–Dorr §3.3, pp.49–50. The middle model data,
  including its valuation, are the same in the two premises; the
  three valuations are otherwise unrelated.
\<close>

theorem paper_bbk_model_morphism_identity:
  assumes model: "paper_named_bbk_model \<Sigma> G D J V"
  shows "paper_bbk_model_morphism \<Sigma> G D J V D J V (\<lambda>\<sigma> a. a)"
  by (rule paper_bbk_model_morphismI[OF model model paper_bbk_homomorphism_identity])

theorem paper_bbk_model_morphism_compose:
  fixes D :: "otype \<Rightarrow> 'v set"
    and E :: "otype \<Rightarrow> 'w set"
    and F :: "otype \<Rightarrow> 'u set"
  assumes first: "paper_bbk_model_morphism \<Sigma> G D J V E K W h"
    and second: "paper_bbk_model_morphism \<Sigma> G E K W F L U k"
  shows "paper_bbk_model_morphism \<Sigma> G D J V F L U (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
proof -
  have source_model: "paper_named_bbk_model \<Sigma> G D J V"
    by (rule paper_bbk_model_morphism_source[OF first])
  have target_model: "paper_named_bbk_model \<Sigma> G F L U"
    by (rule paper_bbk_model_morphism_target[OF second])
  have first_raw: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    by (rule paper_bbk_model_morphism_raw[OF first])
  have second_raw: "paper_bbk_homomorphism \<Sigma> G E K F L k"
    by (rule paper_bbk_model_morphism_raw[OF second])
  have composite: "paper_bbk_homomorphism \<Sigma> G D J F L (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
    by (rule paper_bbk_homomorphism_compose[OF first_raw second_raw])
  show ?thesis by (rule paper_bbk_model_morphismI[OF source_model target_model composite])
qed

end
