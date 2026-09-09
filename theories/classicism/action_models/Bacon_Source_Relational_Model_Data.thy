theory Bacon_Source_Relational_Model_Data
  imports Bacon_Source_BBK_Model_Data Bacon_Source_Relational_Model_Morphism
begin

section \<open>Specified model data for category objects\<close>

text \<open>
  An R BBK model has domains Dσ for σ∈R, a named interpretation J, and a
  valuation V. The record retains ALL three fields: models with the
  same domains and interpretation but different valuations must not be
  silently identified. Source: Bacon–Dorr Definition 3.1, pp.43–44,
  and §3.3, p.49, footnote 71.

  Signature Σ and stock G are fixed externally for a category of models.
  A record is only data; paper_R_bbk_data_valid asserts the existing
  independent R named-model conditions. The old F validator is not used.
  Only the generic three-field record is reused as data. The record uses one specified HOL
  value carrier, while morphisms below can connect different carriers.
  No claim that all source models fit one HOL type is made.
\<close>

definition paper_R_bbk_data_valid ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> bool" where
  "paper_R_bbk_data_valid \<Sigma> G M \<longleftrightarrow>
    paper_R_bbk_model \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)"

lemma paper_R_bbk_data_model:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_R_bbk_model \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)"
  using valid unfolding paper_R_bbk_data_valid_def by assumption

lemma paper_R_bbk_data_stock_rich:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_R_rich G"
proof -
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_R_bbk_data_model[OF valid])
  show ?thesis by (rule Model.stock_rich)
qed

lemma paper_R_bbk_data_domain_nonempty:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M" and rt: "paper_R_type \<sigma>"
  shows "paper_bbk_domain M \<sigma> \<noteq> {}"
proof -
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_R_bbk_data_model[OF valid])
  show ?thesis by (rule Model.domain_nonempty[OF rt])
qed

lemma paper_R_bbk_data_domain_empty:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M" and outside: "\<not> paper_R_type \<sigma>"
  shows "paper_bbk_domain M \<sigma> = {}"
proof -
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_R_bbk_data_model[OF valid])
  show ?thesis by (rule Model.domain_empty[OF outside])
qed

lemma paper_R_bbk_data_denote_type:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and language: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_denote M g A \<in> paper_bbk_domain M \<sigma>"
proof -
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_R_bbk_data_model[OF valid])
  show ?thesis by (rule Model.denote_type[OF language typed adequate])
qed

section \<open>Morphisms between specified records\<close>

text \<open>
  A morphism M→N uses the existing endpoint-aware predicate. Valuations
  appear in endpoint validity but are not preserved by the map. Identity
  and composition keep the specified endpoint records, including the
  common middle model in a composite. These are not yet arrow records or
  a category construction.
\<close>

definition paper_R_bbk_data_morphism ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow>
    ('c,'w) paper_bbk_model_data \<Rightarrow> (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "paper_R_bbk_data_morphism \<Sigma> G M N h \<longleftrightarrow>
    paper_R_bbk_model_morphism \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
      (paper_bbk_domain N) (paper_bbk_denote N) (paper_bbk_valuation N) h"

lemma paper_R_bbk_data_morphism_source:
  assumes morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
  shows "paper_R_bbk_data_valid \<Sigma> G M"
  unfolding paper_R_bbk_data_valid_def
  by (rule paper_R_bbk_model_morphism_source[OF morphism[unfolded paper_R_bbk_data_morphism_def]])

lemma paper_R_bbk_data_morphism_target:
  assumes morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
  shows "paper_R_bbk_data_valid \<Sigma> G N"
  unfolding paper_R_bbk_data_valid_def
  by (rule paper_R_bbk_model_morphism_target[OF morphism[unfolded paper_R_bbk_data_morphism_def]])

lemma paper_R_bbk_data_morphism_raw:
  assumes morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
  shows "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
    (paper_bbk_domain N) (paper_bbk_denote N) h"
  by (rule paper_R_bbk_model_morphism_raw[OF morphism[unfolded paper_R_bbk_data_morphism_def]])

theorem paper_R_bbk_data_morphism_identity:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_R_bbk_data_morphism \<Sigma> G M M (\<lambda>\<sigma> a. a)"
  unfolding paper_R_bbk_data_morphism_def
  by (rule paper_R_bbk_model_morphism_identity[OF paper_R_bbk_data_model[OF valid]])

theorem paper_R_bbk_data_morphism_compose:
  fixes M :: "('c,'v) paper_bbk_model_data"
    and N :: "('c,'w) paper_bbk_model_data"
    and P :: "('c,'u) paper_bbk_model_data"
  assumes first: "paper_R_bbk_data_morphism \<Sigma> G M N h"
    and second: "paper_R_bbk_data_morphism \<Sigma> G N P k"
  shows "paper_R_bbk_data_morphism \<Sigma> G M P (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
  unfolding paper_R_bbk_data_morphism_def
  by (rule paper_R_bbk_model_morphism_compose[
    OF first[unfolded paper_R_bbk_data_morphism_def] second[unfolded paper_R_bbk_data_morphism_def]])

text \<open>
  Raw record equality also compares total-function values outside genuine
  interpretation inputs and outside Dₜ. Those extensions are not source
  model data. A separate canonical normalization is required before raw
  record equality is used as source-faithful category-object equality.
\<close>

end
