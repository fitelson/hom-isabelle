theory Bacon_Source_Relational_Normalization_Morphisms
  imports Bacon_Source_Relational_Normalization_Validity
begin

section \<open>Normalizing a morphism's target record\<close>

theorem paper_R_bbk_homomorphism_normalize_target:
  assumes hom: "paper_R_bbk_homomorphism \<Sigma> G D J
    (paper_bbk_domain N) (paper_bbk_denote N) h"
  shows "paper_R_bbk_homomorphism \<Sigma> G D J
    (paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G N))
    (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G N)) h"
proof (simp only: paper_R_bbk_normalize_domain; rule paper_R_bbk_homomorphismI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  show "h \<sigma> a \<in> paper_bbk_domain N \<sigma>"
    by (rule paper_R_bbk_homomorphism_domain[OF hom member])
next
  fix \<sigma> A g
  assume language: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  have target_typed: "named_env_typed (paper_bbk_domain N) G (paper_hom_assignment G h g)"
    by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
  have target_adequate: "named_adequate (paper_hom_assignment G h g) A"
    by (rule paper_R_bbk_homomorphism_assignment_adequate[OF adequate])
  have original: "h \<sigma> (J g A) = paper_bbk_denote N (paper_hom_assignment G h g) A"
    by (rule paper_R_bbk_homomorphism_denote[OF hom language typed adequate])
  show "h \<sigma> (J g A) =
      paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G N) (paper_hom_assignment G h g) A"
    by (simp only: paper_R_bbk_normalize_denote[OF language target_typed target_adequate]; rule original)
qed

theorem paper_R_bbk_data_morphism_normalize_target:
  assumes morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
  shows "paper_R_bbk_data_morphism \<Sigma> G M (paper_R_bbk_normalize \<Sigma> G N) h"
proof -
  have source_valid: "paper_R_bbk_data_valid \<Sigma> G M"
    by (rule paper_R_bbk_data_morphism_source[OF morphism])
  have target_valid: "paper_R_bbk_data_valid \<Sigma> G N"
    by (rule paper_R_bbk_data_morphism_target[OF morphism])
  have normalized_valid: "paper_R_bbk_data_valid \<Sigma> G (paper_R_bbk_normalize \<Sigma> G N)"
    by (rule paper_R_bbk_normalize_valid[OF target_valid])
  have raw: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain (paper_R_bbk_normalize \<Sigma> G N))
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G N)) h"
    by (rule paper_R_bbk_homomorphism_normalize_target[
      OF paper_R_bbk_data_morphism_raw[OF morphism]])
  show ?thesis unfolding paper_R_bbk_data_morphism_def
    by (rule paper_R_bbk_model_morphismI[
      OF paper_R_bbk_data_model[OF source_valid] paper_R_bbk_data_model[OF normalized_valid] raw])
qed

text \<open>
  This changes the TARGET RECORD, not the typed map's off-domain
  extension. Every transported assignment is typed and adequate, so
  the target denotation is unchanged where the homomorphism tests it.
  The source and target may have different HOL value carriers.
  No valuation-preservation condition is introduced. Source: §3.3,
  p.49 n.71, and the target normalization in the p.52 bounded category.
\<close>

end
