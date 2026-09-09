theory Bacon_Source_BBK_Homomorphism
  imports Bacon_Source_Homomorphism_Assignments
    Bacon_Source_Model_Development.Bacon_Source_Named_BBK_Interface
begin

section \<open>Typed maps commuting with named-term denotation\<close>

text \<open>
  hσ : Mσ → Nσ and hσ(⟦A⟧Mᵍ) = ⟦A⟧Nʰ∘ᵍ, for every
  A:σ in the common language and each typed assignment g adequate for A.
  Source: Bacon–Dorr §3.3, p.49, including footnote 71.

  The predicate below states these conditions on domains and interpretations
  alone. The source and target HOL carriers may differ. In its intended use
  the supplied structures belong to BBK models, but neither model predicate
  nor either valuation is built into this raw condition. Footnote 71
  explicitly excludes valuations from the preservation requirement.
  Packaging a category arrow with its specified source and target models is
  a separate construction; this predicate does not encode that metadata.

  Scope: the first-class paper basis, full F, arbitrary nonlogical signature
  Σ, and the same named variable stock G on both sides. No richness,
  injectivity, surjectivity, truth preservation or Functionality is assumed.
\<close>

definition paper_bbk_homomorphism ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    (otype \<Rightarrow> 'w set) \<Rightarrow>
    ('w named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'w) \<Rightarrow>
    (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "paper_bbk_homomorphism \<Sigma> G D J E K h \<longleftrightarrow>
    (\<forall>\<sigma> a. a \<in> D \<sigma> \<longrightarrow> h \<sigma> a \<in> E \<sigma>) \<and>
    (\<forall>\<sigma> A g. named_in_language paper_logical_type \<Sigma> G A \<sigma> \<longrightarrow>
      named_env_typed D G g \<longrightarrow> named_adequate g A \<longrightarrow>
      h \<sigma> (J g A) = K (paper_hom_assignment G h g) A)"

lemma paper_bbk_homomorphismI:
  assumes domains: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a \<in> E \<sigma>"
    and terms: "\<And>\<sigma> A g. named_in_language paper_logical_type \<Sigma> G A \<sigma> \<Longrightarrow>
      named_env_typed D G g \<Longrightarrow> named_adequate g A \<Longrightarrow>
      h \<sigma> (J g A) = K (paper_hom_assignment G h g) A"
  shows "paper_bbk_homomorphism \<Sigma> G D J E K h"
  unfolding paper_bbk_homomorphism_def
  by (intro conjI allI impI; (rule domains | rule terms); assumption)

lemma paper_bbk_homomorphism_domain:
  assumes hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and member: "a \<in> D \<sigma>"
  shows "h \<sigma> a \<in> E \<sigma>"
  using hom member unfolding paper_bbk_homomorphism_def by blast

lemma paper_bbk_homomorphism_denote:
  assumes hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  shows "h \<sigma> (J g A) = K (paper_hom_assignment G h g) A"
  using hom language typed adequate unfolding paper_bbk_homomorphism_def by blast

lemma paper_bbk_homomorphism_assignment_typed:
  assumes hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and typed: "named_env_typed D G g"
  shows "named_env_typed E G (paper_hom_assignment G h g)"
proof (rule paper_hom_assignment_typed[where D=D and E=E, OF _ typed])
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  show "h \<sigma> a \<in> E \<sigma>" by (rule paper_bbk_homomorphism_domain[OF hom member])
qed

section \<open>Identity and composition\<close>

text \<open>
  The families 1σ(a)=a and (k∘h)σ(a)=kσ(hσ(a)) preserve
  interpretations. Source: Bacon–Dorr §3.3, p.49, immediately after
  the homomorphism definition. Composition first transports the typed,
  adequate assignment to the intermediate domains, then uses the second
  commuting equation. These results require no BBK model axioms.
\<close>

theorem paper_bbk_homomorphism_identity:
  "paper_bbk_homomorphism \<Sigma> G D J D J (\<lambda>\<sigma> a. a)"
proof (rule paper_bbk_homomorphismI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  show "a \<in> D \<sigma>" by (rule member)
next
  fix \<sigma> A g
  assume "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and "named_env_typed D G g" and "named_adequate g A"
  show "J g A = J (paper_hom_assignment G (\<lambda>\<sigma> a. a) g) A"
    by (simp only: paper_hom_assignment_identity)
qed

theorem paper_bbk_homomorphism_compose:
  assumes first: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and second: "paper_bbk_homomorphism \<Sigma> G E K F L k"
  shows "paper_bbk_homomorphism \<Sigma> G D J F L (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
proof (rule paper_bbk_homomorphismI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  have intermediate: "h \<sigma> a \<in> E \<sigma>"
    by (rule paper_bbk_homomorphism_domain[OF first member])
  show "k \<sigma> (h \<sigma> a) \<in> F \<sigma>"
    by (rule paper_bbk_homomorphism_domain[OF second intermediate])
next
  fix \<sigma> A g
  assume language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  have intermediate_typed: "named_env_typed E G (paper_hom_assignment G h g)"
    by (rule paper_bbk_homomorphism_assignment_typed[OF first typed])
  have intermediate_adequate: "named_adequate (paper_hom_assignment G h g) A"
    by (rule iffD2[OF paper_hom_assignment_adequate_iff adequate])
  have first_equation: "h \<sigma> (J g A) = K (paper_hom_assignment G h g) A"
    by (rule paper_bbk_homomorphism_denote[OF first language typed adequate])
  have second_equation: "k \<sigma> (K (paper_hom_assignment G h g) A) =
    L (paper_hom_assignment G k (paper_hom_assignment G h g)) A"
    by (rule paper_bbk_homomorphism_denote[OF second language intermediate_typed intermediate_adequate])
  show "k \<sigma> (h \<sigma> (J g A)) =
    L (paper_hom_assignment G (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a)) g) A"
    by (simp only: first_equation second_equation paper_hom_assignment_compose)
qed

section \<open>The family matters only on its typed domains\<close>

text \<open>
  If hσ and kσ agree on Dσ, replacing h by k preserves the commuting
  condition PROVIDED interpreted source terms belong to their declared
  domains. That proviso is automatic for a supplied BBK model, but is
  explicit below: the raw homomorphism predicate alone does not assert
  typing of J. No equality outside Dσ is required.
\<close>

theorem paper_bbk_homomorphism_cong:
  assumes hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and source_typed: "\<And>A \<sigma> g. named_in_language paper_logical_type \<Sigma> G A \<sigma> \<Longrightarrow>
      named_env_typed D G g \<Longrightarrow> named_adequate g A \<Longrightarrow> J g A \<in> D \<sigma>"
    and agree: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a = k \<sigma> a"
  shows "paper_bbk_homomorphism \<Sigma> G D J E K k"
proof (rule paper_bbk_homomorphismI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  have image: "h \<sigma> a \<in> E \<sigma>" by (rule paper_bbk_homomorphism_domain[OF hom member])
  show "k \<sigma> a \<in> E \<sigma>" using image by (simp only: agree[OF member])
next
  fix \<sigma> A g
  assume language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  have member: "J g A \<in> D \<sigma>" by (rule source_typed[OF language typed adequate])
  have maps: "paper_hom_assignment G h g = paper_hom_assignment G k g"
    by (rule paper_hom_assignment_cong[OF typed agree])
  have equation: "h \<sigma> (J g A) = K (paper_hom_assignment G h g) A"
    by (rule paper_bbk_homomorphism_denote[OF hom language typed adequate])
  show "k \<sigma> (J g A) = K (paper_hom_assignment G k g) A"
    using equation by (simp only: agree[OF member] maps)
qed

end
