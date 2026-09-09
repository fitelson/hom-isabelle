theory Bacon_Source_Relational_Arrows
  imports Bacon_Source_Relational_Model_Data Bacon_Source_Typed_Arrows
begin

section \<open>Denotation-preserving arrows between specified model records\<close>

text \<open>
  An arrow has a specified source M, target N, and normalized typed
  map hσ:Mσ→Nσ. Retain precisely those maps preserving interpretation.
  Source: Bacon–Dorr §3.3, p.49, including footnote 71.
  The model records include their valuations, but no equation preserving
  valuation is imposed on h. Equality of arrow maps ignores values outside
  their source domains because those values are normalized.

  These are arrows between independently R-valid model records on a
  common carrier. The separate normalization of model records handles
  their own irrelevant interpretation/valuation extensions. No F validity
  predicate or F homomorphism theorem is used. No category
  of all models on arbitrary varying carriers is asserted here.
\<close>

type_synonym ('c,'v) paper_R_bbk_arrow =
  "(('c,'v) paper_bbk_model_data, 'v) paper_typed_arrow"

definition paper_R_bbk_arrows ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_bbk_arrows \<Sigma> G Obj = {f \<in> paper_typed_arrows Obj paper_bbk_domain.
    paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target f) (paper_arrow_map f)}"

lemma paper_R_bbk_arrows_typed:
  "f \<in> paper_R_bbk_arrows \<Sigma> G Obj \<Longrightarrow> f \<in> paper_typed_arrows Obj paper_bbk_domain"
  unfolding paper_R_bbk_arrows_def by blast

lemma paper_R_bbk_arrows_morphism:
  "f \<in> paper_R_bbk_arrows \<Sigma> G Obj \<Longrightarrow>
    paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target f) (paper_arrow_map f)"
  unfolding paper_R_bbk_arrows_def by blast

lemma paper_R_bbk_arrowsI:
  assumes typed: "f \<in> paper_typed_arrows Obj paper_bbk_domain"
    and morphism: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target f) (paper_arrow_map f)"
  shows "f \<in> paper_R_bbk_arrows \<Sigma> G Obj"
  using typed morphism unfolding paper_R_bbk_arrows_def by blast

lemma paper_R_bbk_arrows_subset:
  "paper_R_bbk_arrows \<Sigma> G Obj \<subseteq> paper_typed_arrows Obj paper_bbk_domain"
  by (rule subsetI; rule paper_R_bbk_arrows_typed; assumption)

theorem paper_R_bbk_data_morphism_normalize:
  assumes morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
  shows "paper_R_bbk_data_morphism \<Sigma> G M N (paper_typed_map_normalize (paper_bbk_domain M) h)"
proof -
  have original: "paper_R_bbk_model_morphism \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
      (paper_bbk_domain N) (paper_bbk_denote N) (paper_bbk_valuation N) h"
    using morphism unfolding paper_R_bbk_data_morphism_def by assumption
  show ?thesis unfolding paper_R_bbk_data_morphism_def
  proof (rule paper_R_bbk_model_morphism_cong[OF original])
    fix \<sigma> a
    assume rt: "paper_R_type \<sigma>" and member: "a \<in> paper_bbk_domain M \<sigma>"
    show "h \<sigma> a = paper_typed_map_normalize (paper_bbk_domain M) h \<sigma> a"
      by (rule paper_typed_map_normalize_on_domain[
        where D="paper_bbk_domain M" and \<sigma>=\<sigma> and h=h, OF member, symmetric])
  qed
qed

theorem paper_R_bbk_identity_arrow:
  assumes member: "M \<in> Obj" and valid: "paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_typed_identity paper_bbk_domain M \<in> paper_R_bbk_arrows \<Sigma> G Obj"
proof (rule paper_R_bbk_arrowsI)
  show "paper_typed_identity paper_bbk_domain M \<in> paper_typed_arrows Obj paper_bbk_domain"
    by (rule paper_typed_identity_arrow[OF member])
next
  have normalized: "paper_R_bbk_data_morphism \<Sigma> G M M
    (paper_typed_map_normalize (paper_bbk_domain M) (\<lambda>\<sigma> a. a))"
    by (rule paper_R_bbk_data_morphism_normalize[OF paper_R_bbk_data_morphism_identity[OF valid]])
  show "paper_R_bbk_data_morphism \<Sigma> G
    (paper_arrow_source (paper_typed_identity paper_bbk_domain M))
    (paper_arrow_target (paper_typed_identity paper_bbk_domain M))
    (paper_arrow_map (paper_typed_identity paper_bbk_domain M))"
    by (simp only: paper_typed_identity_def paper_typed_arrow.select_convs; rule normalized)
qed

theorem paper_R_bbk_compose_arrow:
  assumes first: "f \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    and second: "g \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    and meeting: "paper_arrow_target f = paper_arrow_source g"
  shows "paper_typed_compose paper_bbk_domain g f \<in> paper_R_bbk_arrows \<Sigma> G Obj"
proof (rule paper_R_bbk_arrowsI)
  show "paper_typed_compose paper_bbk_domain g f \<in> paper_typed_arrows Obj paper_bbk_domain"
    by (rule paper_typed_compose_arrow[
      OF paper_R_bbk_arrows_typed[OF first] paper_R_bbk_arrows_typed[OF second] meeting])
next
  have fm: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target f) (paper_arrow_map f)"
    by (rule paper_R_bbk_arrows_morphism[OF first])
  have gm: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_target f) (paper_arrow_target g) (paper_arrow_map g)"
    using paper_R_bbk_arrows_morphism[OF second] by (simp only: meeting)
  have combined: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target g)
    (\<lambda>\<sigma> a. paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a))"
    by (rule paper_R_bbk_data_morphism_compose[OF fm gm])
  have normalized: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source f) (paper_arrow_target g)
    (paper_typed_map_normalize (paper_bbk_domain (paper_arrow_source f))
      (\<lambda>\<sigma> a. paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a)))"
    by (rule paper_R_bbk_data_morphism_normalize[OF combined])
  show "paper_R_bbk_data_morphism \<Sigma> G
    (paper_arrow_source (paper_typed_compose paper_bbk_domain g f))
    (paper_arrow_target (paper_typed_compose paper_bbk_domain g f))
    (paper_arrow_map (paper_typed_compose paper_bbk_domain g f))"
    by (simp only: paper_typed_compose_def paper_typed_arrow.select_convs; rule normalized)
qed

theorem paper_R_bbk_arrow_ext:
  assumes first: "f \<in> paper_R_bbk_arrows \<Sigma> G Obj" and second: "g \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    and src: "paper_arrow_source f = paper_arrow_source g"
    and tgt: "paper_arrow_target f = paper_arrow_target g"
    and agree: "\<And>\<sigma> a. a \<in> paper_bbk_domain (paper_arrow_source f) \<sigma> \<Longrightarrow>
      paper_arrow_map f \<sigma> a = paper_arrow_map g \<sigma> a"
  shows "f = g"
  by (rule paper_typed_arrow_ext[
    OF paper_R_bbk_arrows_typed[OF first] paper_R_bbk_arrows_typed[OF second] src tgt agree])

end
