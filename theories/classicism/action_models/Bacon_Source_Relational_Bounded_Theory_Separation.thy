theory Bacon_Source_Relational_Bounded_Theory_Separation
  imports Bacon_Source_Relational_Bounded_Theory_Models
    Bacon_Source_Relational_Normalization_Morphisms Bacon_Source_Relational_Naming_Bounded_Separation
begin

section \<open>Represent an actual homomorphism by a normalized arrow\<close>

lemma paper_R_bounded_theory_arrow_from_homomorphism:
  assumes source: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    and target: "N \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    and hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain N) (paper_bbk_denote N) h"
  obtains r where "r \<in> paper_R_bounded_theory_arrows \<Sigma> G U T"
    and "paper_arrow_source r = M" and "paper_arrow_target r = N"
    and "\<And>\<sigma> a. a \<in> paper_bbk_domain M \<sigma> \<Longrightarrow> paper_arrow_map r \<sigma> a = h \<sigma> a"
proof -
  note finish = that
  let ?Obj = "paper_R_bounded_theory_models \<Sigma> G U T"
  let ?k = "paper_typed_map_normalize (paper_bbk_domain M) h"
  let ?r = "\<lparr>paper_arrow_source = M, paper_arrow_target = N, paper_arrow_map = ?k\<rparr>"
  have source_valid: "paper_R_bbk_data_valid \<Sigma> G M" by (rule paper_R_bounded_theory_models_valid[OF source])
  have target_valid: "paper_R_bbk_data_valid \<Sigma> G N" by (rule paper_R_bounded_theory_models_valid[OF target])
  have morphism: "paper_R_bbk_data_morphism \<Sigma> G M N h"
    unfolding paper_R_bbk_data_morphism_def
    by (rule paper_R_bbk_model_morphismI[OF paper_R_bbk_data_model[OF source_valid]
      paper_R_bbk_data_model[OF target_valid] hom])
  have normalized: "paper_R_bbk_data_morphism \<Sigma> G M N ?k"
    by (rule paper_R_bbk_data_morphism_normalize[OF morphism])
  have raw_normalized: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain N) (paper_bbk_denote N) ?k"
    by (rule paper_R_bbk_data_morphism_raw[OF normalized])
  have typed_arrow: "?r \<in> paper_typed_arrows ?Obj paper_bbk_domain"
  proof (rule paper_typed_arrowsI)
    show "paper_arrow_source ?r \<in> ?Obj" by (simp only: paper_typed_arrow.select_convs; rule source)
  next
    show "paper_arrow_target ?r \<in> ?Obj" by (simp only: paper_typed_arrow.select_convs; rule target)
  next
    fix \<sigma> a
    assume member: "a \<in> paper_bbk_domain (paper_arrow_source ?r) \<sigma>"
    have source_member: "a \<in> paper_bbk_domain M \<sigma>" using member by simp
    show "paper_arrow_map ?r \<sigma> a \<in> paper_bbk_domain (paper_arrow_target ?r) \<sigma>"
      by (simp only: paper_typed_arrow.select_convs; rule paper_R_bbk_homomorphism_domain[OF raw_normalized source_member])
  next
    show "paper_typed_map_normal (paper_bbk_domain (paper_arrow_source ?r)) (paper_arrow_map ?r)"
      by (simp only: paper_typed_arrow.select_convs; rule paper_typed_map_normalize_normal)
  qed
  have arrow: "?r \<in> paper_R_bounded_theory_arrows \<Sigma> G U T"
    unfolding paper_R_bounded_theory_arrows_def
    by (rule paper_R_bbk_arrowsI[OF typed_arrow]; simp only: paper_typed_arrow.select_convs; rule normalized)
  have src: "paper_arrow_source ?r = M" and tgt: "paper_arrow_target ?r = N" by simp_all
  have on_domain: "paper_arrow_map ?r \<sigma> a = h \<sigma> a" if "a \<in> paper_bbk_domain M \<sigma>" for \<sigma> a
    by (simp only: paper_typed_arrow.select_convs;
      rule paper_typed_map_normalize_on_domain[where D="paper_bbk_domain M" and h=h and \<sigma>=\<sigma>, OF that])
  show thesis by (rule finish[OF arrow src tgt on_domain])
qed

section \<open>Every distinct propositional pair has a separating outgoing arrow\<close>

theorem paper_R_bounded_theory_separating_arrow:
  fixes U :: "'v set" and M :: "('c,'v) paper_bbk_model_data"
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and theory_h: "paper_R_H_theory \<Sigma> G T" and pe: "paper_R_PE_closed \<Sigma> G T"
    and object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    and pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  obtains r where "r \<in> paper_R_bounded_theory_arrows \<Sigma> G U T" and "paper_arrow_source r = M"
    and "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
proof -
  note finish = that
  have source_valid: "paper_R_bbk_data_valid \<Sigma> G M" by (rule paper_R_bounded_theory_models_valid[OF object])
  interpret Source: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF source_valid])
  have source_bound: "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
    by (rule paper_R_bounded_theory_models_bound[OF object])
  have parameters: "card_of (\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<le>o card_of U"
    by (rule card_of_mono1[OF source_bound])
  have source_truth: "\<forall>A\<in>T. Source.paper_R_valid A"
    by (intro ballI; rule paper_R_bounded_theory_models_truth[OF object]; assumption)
  obtain E :: "otype \<Rightarrow> 'v set" and L W h
    where model: "paper_R_bbk_model \<Sigma> G E L W" and bound: "(\<Union>\<sigma>. E \<sigma>) \<subseteq> U"
    and target_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G E L W A"
    and hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) E L h"
    and separated: "W (h Prop p) \<noteq> W (h Prop q)"
    using Source.paper_R_naming_bounded_proposition_separation[
      OF infinite names parameters theory_h pe source_truth pm qm different] by blast
  let ?Raw = "\<lparr>paper_bbk_domain = E, paper_bbk_denote = L, paper_bbk_valuation = W\<rparr> :: ('c,'v) paper_bbk_model_data"
  let ?N = "paper_R_bbk_normalize \<Sigma> G ?Raw"
  have raw_valid: "paper_R_bbk_data_valid \<Sigma> G ?Raw" using model by (simp add: paper_R_bbk_data_valid_def)
  have raw_bound: "(\<Union>\<sigma>. paper_bbk_domain ?Raw \<sigma>) \<subseteq> U" using bound by simp
  have raw_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain ?Raw) (paper_bbk_denote ?Raw) (paper_bbk_valuation ?Raw) A"
    using target_truth by simp
  have target: "?N \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    by (rule paper_R_bounded_theory_models_normalize[OF raw_valid raw_bound raw_truth])
  have raw_hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain ?Raw) (paper_bbk_denote ?Raw) h" using hom by simp
  have normalized_hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain ?N) (paper_bbk_denote ?N) h"
    by (rule paper_R_bbk_homomorphism_normalize_target[OF raw_hom])
  have hp: "h Prop p \<in> paper_bbk_domain ?Raw Prop" by (rule paper_R_bbk_homomorphism_domain[OF raw_hom pm])
  have hq: "h Prop q \<in> paper_bbk_domain ?Raw Prop" by (rule paper_R_bbk_homomorphism_domain[OF raw_hom qm])
  have vp: "paper_bbk_valuation ?N (h Prop p) = W (h Prop p)"
    using paper_R_bbk_normalize_valuation[where \<Sigma>=\<Sigma> and G=G and M="?Raw", OF hp] by simp
  have vq: "paper_bbk_valuation ?N (h Prop q) = W (h Prop q)"
    using paper_R_bbk_normalize_valuation[where \<Sigma>=\<Sigma> and G=G and M="?Raw", OF hq] by simp
  obtain r where arrow: "r \<in> paper_R_bounded_theory_arrows \<Sigma> G U T" and src: "paper_arrow_source r = M"
    and tgt: "paper_arrow_target r = ?N"
    and on_domain: "\<And>\<sigma> a. a \<in> paper_bbk_domain M \<sigma> \<Longrightarrow> paper_arrow_map r \<sigma> a = h \<sigma> a"
    by (rule paper_R_bounded_theory_arrow_from_homomorphism[OF object target normalized_hom];
      rule that; assumption)
  have distinct_truth: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
    by (simp only: tgt on_domain[OF pm] on_domain[OF qm] vp vq; rule separated)
  show thesis by (rule finish[OF arrow src distinct_truth])
qed

text \<open>
  The target record is normalized only after constructing an actual
  bounded separating model. Its truth values at h(p),h(q) are unchanged
  because these lie in its propositional domain. The arrow's map is then
  normalized only outside the source domains. Both normalizations are
  accounted for explicitly; valuation preservation along the arrow is
  never required. Source: Definition 3.11 and pp.51–52 n.73.
\<close>

end
