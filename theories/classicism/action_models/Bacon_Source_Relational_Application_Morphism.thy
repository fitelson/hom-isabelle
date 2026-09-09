theory Bacon_Source_Relational_Application_Morphism
  imports Bacon_Source_Relational_Application Bacon_Source_Relational_Model_Morphism
begin

section \<open>Transporting an application witness\<close>

text \<open>
  If h:M→N and appᴹσ,τ(d,a)=b, then the same terms witnessing
  application in M, interpreted under h∘g in N, witness application
  with head hσ→τ(d), argument hσ(a), and result hτ(b).
  Source: Bacon–Dorr Definition 3.3, pp.45–46, and the
  homomorphism equation in §3.3, p.49.

  This first lemma transports the independent R application graph. Each of
  F, A and FA has its own guarded denotation equation. Adequacy
  for FA supplies adequacy for both subterms and survives assignment
  transport. Source and target HOL carriers may differ.
\<close>

lemma paper_R_application_graph_morphism:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and graph: "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b"
  shows "paper_R_application_graph \<Sigma> G E K \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a) (h \<tau> b)"
proof -
  have hom: "paper_R_bbk_homomorphism \<Sigma> G D J
      E K h"
    by (rule paper_R_bbk_model_morphism_raw[OF morphism])
  obtain g F A where fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g"
    and adequate: "named_adequate g (NApp F A)"
    and fv: "J g F = d" and av: "J g A = a"
    and bv: "J g (NApp F A) = b"
    by (rule paper_R_application_graphE[OF graph])
  have fa: "named_adequate g F" and aa: "named_adequate g A"
    using adequate by (auto simp: named_adequate_def)
  have application: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
    by (rule paper_R_language_App[OF fl al])
  have image_typed: "named_env_typed E G (paper_hom_assignment G h g)"
    by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
  have image_adequate: "named_adequate (paper_hom_assignment G h g) (NApp F A)"
    by (rule iffD2[OF paper_hom_assignment_adequate_iff adequate])
  have head_eq: "h (Arr \<sigma> \<tau>) d = K (paper_hom_assignment G h g) F"
    using paper_R_bbk_homomorphism_denote[OF hom fl typed fa] by (simp only: fv)
  have arg_eq: "h \<sigma> a = K (paper_hom_assignment G h g) A"
    using paper_R_bbk_homomorphism_denote[OF hom al typed aa] by (simp only: av)
  have app_eq: "h \<tau> b = K (paper_hom_assignment G h g) (NApp F A)"
    using paper_R_bbk_homomorphism_denote[OF hom application typed adequate] by (simp only: bv)
  show ?thesis by (rule paper_R_application_graphI[where J=K and D=E and g="paper_hom_assignment G h g",
    OF fl al image_typed image_adequate head_eq[symmetric] arg_eq[symmetric] app_eq[symmetric]])
qed

section \<open>Homomorphisms commute with reconstructed application\<close>

text \<open>
  For σ→τ∈R, d∈Mσ→τ and a∈Mσ,
  hτ(appᴹσ,τ(d,a))=appᴺσ,τ(hσ→τ(d),hσ(a)).
  The chosen source result belongs to its witnessed graph. Transport
  gives a target graph witness, and target graph uniqueness identifies
  it with the chosen target result. This derives application
  preservation from interpretation preservation; it does not assume
  an application field in the definition of homomorphism.

  Valuations validate the independently supplied endpoint models but
  are never equated across h (p.49, footnote 71). No Functionality,
  fullness, closed denotability or injectivity premise is used.
\<close>

theorem paper_R_application_morphism:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and dm: "d \<in> D (Arr \<sigma> \<tau>)" and am: "a \<in> D \<sigma>"
  shows "h \<tau> (paper_R_application \<Sigma> G D J \<sigma> \<tau> d a) =
    paper_R_application \<Sigma> G E K \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a)"
proof -
  interpret Source: paper_R_bbk_model \<Sigma> G D J V
    by (rule paper_R_bbk_model_morphism_source[OF morphism])
  interpret Target: paper_R_bbk_model \<Sigma> G E K W
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  have hom: "paper_R_bbk_homomorphism \<Sigma> G D J E K h"
    by (rule paper_R_bbk_model_morphism_raw[OF morphism])
  have hd: "h (Arr \<sigma> \<tau>) d \<in> E (Arr \<sigma> \<tau>)"
    by (rule paper_R_bbk_homomorphism_domain[OF hom dm])
  have ha: "h \<sigma> a \<in> E \<sigma>" by (rule paper_R_bbk_homomorphism_domain[OF hom am])
  have chosen_source: "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a
      (paper_R_application \<Sigma> G D J \<sigma> \<tau> d a)"
    by (rule Source.paper_R_application_graph_chosen[OF rt dm am])
  have transported: "paper_R_application_graph \<Sigma> G E K \<sigma> \<tau>
      (h (Arr \<sigma> \<tau>) d) (h \<sigma> a) (h \<tau> (paper_R_application \<Sigma> G D J \<sigma> \<tau> d a))"
    by (rule paper_R_application_graph_morphism[OF morphism chosen_source])
  have chosen_target: "paper_R_application_graph \<Sigma> G E K \<sigma> \<tau>
      (h (Arr \<sigma> \<tau>) d) (h \<sigma> a)
      (paper_R_application \<Sigma> G E K \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a))"
    by (rule Target.paper_R_application_graph_chosen[OF rt hd ha])
  show ?thesis by (rule Target.paper_R_application_graph_unique[OF transported chosen_target])
qed

end
