theory Bacon_Source_BBK_Application_Morphism
  imports Bacon_Source_BBK_Application
begin

section \<open>Transporting an application witness\<close>

text \<open>
  If h:M→N and appᴹσ,τ(d,a)=b, then the same terms witnessing
  application in M, interpreted under h∘g in N, witness application
  with head hσ→τ(d), argument hσ(a), and result hτ(b).
  Source: Bacon–Dorr Definition 3.3, pp.45–46, and the
  homomorphism equation in §3.3, p.49.

  This first lemma transports the actual application graph. Each of
  F, A and FA has its own guarded denotation equation. Adequacy
  for FA supplies adequacy for both subterms and survives assignment
  transport. Source and target HOL carriers may differ.
\<close>

lemma paper_bbk_application_graph_morphism:
  fixes M :: "('c,'v) paper_bbk_model_data"
    and N :: "('c,'w) paper_bbk_model_data"
  assumes morphism: "paper_bbk_data_morphism \<Sigma> G M N h"
    and graph: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
  shows "paper_bbk_application_graph \<Sigma> G N \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a) (h \<tau> b)"
proof -
  have hom: "paper_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain N) (paper_bbk_denote N) h"
    by (rule paper_bbk_data_morphism_raw[OF morphism])
  obtain g F A where fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g (NApp F A)"
    and fv: "paper_bbk_denote M g F = d" and av: "paper_bbk_denote M g A = a"
    and bv: "paper_bbk_denote M g (NApp F A) = b"
    by (rule paper_bbk_application_graphE[OF graph])
  have fa: "named_adequate g F" and aa: "named_adequate g A"
    using adequate by (auto simp: named_adequate_def)
  have application: "named_in_language paper_logical_type \<Sigma> G (NApp F A) \<tau>"
    by (rule named_language_App[OF fl al])
  have image_typed: "named_env_typed (paper_bbk_domain N) G (paper_hom_assignment G h g)"
    by (rule paper_bbk_homomorphism_assignment_typed[OF hom typed])
  have image_adequate: "named_adequate (paper_hom_assignment G h g) (NApp F A)"
    by (rule iffD2[OF paper_hom_assignment_adequate_iff adequate])
  have head_eq: "h (Arr \<sigma> \<tau>) d = paper_bbk_denote N (paper_hom_assignment G h g) F"
    using paper_bbk_homomorphism_denote[OF hom fl typed fa] by (simp only: fv)
  have arg_eq: "h \<sigma> a = paper_bbk_denote N (paper_hom_assignment G h g) A"
    using paper_bbk_homomorphism_denote[OF hom al typed aa] by (simp only: av)
  have app_eq: "h \<tau> b = paper_bbk_denote N (paper_hom_assignment G h g) (NApp F A)"
    using paper_bbk_homomorphism_denote[OF hom application typed adequate] by (simp only: bv)
  show ?thesis by (rule paper_bbk_application_graphI[
    OF fl al image_typed image_adequate head_eq[symmetric] arg_eq[symmetric] app_eq[symmetric]])
qed

section \<open>Homomorphisms commute with reconstructed application\<close>

text \<open>
  For d∈Mσ→τ and a∈Mσ,
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

theorem paper_bbk_application_morphism:
  fixes M :: "('c,'v) paper_bbk_model_data"
    and N :: "('c,'w) paper_bbk_model_data"
  assumes morphism: "paper_bbk_data_morphism \<Sigma> G M N h"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and am: "a \<in> paper_bbk_domain M \<sigma>"
  shows "h \<tau> (paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a) =
    paper_bbk_application \<Sigma> G N \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a)"
proof -
  have source_valid: "paper_bbk_data_valid \<Sigma> G M"
    by (rule paper_bbk_data_morphism_source[OF morphism])
  have target_valid: "paper_bbk_data_valid \<Sigma> G N"
    by (rule paper_bbk_data_morphism_target[OF morphism])
  have hom: "paper_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
    (paper_bbk_domain N) (paper_bbk_denote N) h"
    by (rule paper_bbk_data_morphism_raw[OF morphism])
  have hd: "h (Arr \<sigma> \<tau>) d \<in> paper_bbk_domain N (Arr \<sigma> \<tau>)"
    by (rule paper_bbk_homomorphism_domain[OF hom dm])
  have ha: "h \<sigma> a \<in> paper_bbk_domain N \<sigma>"
    by (rule paper_bbk_homomorphism_domain[OF hom am])
  have chosen_source: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a
      (paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a)"
    by (rule paper_bbk_application_graph_chosen[OF source_valid dm am])
  have transported: "paper_bbk_application_graph \<Sigma> G N \<sigma> \<tau>
      (h (Arr \<sigma> \<tau>) d) (h \<sigma> a) (h \<tau> (paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a))"
    by (rule paper_bbk_application_graph_morphism[OF morphism chosen_source])
  have chosen_target: "paper_bbk_application_graph \<Sigma> G N \<sigma> \<tau>
      (h (Arr \<sigma> \<tau>) d) (h \<sigma> a)
      (paper_bbk_application \<Sigma> G N \<sigma> \<tau> (h (Arr \<sigma> \<tau>) d) (h \<sigma> a))"
    by (rule paper_bbk_application_graph_chosen[OF target_valid hd ha])
  show ?thesis by (rule paper_bbk_application_graph_unique[OF target_valid transported chosen_target])
qed

end
