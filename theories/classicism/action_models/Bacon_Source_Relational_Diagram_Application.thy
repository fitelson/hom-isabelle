theory Bacon_Source_Relational_Diagram_Application
  imports Bacon_Source_Relational_Diagram_Mapping Bacon_Source_Homomorphism_Assignments
begin

section \<open>The diagram map preserves actual application on all typed values\<close>

text \<open>
  Apply the closed-expression diagram equation to name(d) name(a).
  The names denote d and a in M⁺ and h(d) and h(a) in N⁺.
  Thus application preservation is derived before any open-expression
  homomorphism theorem is used. Source: p.51–52 n.73 and §3.3 p.49.
\<close>

context paper_R_diagram_target
begin

lemma paper_R_diagram_assignment_typed:
  assumes typed: "named_env_typed D G g"
  shows "named_env_typed E G (paper_hom_assignment G paper_R_diagram_map g)"
  by (rule paper_hom_assignment_typed[where D=D and E=E,
    OF paper_R_diagram_map_typed typed])

theorem paper_R_diagram_map_application:
  assumes head: "d \<in> D (Arr \<sigma> \<tau>)" and argument: "a \<in> D \<sigma>"
  shows "paper_R_diagram_map \<tau>
      (paper_R_application (paper_R_naming_signature \<Sigma> D) G D source.paper_R_naming_denote \<sigma> \<tau> d a) =
    paper_R_application (paper_R_naming_signature \<Sigma> D) G E K \<sigma> \<tau>
      (paper_R_diagram_map (Arr \<sigma> \<tau>) d) (paper_R_diagram_map \<sigma> a)"
proof -
  interpret Expanded: paper_R_bbk_model "paper_R_naming_signature \<Sigma> D" G D source.paper_R_naming_denote V
    by (rule source.paper_R_naming_model)
  let ?F = "NConst (Inr d) (Arr \<sigma> \<tau>) :: ('c + 'v) paper_named_term"
  let ?A = "NConst (Inr a) \<sigma> :: ('c + 'v) paper_named_term"
  have fl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?F (Arr \<sigma> \<tau>)"
    by (rule paper_R_diagram_value_name_language[OF head])
  have al: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?A \<sigma>"
    by (rule paper_R_diagram_value_name_language[OF argument])
  have application: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (NApp ?F ?A) \<tau>"
    by (rule paper_R_language_App[OF fl al])
  have closed: "named_fv (NApp ?F ?A) = {}" by simp
  have source_empty: "named_env_typed D G Map.empty" and target_empty: "named_env_typed E G Map.empty"
    by (simp_all add: named_env_typed_def)
  have source_adequate: "named_adequate (Map.empty :: 'v named_assignment) (NApp ?F ?A)"
    and target_adequate: "named_adequate (Map.empty :: 'w named_assignment) (NApp ?F ?A)"
    by (simp_all add: named_adequate_def)
  have source_head: "source.paper_R_naming_denote Map.empty ?F = d"
    by (rule source.paper_R_naming_denote_value_constant[OF head source_empty])
  have source_argument: "source.paper_R_naming_denote Map.empty ?A = a"
    by (rule source.paper_R_naming_denote_value_constant[OF argument source_empty])
  have source_application: "paper_R_application (paper_R_naming_signature \<Sigma> D) G D
      source.paper_R_naming_denote \<sigma> \<tau> d a = source.paper_R_naming_denote Map.empty (NApp ?F ?A)"
    using Expanded.paper_R_application_denote[OF fl al source_empty source_adequate]
    by (simp only: source_head source_argument)
  have target_application: "paper_R_application (paper_R_naming_signature \<Sigma> D) G E K \<sigma> \<tau>
      (paper_R_diagram_map (Arr \<sigma> \<tau>) d) (paper_R_diagram_map \<sigma> a) = K Map.empty (NApp ?F ?A)"
    using target.paper_R_application_denote[OF fl al target_empty target_adequate]
    by (simp only: paper_R_diagram_map_def)
  show ?thesis by (simp only: source_application target_application;
    rule paper_R_diagram_map_closed_denote[OF application closed])
qed

end

end
