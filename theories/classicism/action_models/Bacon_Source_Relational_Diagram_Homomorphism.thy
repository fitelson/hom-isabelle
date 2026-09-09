theory Bacon_Source_Relational_Diagram_Homomorphism
  imports Bacon_Source_Relational_Diagram_Open_Denotation
    Bacon_Source_Relational_Homomorphism Bacon_Source_Relational_BBK_Constant_Pullback
    Bacon_Source_Relational_Naming_Validity
begin

section \<open>The diagram map is a homomorphism to the original-signature reduct\<close>

context paper_R_diagram_target
begin

theorem paper_R_diagram_expanded_homomorphism:
  "paper_R_bbk_homomorphism (paper_R_naming_signature \<Sigma> D) G D source.paper_R_naming_denote E K paper_R_diagram_map"
  by (rule paper_R_bbk_homomorphismI; (rule paper_R_diagram_map_typed | rule paper_R_diagram_map_open_denote); assumption)

theorem paper_R_diagram_reduct_model:
  "paper_R_bbk_model \<Sigma> G E (paper_R_constant_pullback_denote Inl K) W"
proof -
  have model: "paper_R_bbk_model (paper_R_naming_signature \<Sigma> D) G E K W" by unfold_locales
  show ?thesis
  proof (rule paper_R_bbk_constant_pullback[OF model])
    fix \<rho> c
    assume declared: "c \<in> \<Sigma> \<rho>"
    show "Inl c \<in> paper_R_naming_signature \<Sigma> D \<rho>" by (simp only: paper_R_naming_signature_old; rule declared)
  qed
qed

theorem paper_R_diagram_reduct_homomorphism:
  "paper_R_bbk_homomorphism \<Sigma> G D J E (paper_R_constant_pullback_denote Inl K) paper_R_diagram_map"
proof (rule paper_R_bbk_homomorphismI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  show "paper_R_diagram_map \<sigma> a \<in> E \<sigma>" by (rule paper_R_diagram_map_typed[OF member])
next
  fix \<sigma> A g
  assume language: "paper_R_in_language \<Sigma> G A \<sigma>" and typed: "named_env_typed D G g"
    and adequate: "named_adequate g A"
  have expanded_language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (map_named_term Inl id A) \<sigma>"
    by (rule iffD2[OF paper_R_naming_old_language_iff language])
  have expanded_adequate: "named_adequate g (map_named_term Inl id A)"
    by (rule iffD2[OF paper_R_naming_old_adequate_iff adequate])
  show "paper_R_diagram_map \<sigma> (J g A) =
      paper_R_constant_pullback_denote Inl K (paper_hom_assignment G paper_R_diagram_map g) A"
    using paper_R_diagram_map_open_denote[OF expanded_language typed expanded_adequate]
    by (simp only: source.paper_R_naming_denote_old paper_R_constant_pullback_denote_def)
qed

end

text \<open>
  Both the reduct model and its homomorphism from M are constructed from
  the supplied diagram target N⁺. The domains of N⁺ are retained.
  This is the denotation-preserving map of p.51–52 n.73; it does not
  preserve V or W, and assumes no existence or separation theorem.
\<close>

end
