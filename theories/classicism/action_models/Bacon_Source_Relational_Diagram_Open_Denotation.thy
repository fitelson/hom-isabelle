theory Bacon_Source_Relational_Diagram_Open_Denotation
  imports Bacon_Source_Relational_Diagram_Application
begin

section \<open>The diagram map commutes with every open R expression\<close>

text \<open>
  Induct on the finite number of free variables, not on syntax size.
  At a nonindividual result, abstract one free variable and apply the
  induction hypothesis to that smaller free-variable set. The already
  proved all-value application equation and the two scalar abstraction
  equations recover the open expression. At result e the grammar allows
  only variables and constants; no abstraction returning e is formed.

  This derives the full denotation condition of §3.3 p.49 from the
  closed positive diagram, as required in p.51–52 n.73. The target
  interpretation of a value name is hσ(a), not generally a itself.
  No truth preservation or homomorphism premise is used in this proof.
\<close>

context paper_R_diagram_target
begin

theorem paper_R_diagram_map_open_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  shows "paper_R_diagram_map \<sigma> (source.paper_R_naming_denote g A) =
    K (paper_hom_assignment G paper_R_diagram_map g) A"
proof -
  interpret Expanded: paper_R_bbk_model "paper_R_naming_signature \<Sigma> D" G D source.paper_R_naming_denote V
    by (rule source.paper_R_naming_model)
  show ?thesis using language typed adequate
  proof (induction A arbitrary: \<sigma> g rule: measure_induct_rule[where f="\<lambda>A. card (named_fv A)"])
    case (less A)
    let ?h = "paper_hom_assignment G paper_R_diagram_map g"
    have ht: "named_env_typed E G ?h" by (rule paper_R_diagram_assignment_typed[OF less.prems(2)])
    have ha: "named_adequate ?h A" by (rule iffD2[OF paper_hom_assignment_adequate_iff less.prems(3)])
    show ?case
    proof (cases "named_fv A = {}")
      case True
      have source_value: "source.paper_R_naming_denote g A = source.paper_R_naming_denote Map.empty A"
        by (rule Expanded.paper_R_closed_denote_empty[OF less.prems(1) True less.prems(2)])
      have target_value: "K ?h A = K Map.empty A"
        by (rule target.paper_R_closed_denote_empty[OF less.prems(1) True ht])
      show ?thesis by (simp only: source_value target_value;
        rule paper_R_diagram_map_closed_denote[OF less.prems(1) True])
    next
      case False
      note open_term = False
      show ?thesis
      proof (cases "\<sigma> = Ind")
        case True
        have individual: "paper_R_has_type G A Ind"
          using less.prems(1) True unfolding paper_R_in_language_def by blast
        obtain n where shape: "A = NVar n" and nt: "G n = Ind"
          using paper_R_individual_term_shape[OF individual] open_term by auto
        have covered: "n \<in> dom g" using less.prems(3) by (simp add: named_adequate_def shape)
        obtain a where assigned: "g n = Some a" using covered by (cases "g n") auto
        have source_value: "source.paper_R_naming_denote g (NVar n) = a"
          by (rule source.paper_R_naming_denote_var[OF less.prems(2) assigned])
        have image_assigned: "?h n = Some (paper_R_diagram_map (G n) a)"
          by (rule paper_hom_assignment_Some[where G=G and h=paper_R_diagram_map and g=g and n=n, OF assigned])
        have target_value: "K ?h (NVar n) = paper_R_diagram_map (G n) a"
          by (rule target.denote_var[OF ht image_assigned])
        show ?thesis by (simp only: shape source_value target_value True nt)
      next
        case False
        note nonindividual = False
        obtain n where free: "n \<in> named_fv A" using open_term by blast
        obtain a where assigned: "g n = Some a" by (rule named_adequate_value[OF less.prems(3) free])
        have member: "a \<in> D (G n)" by (rule named_env_value[OF less.prems(2) assigned])
        have nt: "paper_R_type (G n)" by (rule paper_R_language_fv_type[OF less.prems(1) free])
        have abstraction: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (NLam n A) (Arr (G n) \<sigma>)"
          by (rule paper_R_abstraction_language[OF less.prems(1) nt nonindividual])
        have ga: "named_adequate g (NLam n A)" using less.prems(3) unfolding named_adequate_def by auto
        have hla: "named_adequate ?h (NLam n A)" by (rule iffD2[OF paper_hom_assignment_adequate_iff ga])
        have smaller: "card (named_fv (NLam n A)) < card (named_fv A)"
          by (simp only: named_fv.simps; rule card_Diff1_less[OF named_fv_finite free])
        have abstract_map: "paper_R_diagram_map (Arr (G n) \<sigma>) (source.paper_R_naming_denote g (NLam n A)) =
            K ?h (NLam n A)"
          by (rule less.IH[OF smaller abstraction less.prems(2) ga])
        have head_member: "source.paper_R_naming_denote g (NLam n A) \<in> D (Arr (G n) \<sigma>)"
          by (rule Expanded.denote_type[OF abstraction less.prems(2) ga])
        have image_member: "paper_R_diagram_map (G n) a \<in> E (G n)"
          by (rule paper_R_diagram_map_typed[OF member])
        have source_update: "g(n := Some a) = g" by (rule fun_upd_idem[where f=g and x=n, OF assigned])
        have image_assigned: "?h n = Some (paper_R_diagram_map (G n) a)"
          by (rule paper_hom_assignment_Some[where G=G and h=paper_R_diagram_map and g=g and n=n, OF assigned])
        have target_update: "?h(n := Some (paper_R_diagram_map (G n) a)) = ?h"
          by (rule fun_upd_idem[where f="?h" and x=n, OF image_assigned])
        have source_application: "paper_R_application (paper_R_naming_signature \<Sigma> D) G D
            source.paper_R_naming_denote (G n) \<sigma> (source.paper_R_naming_denote g (NLam n A)) a =
            source.paper_R_naming_denote g A"
          using Expanded.paper_R_abstraction_application_denote[OF less.prems(1) nt nonindividual less.prems(2) ga member]
          by (simp only: source_update)
        have target_application: "paper_R_application (paper_R_naming_signature \<Sigma> D) G E K (G n) \<sigma>
            (K ?h (NLam n A)) (paper_R_diagram_map (G n) a) = K ?h A"
          using target.paper_R_abstraction_application_denote[OF less.prems(1) nt nonindividual ht hla image_member]
          by (simp only: target_update)
        show ?thesis using paper_R_diagram_map_application[OF head_member member]
          by (simp only: source_application abstract_map target_application)
      qed
    qed
  qed
qed

end

end
