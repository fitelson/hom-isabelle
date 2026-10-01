theory Typed_Paper_Model
  imports Typed_Paper_Evaluation Typed_Paper_Primitives_Complete
    "Bacon_Source_Vocabulary_Development.Bacon_Source_Rich_Stock"
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Action_Classicism_Soundness"
begin

section \<open>The concrete data satisfy paper Definition 3.20\<close>

theorem concrete_paper_action_model:
  assumes rich: "paper_R_rich G"
  shows "paper_ZF_action_model S G (explode raw_W) pa_Ar Fst Snd pa_compose pa_id raw_root
    paper_D paper_T paper_I"
proof (rule pt_action_model_from_primitives[where V=src_primitive, OF rich])
  show "\<And>l. Elem (src_primitive l) (src_D (paper_logical_type l) raw_root)"
    by (rule src_primitive_type)
  fix w l
  assume ww: "Elem w raw_W" and "paper_R_type (paper_logical_type l)"
  show "paper_enc (paper_logical_type l) w
      (src_T (paper_logical_type l) raw_root w (src_primitive l)) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
    by (rule paper_primitive_identification[OF ww])
qed

theorem concrete_paper_standard_model:
  "paper_ZF_action_model S sg_standard_stock (explode raw_W) pa_Ar Fst Snd
    pa_compose pa_id raw_root paper_D paper_T paper_I"
  by (rule concrete_paper_action_model, rule paper_R_rich_from_F,
    rule sg_standard_stock_rich)

theorem concrete_paper_classicism_truth:
  assumes derivation: "paper_R_classicism_proves S sg_standard_stock A"
    and arrow: "Elem h pa_Ar" and origin: "Fst h = raw_root"
    and env: "paper_ZF_action_env_typed paper_D sg_standard_stock (Snd h) g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_action_holds pa_Ar Fst Snd pa_compose pa_id paper_D paper_T paper_I
    sg_standard_stock h g A"
  by (rule paper_ZF_action_classicism_truth[OF concrete_paper_standard_model
        derivation _ origin env adequate])
    (simp only: explode_Elem arrow)

theorem concrete_paper_term_totality:
  assumes language: "paper_R_in_language S G A a"
    and arrow: "Elem h pa_Ar" and origin: "Fst h = raw_root"
    and env: "paper_ZF_action_env_typed paper_D G (Snd h) g"
    and adequate: "named_adequate g A"
  shows "\<exists>v. paper_ZF_action_eval pa_Ar Fst Snd pa_compose pa_id
    paper_D paper_T paper_I G A h g = Some v \<and> v \<in> explode (paper_D a (Snd h))"
proof (rule pt_totality_from_primitives[where V=src_primitive,
    OF src_primitive_type _ language arrow origin env adequate])
  fix w l
  assume ww: "Elem w raw_W" and "paper_R_type (paper_logical_type l)"
  show "paper_enc (paper_logical_type l) w
      (src_T (paper_logical_type l) raw_root w (src_primitive l)) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
    by (rule paper_primitive_identification[OF ww])
qed

text \<open>The only antecedent of the model theorem is the source
  language's rich relational variable stock. The category, nonempty
  individual domains, proposition and function subactions, six literal
  primitive operations, and total typed partial interpretation are all
  constructed, not assumed. The separate term-totality theorem does not
  need richness. Neither endpoint by itself establishes the intended
  Boolean Completeness, Atomicity, BF, or failed Rigid Comprehension
  formulas: their exact source interpretations remain separate proof
  obligations.\<close>

ML \<open>
  val facts = [@{thm concrete_paper_action_model}, @{thm concrete_paper_standard_model},
    @{thm concrete_paper_classicism_truth}, @{thm concrete_paper_term_totality}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "PAPER-MODEL: concrete Definition 3.20 action model and totality; source axiom/counterexample truth remains separate";
\<close>

end
