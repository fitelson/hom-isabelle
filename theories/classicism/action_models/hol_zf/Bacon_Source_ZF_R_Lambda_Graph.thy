theory Bacon_Source_ZF_R_Lambda_Graph
  imports Bacon_Source_ZF_R_Lambda_Input
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Abstraction_Application
begin

section \<open>A Lambda graph is determined by its applications on its domain\<close>

lemma paper_ZF_Lambda_from_app:
  assumes graph: "F = Lambda P b" and graph_values: "\<And>z. Elem z P \<Longrightarrow> c z = app F z"
  shows "Lambda P c = F"
proof -
  have equal: "Lambda P c = Lambda P b"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z P"
    have applied: "app F z = b z" by (simp only: graph Lambda_app[OF member])
    show "c z = b z" by (rule trans[OF graph_values[OF member] applied])
  qed
  show ?thesis by (rule trans[OF equal graph[symmetric]])
qed

section \<open>The encoded old abstraction has the required body values\<close>

text \<open>
  Apply fσ→τM(⟦λn.B⟧ᵍM) at (i,z). Its defining equation first
  transports the old abstraction to N=target(i), then applies it to
  (fσN)⁻¹(z). The old R abstraction/application lemma therefore gives
  fτN(⟦B⟧⁽ⁱold·g⁾⁽ⁿ↦⁽fσN⁾⁻¹z⁾N).
  Source: Definition 3.19, p.56, and Proposition 3.22, p.72.

  No evaluator induction hypothesis is used in this graph lemma.
  In particular, membership or total interpretation of the new λ term
  is not assumed. The graph is the actual raw arrow encoder.
\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_encoded_arrow_Lambda:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "\<exists>b. paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d =
    Lambda (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation \<sigma>)) M) b"
  by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
    paper_ZF_type_representation.select_convs paper_ZF_R_arrow_encode_def paper_ZF_encode_exponential_graph;
    rule exI; rule refl)

theorem paper_ZF_R_lambda_graph_value:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and body: "paper_R_in_language signature stock B \<tau>"
    and binder_type: "paper_R_type (stock n)" and codomain: "\<tau> \<noteq> Ind"
    and arrow: "i \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_source i)) stock g"
    and adequate: "named_adequate g (NLam n B)"
    and member: "z \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) (Encoding.coded_target i))"
  shows "app (paper_ZF_rep_encode (type_representation (Arr (stock n) \<tau>)) (Encoding.coded_source i)
      (paper_bbk_denote (Encoding.coded_source i) g (NLam n B))) (Opair i z) =
    paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target i)
      (paper_bbk_denote (Encoding.coded_target i)
        ((paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g)
          (n := Some (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n))
            (type_representation (stock n)) (Encoding.coded_target i) z))) B)"
proof -
  let ?M = "Encoding.coded_source i"
  let ?N = "Encoding.coded_target i"
  let ?X = "type_representation (stock n)"
  let ?Y = "type_representation \<tau>"
  let ?k = "paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g"
  let ?a = "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) ?X ?N z"
  have target_object: "?N \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  interpret Target: paper_R_bbk_model signature stock "paper_bbk_domain ?N" "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category target_object]])
  have abstraction: "paper_R_in_language signature stock (NLam n B) (Arr (stock n) \<tau>)"
    by (rule paper_R_abstraction_language[OF body binder_type codomain])
  have rt: "paper_R_type (Arr (stock n) \<tau>)" by (rule paper_R_language_result_type[OF abstraction])
  have hom: "paper_R_bbk_homomorphism signature stock (paper_bbk_domain ?M) (paper_bbk_denote ?M)
      (paper_bbk_domain ?N) (paper_bbk_denote ?N) (paper_arrow_map (Encoding.decode_arrow i))"
    by (rule paper_ZF_R_coded_homomorphism[OF arrow])
  have kt: "named_env_typed (paper_bbk_domain ?N) stock ?k"
    by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
  have ka: "named_adequate ?k (NLam n B)" by (rule iffD2[OF paper_hom_assignment_adequate_iff adequate])
  have child: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) ?X"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional binder_type])
  have am: "?a \<in> paper_bbk_domain ?N (stock n)"
    by (rule paper_ZF_R_type_invariant_decode_type[OF child target_object member])
  have moved_head: "paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f (Arr (stock n) \<tau>)) i
      (paper_bbk_denote ?M g (NLam n B)) = paper_bbk_denote ?N ?k (NLam n B)"
    using paper_R_bbk_homomorphism_denote[OF hom abstraction typed adequate]
    by (simp only: paper_ZF_recode_transport_def)
  have body_value: "paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
      (stock n) \<tau> (paper_bbk_denote ?N ?k (NLam n B)) ?a = paper_bbk_denote ?N (?k(n := Some ?a)) B"
    by (rule Target.paper_R_abstraction_application_denote[OF body binder_type codomain kt ka am])
  have pair: "Elem (Opair i z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain ?X) ?M)"
    using arrow member by (simp only: paper_ZF_pair_code_member; blast)
  have encoder: "paper_ZF_rep_encode (type_representation (Arr (stock n) \<tau>)) =
      paper_ZF_R_arrow_encode signature stock ArrowBound encode arrows (stock n) \<tau> ?X ?Y"
    by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs)
  show ?thesis by (simp only: encoder paper_ZF_R_arrow_encode_value[OF pair]
    paper_ZF_R_arrow_body_on[OF pair] moved_head body_value)
qed

end

end
