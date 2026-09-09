theory Bacon_Source_ZF_Exponential_Identity_Application
  imports Bacon_Source_ZF_Premodel_Application_Naturality
begin

section \<open>Evaluation after transport recovers every outgoing input\<close>

text \<open>
  If i:W→V, F∈Wσ→τ and a∈Vσ, then
  (iσ→τF)⟨1V,a⟩=F⟨i,a⟩. Unlike application naturality,
  a is an arbitrary target value, not necessarily iσ(b).
  This is Example 3.16's precomposition clause, used in C.5 (p.71).
\<close>

theorem paper_ZF_premodel_transport_identity_application:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)" and arrow: "i \<in> explode Ar"
    and head: "F \<in> explode (D (Arr \<sigma> \<tau>) (source i))"
    and argument: "a \<in> explode (D \<sigma> (target i))"
  shows "app (T (Arr \<sigma> \<tau>) i F) (Opair (identity (target i)) a) = app F (Opair i a)"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target i \<in> Obj" by (rule C.target_object[OF arrow])
  have subaction: "paper_subaction Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))
    (\<lambda>W. explode (paper_ZF_exponential_code Ar source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W))
    (paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  have transported: "T (Arr \<sigma> \<tau>) i F = paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>) i F"
    by (rule paper_subaction_transport[OF subaction arrow head])
  have pair: "Elem (Opair (identity (target i)) a) (paper_ZF_pair_code Ar source target (D \<sigma>) (target i))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object argument])
  show ?thesis by (simp only: transported
    paper_ZF_exponential_transport_apply[where Ar=Ar and source=source and target=target and X="D \<sigma>" and i=i, OF pair]
    C.identity_left[OF arrow])
qed

lemma paper_ZF_Pi_as_application_graph:
  assumes graph: "F \<in> explode (paper_ZF_Pi A B)"
  shows "F = Lambda A (app F)"
proof -
  have member: "Elem F (Fun A (Sum (Repl A B)))"
    using paper_ZF_Pi_graph[OF graph] by (simp only: explode_Elem)
  obtain f where shape: "F = Lambda A f" using Elem_Fun_Lambda[OF member] by blast
  show ?thesis by (simp only: shape Lambda_ext; simp add: Lambda_app)
qed

end
