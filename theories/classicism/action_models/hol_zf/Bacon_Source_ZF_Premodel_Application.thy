theory Bacon_Source_ZF_Premodel_Application
  imports Bacon_Source_ZF_Action_Premodel Bacon_Source_ZF_Graph_Application
begin

section \<open>The arrow subaction supplies actual exponential graphs\<close>

text \<open>
  If F∈Wσ→τ and z∈Wσ, then F⟨1W,z⟩ is defined and
  belongs to Wτ. Source: Definition 3.18, p.55, followed by
  Definition 3.19 and footnote 78(i), p.56.

  The proof uses the premodel's arrow-subaction INCLUSION, then
  the actual dependent function graph underlying the exponential.
  Identity supplies an admissible argument pair. Application closure
  is a conclusion, not a premodel field. No R-BBK model, term
  interpretation or interpretation-totality assumption is used.
\<close>

lemma paper_ZF_premodel_function_in_exponential:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and member: "F \<in> explode (D (Arr \<sigma> \<tau>) W)"
  shows "F \<in> explode (paper_ZF_exponential_code A source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W)"
proof -
  have subaction: "paper_subaction Obj (explode A) source target compose identity
    (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))
    (\<lambda>W. explode (paper_ZF_exponential_code A source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W))
    (paper_ZF_exponential_transport_code A source target compose (D \<sigma>))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  show ?thesis by (rule subsetD[OF paper_subaction_subset[OF subaction object] member])
qed

lemma paper_ZF_premodel_identity_pair:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and member: "z \<in> explode (D \<sigma> W)"
  shows "Elem (Opair (identity W) z) (paper_ZF_pair_code A source target (D \<sigma>) W)"
proof -
  have rooted: "paper_rooted_category Obj (explode A) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret Rooted: paper_rooted_category Obj "explode A" source target compose identity root by (rule rooted)
  have arrow: "identity W \<in> explode A" by (rule Rooted.identity_arrow[OF object])
  have origin: "source (identity W) = W" by (rule Rooted.identity_source[OF object])
  have argument: "z \<in> explode (D \<sigma> (target (identity W)))"
    by (simp only: Rooted.identity_target[OF object]; rule member)
  show ?thesis by (simp only: paper_ZF_pair_code_member; rule conjI[OF arrow conjI[OF origin argument]])
qed

theorem paper_ZF_premodel_application_info:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and function_member: "F \<in> explode (D (Arr \<sigma> \<tau>) W)" and argument: "z \<in> explode (D \<sigma> W)"
  shows "isFun F \<and> Elem (Opair (identity W) z) (Domain F) \<and>
    app F (Opair (identity W) z) \<in> explode (D \<tau> W)"
proof -
  have exponential: "F \<in> explode (paper_ZF_exponential_code A source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W)"
    by (rule paper_ZF_premodel_function_in_exponential[OF premodel object rt function_member])
  have graph: "F \<in> explode (paper_ZF_Pi (paper_ZF_pair_code A source target (D \<sigma>) W)
    (\<lambda>p. D \<tau> (target (Fst p))))"
    by (rule paper_ZF_exponential_code_graph[OF exponential])
  have graph_shape: "isFun F \<and> Domain F = paper_ZF_pair_code A source target (D \<sigma>) W"
    by (rule paper_ZF_Pi_function_graph[OF graph])
  have pair: "Elem (Opair (identity W) z) (paper_ZF_pair_code A source target (D \<sigma>) W)"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object argument])
  have pair_in_domain: "Elem (Opair (identity W) z) (Domain F)"
    by (simp only: conjunct2[OF graph_shape]; rule pair)
  have result: "Elem (app F (Opair (identity W) z)) (D \<tau> (target (Fst (Opair (identity W) z))))"
    by (rule paper_ZF_Pi_value[OF graph pair])
  have rooted: "paper_rooted_category Obj (explode A) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret Rooted: paper_rooted_category Obj "explode A" source target compose identity root by (rule rooted)
  have typed: "app F (Opair (identity W) z) \<in> explode (D \<tau> W)"
    using result by (simp only: Fst Rooted.identity_target[OF object] explode_Elem)
  show ?thesis by (rule conjI[OF conjunct1[OF graph_shape] conjI[OF pair_in_domain typed]])
qed

corollary paper_ZF_premodel_application_graph:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and function_member: "F \<in> explode (D (Arr \<sigma> \<tau>) W)" and argument: "z \<in> explode (D \<sigma> W)"
  shows "isFun F" and "Elem (Opair (identity W) z) (Domain F)"
  using paper_ZF_premodel_application_info[OF premodel object rt function_member argument] by blast+

corollary paper_ZF_premodel_application_type:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and function_member: "F \<in> explode (D (Arr \<sigma> \<tau>) W)" and argument: "z \<in> explode (D \<sigma> W)"
  shows "app F (Opair (identity W) z) \<in> explode (D \<tau> W)"
  using paper_ZF_premodel_application_info[OF premodel object rt function_member argument] by blast

corollary paper_ZF_premodel_application_Some:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and function_member: "F \<in> explode (D (Arr \<sigma> \<tau>) W)" and argument: "z \<in> explode (D \<sigma> W)"
  shows "paper_ZF_graph_apply F (Opair (identity W) z) = Some (app F (Opair (identity W) z))"
  by (rule paper_ZF_graph_apply_defined_value[
    OF paper_ZF_premodel_application_graph(1)[OF premodel object rt function_member argument]
      paper_ZF_premodel_application_graph(2)[OF premodel object rt function_member argument]])

end
