theory Bacon_Source_ZF_Premodel_Application_Naturality
  imports Bacon_Source_ZF_Premodel_Application
begin

section \<open>Canonical graph transport evaluates by precomposition\<close>

lemma paper_ZF_exponential_transport_apply:
  assumes pair: "Elem (Opair j z) (paper_ZF_pair_code Ar source target X (target i))"
  shows "app (paper_ZF_exponential_transport_code Ar source target compose X i F) (Opair j z) =
    app F (Opair (compose j i) z)"
  by (simp only: paper_ZF_exponential_transport_code_def Lambda_app[OF pair] Fst Snd)

section \<open>Application naturality follows from the arrow subaction\<close>

text \<open>
  For i:W→V, F∈Wσ→τ and a∈Wσ,
  iτ(F⟨1W,a⟩)=(iσ→τF)⟨1V,iσ(a)⟩.
  Source: Example 3.16, p.54, Definition 3.19, p.56, and the
  application step of Proposition C.1, p.70.

  First apply exponential coherence at (1W,a). Then use the
  subaction equation to replace function transport by its canonical
  graph transport, and evaluate it at (1V,iσ(a)).
  Only a generic premodel and the displayed typed values are assumed.
  This is not unqualified naturality of every partially defined term;
  there is no action-model, BBK-model or C-theorem premise.
\<close>

theorem paper_ZF_premodel_application_naturality:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)" and arrow: "i \<in> explode Ar"
    and head: "F \<in> explode (D (Arr \<sigma> \<tau>) (source i))"
    and argument: "a \<in> explode (D \<sigma> (source i))"
  shows "T \<tau> i (app F (Opair (identity (source i)) a)) =
    app (T (Arr \<sigma> \<tau>) i F) (Opair (identity (target i)) (T \<sigma> i a))"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by (rule conjunct1)
  interpret Category: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have source_object: "source i \<in> Obj" by (rule Category.source_object[OF arrow])
  have target_object: "target i \<in> Obj" by (rule Category.target_object[OF arrow])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  have sigma_action: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<sigma> W)) (T \<sigma>)"
    using premodel sr unfolding paper_ZF_action_premodel_def by blast
  interpret Sigma: paper_action Obj "explode Ar" source target compose identity "\<lambda>W. explode (D \<sigma> W)" "T \<sigma>"
    by (rule sigma_action)
  have moved_argument: "T \<sigma> i a \<in> explode (D \<sigma> (target i))"
    by (rule Sigma.transport_type[OF arrow argument])
  have exponential: "F \<in> explode (paper_ZF_exponential_code Ar source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) (source i))"
    by (rule paper_ZF_premodel_function_in_exponential[OF premodel source_object rt head])
  have source_identity: "identity (source i) \<in> explode Ar" by (rule Category.identity_arrow[OF source_object])
  have identity_source: "source (identity (source i)) = source i" by (rule Category.identity_source[OF source_object])
  have identity_target: "target (identity (source i)) = source i" by (rule Category.identity_target[OF source_object])
  have source_argument: "a \<in> explode (D \<sigma> (target (identity (source i))))"
    by (simp only: identity_target; rule argument)
  have coherent: "T \<tau> i (app F (Opair (identity (source i)) a)) =
    app F (Opair (compose i (identity (source i))) (T \<sigma> i a))"
    by (rule paper_ZF_exponential_code_coherent[
      OF exponential source_identity identity_source arrow identity_target source_argument])
  have left_value: "T \<tau> i (app F (Opair (identity (source i)) a)) = app F (Opair i (T \<sigma> i a))"
    using coherent by (simp only: Category.identity_right[OF arrow])
  have subaction: "paper_subaction Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))
    (\<lambda>W. explode (paper_ZF_exponential_code Ar source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W))
    (paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>))"
    using premodel rt unfolding paper_ZF_action_premodel_def by blast
  have function_transport: "T (Arr \<sigma> \<tau>) i F = paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>) i F"
    by (rule paper_subaction_transport[OF subaction arrow head])
  have target_pair: "Elem (Opair (identity (target i)) (T \<sigma> i a))
    (paper_ZF_pair_code Ar source target (D \<sigma>) (target i))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel target_object moved_argument])
  have right_value: "app (T (Arr \<sigma> \<tau>) i F) (Opair (identity (target i)) (T \<sigma> i a)) =
    app F (Opair i (T \<sigma> i a))"
    by (simp only: function_transport
      paper_ZF_exponential_transport_apply[where Ar=Ar and source=source and target=target and X="D \<sigma>" and i=i,
        OF target_pair] Category.identity_left[OF arrow])
  show ?thesis by (rule trans[OF left_value right_value[symmetric]])
qed

end
