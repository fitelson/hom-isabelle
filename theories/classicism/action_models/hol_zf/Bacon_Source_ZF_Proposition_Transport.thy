theory Bacon_Source_ZF_Proposition_Transport
  imports Bacon_Source_ZF_Action_Premodel
begin

section \<open>Proposition values are subsets of outgoing arrows\<close>

lemma paper_ZF_premodel_proposition_subaction:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
  shows "paper_subaction Obj (explode Ar) source target compose identity
    (\<lambda>W. explode (D Prop W)) (T Prop)
    (\<lambda>W. explode (paper_ZF_powerset_code Ar source W))
    (paper_ZF_powerset_transport_code Ar source target compose)"
  using premodel unfolding paper_ZF_action_premodel_def by blast

lemma paper_ZF_premodel_proposition_member:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and proposition_member: "p \<in> explode (D Prop W)"
    and member: "Elem i p"
  shows "i \<in> explode Ar \<and> source i = W"
proof -
  have subset: "explode (D Prop W) \<subseteq> explode (paper_ZF_powerset_code Ar source W)"
    by (rule paper_subaction_subset[OF paper_ZF_premodel_proposition_subaction[OF premodel] object])
  have powerset_member: "p \<in> explode (paper_ZF_powerset_code Ar source W)"
    using subset proposition_member by blast
  have bounded: "explode p \<subseteq> explode (paper_ZF_outgoing_code Ar source W)"
    using paper_ZF_decode_powerset_type[OF powerset_member]
    by (simp only: paper_ZF_powerset_generic_fiber Pow_iff)
  have in_value: "i \<in> explode p" using member by (simp only: explode_Elem)
  have in_outgoing: "i \<in> explode (paper_ZF_outgoing_code Ar source W)"
    using bounded in_value by blast
  have outgoing: "Elem i (paper_ZF_outgoing_code Ar source W)"
    using in_outgoing by (simp only: explode_Elem)
  show ?thesis using outgoing by (simp only: paper_ZF_outgoing_code_member)
qed

section \<open>Identity truth after transport is original arrow membership\<close>

text \<open>
  For p∈Wt and i:W→V, 1V∈it(p) iff i∈p. This is the
  powerset precomposition law, restricted to the selected proposition
  subaction. Source: Examples 3.15 and Definition 3.18, pp.54–55;
  this is the separating test used in C.7, p.71.
  No term interpretation or action-model totality is required here.
\<close>

lemma paper_ZF_premodel_proposition_transport_test:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and arrow: "i \<in> explode Ar" and member: "p \<in> explode (D Prop (source i))"
  shows "Elem (identity (target i)) (T Prop i p) \<longleftrightarrow> Elem i p"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target i \<in> Obj" by (rule Cat.target_object[OF arrow])
  have identity_arrow: "identity (target i) \<in> explode Ar" by (rule Cat.identity_arrow[OF object])
  have identity_source: "source (identity (target i)) = target i" by (rule Cat.identity_source[OF object])
  have transport: "T Prop i p = paper_ZF_powerset_transport_code Ar source target compose i p"
    by (rule paper_subaction_transport[OF paper_ZF_premodel_proposition_subaction[OF premodel] arrow member])
  show ?thesis
    by (simp only: transport paper_ZF_powerset_transport_code_def Sep paper_ZF_outgoing_code_member
      identity_arrow identity_source Cat.identity_left[OF arrow]; simp)
qed

end
