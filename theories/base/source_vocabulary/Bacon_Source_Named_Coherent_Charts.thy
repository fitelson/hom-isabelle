theory Bacon_Source_Named_Coherent_Charts
  imports Bacon_Source_Named_Charts Bacon_Source_Variable_Embedding
    "HOL-Library.Countable_Set"
begin

section \<open>A coherent typed name for each type and slot index\<close>

text \<open>
  Choose e(σ,i) with G(e(σ,i)) = σ, injectively in the pair (σ,i).
  A chart for Γ then names slot i by e(Γᵢ,i). Two frames agreeing on
  the type of a used slot give that slot the same name, even when their
  unused slots have different types.
  Source role: the infinite typed variable stock of Bacon–Dorr §1.1, p.5.

  Isabelle representation. Each fiber {n | G(n) = σ} is an infinite
  subset of nat and hence has a library enumeration without repetitions.
  Fibers of different types are disjoint by the definition of G, not by
  any assumption about semantic domains. Only variable identifiers are
  enumerated; the nonlogical-name carrier remains arbitrary.

  Status. Pure typed charts and supported name agreement, without
  assignments, denotations, or a model premise. In particular, no frame
  or environment is assumed to type the unused slots of another frame.
\<close>

definition named_typed_supply :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat \<Rightarrow> nat" where
  "named_typed_supply G \<sigma> i = from_nat_into {n. G n = \<sigma>} i"

lemma named_typed_supply_type:
  assumes rich: "sg_rich G"
  shows "G (named_typed_supply G \<sigma> i) = \<sigma>"
proof -
  have fiber_countable: "countable {n. G n = \<sigma>}" by (rule countableI_type)
  have fiber_infinite: "infinite {n. G n = \<sigma>}" by (rule sg_rich_type_fiber[OF rich])
  have enumeration: "bij_betw (from_nat_into {n. G n = \<sigma>}) UNIV {n. G n = \<sigma>}"
    by (rule bij_betw_from_nat_into[OF fiber_countable fiber_infinite])
  have member: "from_nat_into {n. G n = \<sigma>} i \<in> {n. G n = \<sigma>}"
    by (rule bij_betw_apply[OF enumeration UNIV_I])
  show ?thesis using member by (simp only: named_typed_supply_def mem_Collect_eq)
qed

lemma named_typed_supply_same_type_inj:
  assumes rich: "sg_rich G"
  shows "named_typed_supply G \<sigma> i = named_typed_supply G \<sigma> j \<longleftrightarrow> i = j"
  unfolding named_typed_supply_def
  by (rule from_nat_into_inj_infinite[OF countableI_type sg_rich_type_fiber[OF rich]])

theorem named_typed_supply_eq_iff:
  assumes rich: "sg_rich G"
  shows "named_typed_supply G \<sigma> i = named_typed_supply G \<tau> j \<longleftrightarrow>
    \<sigma> = \<tau> \<and> i = j"
proof
  assume equal: "named_typed_supply G \<sigma> i = named_typed_supply G \<tau> j"
  have typed_equal: "G (named_typed_supply G \<sigma> i) = G (named_typed_supply G \<tau> j)"
    by (rule arg_cong[where f=G, OF equal])
  have types: "\<sigma> = \<tau>" using typed_equal by (simp only: named_typed_supply_type[OF rich])
  have same_fiber: "named_typed_supply G \<sigma> i = named_typed_supply G \<sigma> j"
    using equal by (simp only: types)
  have indices: "i = j" by (rule iffD1[OF named_typed_supply_same_type_inj[OF rich] same_fiber])
  show "\<sigma> = \<tau> \<and> i = j" by (rule conjI[OF types indices])
next
  assume equal: "\<sigma> = \<tau> \<and> i = j"
  then show "named_typed_supply G \<sigma> i = named_typed_supply G \<tau> j" by simp
qed

definition named_coherent_chart :: "sgcontext \<Rightarrow> ctx \<Rightarrow> nat list" where
  "named_coherent_chart G \<Gamma> = map (\<lambda>i. named_typed_supply G (\<Gamma> ! i) i) [0..<length \<Gamma>]"

lemma named_coherent_chart_length:
  "length (named_coherent_chart G \<Gamma>) = length \<Gamma>"
  by (simp add: named_coherent_chart_def)

lemma named_coherent_chart_nth:
  assumes bound: "i < length \<Gamma>"
  shows "named_coherent_chart G \<Gamma> ! i = named_typed_supply G (\<Gamma> ! i) i"
  using bound by (simp add: named_coherent_chart_def)

theorem named_coherent_chart_valid:
  assumes rich: "sg_rich G"
  shows "named_chart G \<Gamma> (named_coherent_chart G \<Gamma>)"
proof -
  have injective: "inj_on (\<lambda>i. named_typed_supply G (\<Gamma> ! i) i) (set [0..<length \<Gamma>])"
  proof (rule inj_onI)
    fix i j
    assume ib: "i \<in> set [0..<length \<Gamma>]" and jb: "j \<in> set [0..<length \<Gamma>]"
      and equal: "named_typed_supply G (\<Gamma> ! i) i = named_typed_supply G (\<Gamma> ! j) j"
    have both: "\<Gamma> ! i = \<Gamma> ! j \<and> i = j"
      by (rule iffD1[OF named_typed_supply_eq_iff[OF rich] equal])
    show "i = j" by (rule conjunct2[OF both])
  qed
  have distinct: "distinct (named_coherent_chart G \<Gamma>)"
    using injective by (simp add: named_coherent_chart_def distinct_map)
  have types: "list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) (named_coherent_chart G \<Gamma>) \<Gamma>"
  proof (unfold list_all2_conv_all_nth, rule conjI)
    show "length (named_coherent_chart G \<Gamma>) = length \<Gamma>"
      by (rule named_coherent_chart_length)
  next
    show "\<forall>i < length (named_coherent_chart G \<Gamma>).
      G (named_coherent_chart G \<Gamma> ! i) = \<Gamma> ! i"
    proof (intro allI impI)
      fix i
      assume bound: "i < length (named_coherent_chart G \<Gamma>)"
      have original_bound: "i < length \<Gamma>" using bound by (simp only: named_coherent_chart_length)
      show "G (named_coherent_chart G \<Gamma> ! i) = \<Gamma> ! i"
        by (simp only: named_coherent_chart_nth[OF original_bound] named_typed_supply_type[OF rich])
    qed
  qed
  show ?thesis unfolding named_chart_def by (rule conjI[OF distinct types])
qed

lemma named_coherent_chart_agreement:
  assumes left: "i < length \<Gamma>" and right: "i < length \<Delta>" and types: "\<Gamma> ! i = \<Delta> ! i"
  shows "named_coherent_chart G \<Gamma> ! i = named_coherent_chart G \<Delta> ! i"
  by (simp only: named_coherent_chart_nth[OF left] named_coherent_chart_nth[OF right] types)

theorem named_aligned_charts_for_term:
  assumes rich: "sg_rich G" and left: "has_stype L \<Gamma> M \<tau>"
    and right: "has_stype L \<Delta> M \<tau>"
    and types: "\<And>i. i \<in> sfv M \<Longrightarrow> \<Gamma> ! i = \<Delta> ! i"
  obtains ns ms where "named_chart G \<Gamma> ns" and "named_chart G \<Delta> ms"
    and "\<And>i. i \<in> sfv M \<Longrightarrow> ns ! i = ms ! i"
proof -
  have agree: "named_coherent_chart G \<Gamma> ! i = named_coherent_chart G \<Delta> ! i"
    if free: "i \<in> sfv M" for i
  proof -
    have lb: "i < length \<Gamma>" using subsetD[OF source_typed_fv_bound[OF left] free] by simp
    have rb: "i < length \<Delta>" using subsetD[OF source_typed_fv_bound[OF right] free] by simp
    show "named_coherent_chart G \<Gamma> ! i = named_coherent_chart G \<Delta> ! i"
      by (rule named_coherent_chart_agreement[OF lb rb types[OF free]])
  qed
  show thesis by (rule that[OF named_coherent_chart_valid[OF rich]
    named_coherent_chart_valid[OF rich] agree])
qed

end
