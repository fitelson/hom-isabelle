theory Bacon_Source_Named_Charts
  imports Bacon_Source_Named_Representation Bacon_Source_Rich_Stock
begin

section \<open>Distinct typed names for the slots of a finite frame\<close>

text \<open>
  A chart for Γ = [σ₀,…,σₖ] chooses distinct names [x₀,…,xₖ]
  with G(xᵢ) = σᵢ. A binder of type σ extends the chart by a fresh
  name of that type. Source role: the fixed types and infinitely many
  variables of each type in Bacon–Dorr §1.1, p.5.

  Isabelle representation. Charts run from slot 0 outwards, unlike an
  outermost-first abstraction vector. A fresh name is chosen outside
  the finite chart by HOL choice. This is syntax and typing infrastructure,
  not an assignment function, interpretation, or context-erasure theorem.
\<close>

definition named_chart :: "sgcontext \<Rightarrow> ctx \<Rightarrow> nat list \<Rightarrow> bool" where
  "named_chart G \<Gamma> ns \<longleftrightarrow>
    distinct ns \<and> list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) ns \<Gamma>"

lemma named_chart_distinct:
  "named_chart G \<Gamma> ns \<Longrightarrow> distinct ns"
  unfolding named_chart_def by (rule conjunct1)

lemma named_chart_types:
  "named_chart G \<Gamma> ns \<Longrightarrow> list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) ns \<Gamma>"
  unfolding named_chart_def by (rule conjunct2)

lemma named_chart_length:
  "named_chart G \<Gamma> ns \<Longrightarrow> length ns = length \<Gamma>"
  by (rule list_all2_lengthD, rule named_chart_types, assumption)

lemma named_chart_Nil: "named_chart G [] []"
  by (simp add: named_chart_def)

lemma named_chart_Cons:
  assumes chart: "named_chart G \<Gamma> ns" and typed: "G n = \<sigma>" and fresh: "n \<notin> set ns"
  shows "named_chart G (\<sigma> # \<Gamma>) (n # ns)"
  using chart typed fresh by (simp add: named_chart_def)

lemma named_chart_lookup_bound:
  assumes chart: "named_chart G \<Gamma> ns" and lookup: "lookup \<Gamma> i = Some \<sigma>"
  shows "i < length ns"
  using lookup named_chart_length[OF chart] by (auto simp: lookup_def split: if_splits)

lemma named_chart_lookup:
  assumes chart: "named_chart G \<Gamma> ns" and lookup: "lookup \<Gamma> i = Some \<sigma>"
  shows "G (ns ! i) = \<sigma>"
proof -
  have bound: "i < length ns" by (rule named_chart_lookup_bound[OF chart lookup])
  have slot: "\<Gamma> ! i = \<sigma>" using lookup by (auto simp: lookup_def split: if_splits)
  have types: "G (ns ! i) = \<Gamma> ! i"
    by (rule list_all2_nthD[OF named_chart_types[OF chart] bound])
  show ?thesis by (rule trans[OF types slot])
qed

definition named_chart_fresh :: "sgcontext \<Rightarrow> nat list \<Rightarrow> otype \<Rightarrow> nat" where
  "named_chart_fresh G ns \<sigma> = (SOME n. G n = \<sigma> \<and> n \<notin> set ns)"

lemma named_chart_fresh_spec:
  assumes rich: "sg_rich G"
  shows "G (named_chart_fresh G ns \<sigma>) = \<sigma> \<and> named_chart_fresh G ns \<sigma> \<notin> set ns"
  unfolding named_chart_fresh_def
  by (rule someI_ex, rule sg_rich_fresh[OF rich], rule finite_set)

lemma named_chart_fresh_type:
  "sg_rich G \<Longrightarrow> G (named_chart_fresh G ns \<sigma>) = \<sigma>"
  by (rule conjunct1, rule named_chart_fresh_spec, assumption)

lemma named_chart_fresh_notin:
  "sg_rich G \<Longrightarrow> named_chart_fresh G ns \<sigma> \<notin> set ns"
  by (rule conjunct2, rule named_chart_fresh_spec, assumption)

lemma named_chart_fresh_extend:
  assumes chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_chart G (\<sigma> # \<Gamma>) (named_chart_fresh G ns \<sigma> # ns)"
  by (rule named_chart_Cons[OF chart named_chart_fresh_type[OF rich] named_chart_fresh_notin[OF rich]])

theorem named_chart_exists:
  assumes rich: "sg_rich G"
  shows "\<exists>ns. named_chart G \<Gamma> ns"
proof (induction \<Gamma>)
  case Nil
  show ?case by (rule exI[where x="[]"], rule named_chart_Nil)
next
  case (Cons \<sigma> \<Gamma>)
  obtain ns where chart: "named_chart G \<Gamma> ns" using Cons.IH by (elim exE)
  show ?case by (rule exI[where x="named_chart_fresh G ns \<sigma> # ns"],
    rule named_chart_fresh_extend[OF chart rich])
qed

subsection \<open>A distinct chart is inverse to its relative binder index\<close>

lemma named_index_nth_distinct:
  assumes distinct: "distinct ns" and bound: "i < length ns"
  shows "named_index ns (ns ! i) = i"
  using distinct bound
proof (induction ns arbitrary: i)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons n ns)
  show ?case
  proof (cases i)
    case 0
    show ?thesis by (simp add: 0)
  next
    case (Suc j)
    have tail_distinct: "distinct ns" and absent: "n \<notin> set ns"
      using Cons.prems(1) by simp_all
    have tail_bound: "j < length ns" using Cons.prems(2) Suc by simp
    have member: "ns ! j \<in> set ns" by (rule nth_mem[OF tail_bound])
    have different: "ns ! j \<noteq> n" using absent member by auto
    have tail_index: "named_index ns (ns ! j) = j"
      by (rule Cons.IH[OF tail_distinct tail_bound])
    show ?thesis by (simp add: Suc different tail_index)
  qed
qed

lemma named_chart_index_lookup:
  assumes chart: "named_chart G \<Gamma> ns" and lookup: "lookup \<Gamma> i = Some \<sigma>"
  shows "named_index ns (ns ! i) = i"
  by (rule named_index_nth_distinct[OF named_chart_distinct[OF chart] named_chart_lookup_bound[OF chart lookup]])

end
