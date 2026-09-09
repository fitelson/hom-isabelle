theory Bacon_Source_Chart_Assignments
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Charts
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>A finite typed frame supplies an adequate partial named assignment\<close>

text \<open>
  A chart ns names the slots of Γ without repetitions and preserves each
  slot's type. Assign nsᵢ the value ρ(i); names outside ns are unassigned.
  Source role: comparing finite de Bruijn environments with the adequate
  partial assignments of Bacon–Dorr Definition 3.1, pp.43–44.

  The map is explicitly finite. Its typing is proved from Γ and the chart,
  not obtained by imposing global type constraints on unused slots of ρ.
  Adequacy follows when the represented term's free names lie in the chart.
  This leaf asserts no denotation independence or model equivalence.
\<close>

definition named_chart_assignment :: "nat list \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'v named_assignment" where
  "named_chart_assignment ns \<rho> = map_of (zip ns (map \<rho> [0..<length ns]))"

lemma named_chart_assignment_domain:
  "dom (named_chart_assignment ns \<rho>) = set ns"
  by (simp add: named_chart_assignment_def)

lemma named_chart_assignment_lookup:
  assumes distinct: "distinct ns" and bound: "i < length ns"
  shows "named_chart_assignment ns \<rho> (ns ! i) = Some (\<rho> i)"
proof -
  have lengths: "length ns = length (map \<rho> [0..<length ns])" by simp
  have index: "i < length (map \<rho> [0..<length ns])" using bound by simp
  have result: "map_of (zip ns (map \<rho> [0..<length ns])) (ns ! i) =
    Some ((map \<rho> [0..<length ns]) ! i)"
    by (rule map_of_zip_nth[OF lengths distinct index])
  show ?thesis using result bound by (simp add: named_chart_assignment_def)
qed

lemma named_chart_assignment_value:
  assumes distinct: "distinct ns" and assigned: "named_chart_assignment ns \<rho> n = Some a"
  obtains i where "i < length ns" and "ns ! i = n" and "\<rho> i = a"
proof -
  have member: "n \<in> set ns"
    using assigned named_chart_assignment_domain[where ns=ns and \<rho>=\<rho>]
    by (auto simp: dom_def)
  obtain i where bound: "i < length ns" and index: "ns ! i = n"
    using member by (auto simp: in_set_conv_nth)
  have projected: "named_chart_assignment ns \<rho> n = Some (\<rho> i)"
    using named_chart_assignment_lookup[OF distinct bound, where \<rho>=\<rho>]
    by (simp only: index)
  have payload: "\<rho> i = a" using assigned projected by simp
  show thesis by (rule that[OF bound index payload])
qed

theorem named_chart_assignment_typed:
  assumes chart: "named_chart G \<Gamma> ns" and env: "pbbk_env_typed D \<Gamma> \<rho>"
  shows "named_env_typed D G (named_chart_assignment ns \<rho>)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "named_chart_assignment ns \<rho> n = Some a"
  have distinct: "distinct ns" and types: "list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) ns \<Gamma>"
    using chart unfolding named_chart_def by blast+
  obtain i where bound: "i < length ns" and index: "ns ! i = n" and payload: "\<rho> i = a"
    by (rule named_chart_assignment_value[OF distinct assigned])
  have lengths: "length ns = length \<Gamma>" by (rule list_all2_lengthD[OF types])
  have context_bound: "i < length \<Gamma>" using bound lengths by simp
  have lookup: "lookup \<Gamma> i = Some (\<Gamma> ! i)" using context_bound by (simp add: lookup_def)
  have named_type: "G (ns ! i) = \<Gamma> ! i" by (rule list_all2_nthD[OF types bound])
  have member: "\<rho> i \<in> D (\<Gamma> ! i)" by (rule pbbk_env_lookup[OF env lookup])
  have type_eq: "G n = \<Gamma> ! i" using named_type by (simp only: index)
  show "a \<in> D (G n)" using member by (simp only: payload type_eq)
qed

lemma named_chart_assignment_adequate:
  assumes support: "named_fv A \<subseteq> set ns"
  shows "named_adequate (named_chart_assignment ns \<rho>) A"
  by (simp only: named_adequate_def named_chart_assignment_domain; rule support)

subsection \<open>Extending a frame corresponds to assigning its new binder\<close>

lemma named_chart_values_Cons:
  "map \<rho> [0..<Suc n] = \<rho> 0 # map (\<lambda>i. \<rho> (Suc i)) [0..<n]"
  by (induction n) (simp_all add: upt_Suc)

theorem named_chart_assignment_extend:
  "named_chart_assignment (n # ns) (pbbk_extend a \<rho>) =
    (named_chart_assignment ns \<rho>)(n := Some a)"
  unfolding named_chart_assignment_def
  by (simp only: length_Cons named_chart_values_Cons; simp)

lemma named_chart_assignment_empty:
  "named_chart_assignment [] \<rho> = Map.empty"
  by (simp add: named_chart_assignment_def)

end
