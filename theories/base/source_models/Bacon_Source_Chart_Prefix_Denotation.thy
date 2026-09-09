theory Bacon_Source_Chart_Prefix_Denotation
  imports Bacon_Source_Chart_Denotation Bacon_Source_Named_Model_Vector_Denotation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Chart_Prefix
begin

section \<open>Removing unused trailing chart slots preserves denotation\<close>

text \<open>
  If Γ ⊢ M:τ and Γ↾k ⊢ M:τ, interpreting M through ns or ns↾k
  gives the same value under the same source environment ρ.
  Source role: locality and βη invariance in Bacon–Dorr
  Definition 3.1(ii.c–d), pp.43–44.

  Representation. First replace the full-chart decoding by the
  α-equivalent prefix decoding, keeping the full partial assignment.
  Then locality replaces that assignment by the prefix assignment.
  They agree only on the prefix decoding's free names; no assignment
  to discarded chart names is required on the prefix side.

  Status. This is a typed prefix-restriction theorem in an arbitrary
  independent named model. Both source typings are explicit. It does
  not identify unrelated frames or charts, impose disjoint domains,
  or assume Functionality or general Γ erasure.
\<close>

lemma chart_prefix_lookup:
  assumes index: "lookup (take k \<Gamma>) i = Some \<sigma>"
  shows "lookup \<Gamma> i = Some \<sigma>"
proof -
  have bound: "i < length (take k \<Gamma>)" and ty: "(take k \<Gamma>) ! i = \<sigma>"
    using index by (auto simp: lookup_def split: if_splits)
  have before_k: "i < k" and before_end: "i < length \<Gamma>" using bound by simp_all
  have original: "\<Gamma> ! i = \<sigma>" using ty by (simp only: nth_take[OF before_k])
  show ?thesis by (simp only: lookup_def before_end if_True original)
qed

lemma chart_prefix_env_typed:
  assumes env: "pbbk_env_typed D \<Gamma> \<rho>"
  shows "pbbk_env_typed D (take k \<Gamma>) \<rho>"
proof (unfold pbbk_env_typed_def, intro allI impI)
  fix i \<sigma>
  assume index: "lookup (take k \<Gamma>) i = Some \<sigma>"
  show "\<rho> i \<in> D \<sigma>" by (rule pbbk_env_lookup[OF env chart_prefix_lookup[OF index]])
qed

lemma named_chart_assignment_prefix_agree:
  assumes distinct: "distinct ns" and member: "n \<in> set (take k ns)"
  shows "named_chart_assignment ns \<rho> n = named_chart_assignment (take k ns) \<rho> n"
proof -
  obtain i where bound: "i < length (take k ns)" and at_i: "(take k ns) ! i = n"
    using member by (auto simp: in_set_conv_nth)
  have before_k: "i < k" and before_end: "i < length ns" using bound by simp_all
  have full_name: "ns ! i = n" using at_i by (simp only: nth_take[OF before_k])
  have full: "named_chart_assignment ns \<rho> n = Some (\<rho> i)"
    using named_chart_assignment_lookup[OF distinct before_end, where \<rho>=\<rho>]
    by (simp only: full_name)
  have small_distinct: "distinct (take k ns)" by (rule distinct_take[OF distinct])
  have small: "named_chart_assignment (take k ns) \<rho> n = Some (\<rho> i)"
    using named_chart_assignment_lookup[OF small_distinct bound, where \<rho>=\<rho>]
    by (simp only: at_i)
  show ?thesis by (rule trans[OF full sym[OF small]])
qed

context paper_named_bbk_model
begin

theorem chart_denote_prefix:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and prefix_type: "has_stype paper_logical_type (take k \<Gamma>) M \<tau>"
    and chart: "named_chart stock \<Gamma> ns"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "chart_denote ns \<rho> M = chart_denote (take k ns) \<rho> M"
proof -
  let ?N = "source_to_named stock ns M"
  let ?P = "source_to_named stock (take k ns) M"
  let ?g = "named_chart_assignment ns \<rho>"
  let ?h = "named_chart_assignment (take k ns) \<rho>"
  have whole_type: "has_stype paper_logical_type \<Gamma> M \<tau>"
    and sig: "sterm_in_signature signature M"
    using language unfolding sterm_in_language_def by blast+
  have prefix_language: "sterm_in_language paper_logical_type signature (take k \<Gamma>) M \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF prefix_type sig])
  have prefix_chart: "named_chart stock (take k \<Gamma>) (take k ns)"
    by (rule named_chart_take[OF chart])
  have prefix_env: "pbbk_env_typed domain (take k \<Gamma>) \<rho>"
    by (rule chart_prefix_env_typed[OF env])
  have gt: "named_env_typed domain stock ?g" by (rule named_chart_assignment_typed[OF chart env])
  have ht: "named_env_typed domain stock ?h"
    by (rule named_chart_assignment_typed[OF prefix_chart prefix_env])
  have nl: "named_in_language paper_logical_type signature stock ?N \<tau>"
    by (rule source_to_named_language[OF language chart stock_rich])
  have pl: "named_in_language paper_logical_type signature stock ?P \<tau>"
    by (rule source_to_named_language[OF prefix_language prefix_chart stock_rich])
  have ga: "named_adequate ?g ?N" by (rule chart_decoder_adequate[OF whole_type chart])
  have alpha: "named_alpha stock ?N ?P"
    by (rule source_to_named_chart_prefix_alpha[OF whole_type prefix_type chart stock_rich])
  have replace_decoding: "denote ?g ?N = denote ?g ?P"
    by (rule paper_named_alpha_denote[OF alpha nl gt ga])
  have support: "named_fv ?P \<subseteq> set (take k ns)"
    by (rule source_to_named_fv_bound[OF prefix_type prefix_chart stock_rich])
  have full_support: "named_fv ?P \<subseteq> set ns"
    by (rule subset_trans[OF support set_take_subset])
  have gp: "named_adequate ?g ?P" by (rule named_chart_assignment_adequate[OF full_support])
  have hp: "named_adequate ?h ?P" by (rule named_chart_assignment_adequate[OF support])
  have agree: "?g n = ?h n" if "n \<in> named_fv ?P" for n
    by (rule named_chart_assignment_prefix_agree[OF named_chart_distinct[OF chart]
      subsetD[OF support that]])
  have replace_assignment: "denote ?g ?P = denote ?h ?P"
    by (rule denote_locality[OF pl gt ht gp hp agree])
  show ?thesis unfolding chart_denote_def
    by (rule trans[OF replace_decoding replace_assignment])
qed

end

end
