theory Bacon_Source_Chart_Independence
  imports Bacon_Source_Chart_Denotation Bacon_Source_Named_Model_Vector_Denotation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Vector_Encoding
begin

section \<open>Changing the names of one fixed finite frame does not change denotation\<close>

text \<open>
  For two charts ns and ms of Γ, close the two decoded terms by
  λrev(ns) and λrev(ms). Their empty-stack encodings are the same
  source abstraction, so these closed terms are α-equivalent and have
  equal values even under the two chart assignments. Corresponding
  variable arguments have the common value ρ(i). Finite application
  congruence and literal β self-deabstraction recover the decoded terms.
  Source: Bacon–Dorr Definition 3.1(ii.a–d), pp.43–44.

  Status: the proof is in an arbitrary independent named model. It
  neither uses pointwise λ-extensionality nor assumes disjoint domains.
  Γ is the same on both sides: independence of different typing frames
  is not asserted by this chart-choice result.
\<close>

lemma chart_named_app_vec_adequate:
  assumes head: "named_adequate g F"
    and arguments: "\<And>A. A \<in> set As \<Longrightarrow> named_adequate g A"
  shows "named_adequate g (named_app_vec F As)"
  using head arguments
proof (induction As arbitrary: F)
  case Nil
  show ?case using Nil.prems(1) by simp
next
  case (Cons A As)
  have argument: "named_adequate g A" by (rule Cons.prems(2)) simp
  have next_head: "named_adequate g (NApp F A)"
    using Cons.prems(1) argument unfolding named_adequate_def by auto
  have rest: "\<And>B. B \<in> set As \<Longrightarrow> named_adequate g B"
    by (rule Cons.prems(2)) simp
  show ?case using Cons.IH[OF next_head rest] by simp
qed

lemma chart_named_vector_argument_adequate:
  assumes member: "A \<in> set (map NVar (rev ns))"
  shows "named_adequate (named_chart_assignment ns \<rho>) A"
proof (rule named_chart_assignment_adequate)
  show "named_fv A \<subseteq> set ns" using member by auto
qed

context paper_named_bbk_model
begin

lemma chart_reverse_variable_values:
  assumes first: "named_chart stock \<Gamma> ns"
    and second: "named_chart stock \<Gamma> ms"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "list_all2 (\<lambda>A B. denote (named_chart_assignment ns \<rho>) A =
    denote (named_chart_assignment ms \<rho>) B) (map NVar (rev ns)) (map NVar (rev ms))"
proof -
  have lengths: "length ns = length ms"
    using named_chart_length[OF first] named_chart_length[OF second] by simp
  have gt: "named_env_typed domain stock (named_chart_assignment ns \<rho>)"
    by (rule named_chart_assignment_typed[OF first env])
  have ht: "named_env_typed domain stock (named_chart_assignment ms \<rho>)"
    by (rule named_chart_assignment_typed[OF second env])
  have ascending: "list_all2 (\<lambda>A B. denote (named_chart_assignment ns \<rho>) A =
    denote (named_chart_assignment ms \<rho>) B) (map NVar ns) (map NVar ms)"
  proof (unfold list_all2_conv_all_nth length_map, rule conjI)
    show "length ns = length ms" by (rule lengths)
  next
    show "\<forall>i < length ns.
      denote (named_chart_assignment ns \<rho>) ((map NVar ns) ! i) =
      denote (named_chart_assignment ms \<rho>) ((map NVar ms) ! i)"
    proof (intro allI impI)
      fix i
      assume ni: "i < length ns"
      have mi: "i < length ms" using ni lengths by simp
      have na: "named_chart_assignment ns \<rho> (ns ! i) = Some (\<rho> i)"
        by (rule named_chart_assignment_lookup[OF named_chart_distinct[OF first] ni])
      have ma: "named_chart_assignment ms \<rho> (ms ! i) = Some (\<rho> i)"
        by (rule named_chart_assignment_lookup[OF named_chart_distinct[OF second] mi])
      have nv: "denote (named_chart_assignment ns \<rho>) (NVar (ns ! i)) = \<rho> i"
        by (rule denote_var[OF gt na])
      have mv: "denote (named_chart_assignment ms \<rho>) (NVar (ms ! i)) = \<rho> i"
        by (rule denote_var[OF ht ma])
      show "denote (named_chart_assignment ns \<rho>) ((map NVar ns) ! i) =
        denote (named_chart_assignment ms \<rho>) ((map NVar ms) ! i)"
        using trans[OF nv sym[OF mv]] by (simp only: nth_map[OF ni] nth_map[OF mi])
    qed
  qed
  show ?thesis using ascending by (simp only: rev_map[symmetric] list_all2_rev)
qed

theorem chart_denote_independent:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and first: "named_chart stock \<Gamma> ns"
    and second: "named_chart stock \<Gamma> ms"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "chart_denote ns \<rho> M = chart_denote ms \<rho> M"
proof -
  let ?A = "source_to_named stock ns M"
  let ?B = "source_to_named stock ms M"
  let ?F = "named_lam_vec (rev ns) ?A"
  let ?H = "named_lam_vec (rev ms) ?B"
  let ?g = "named_chart_assignment ns \<rho>"
  let ?h = "named_chart_assignment ms \<rho>"
  let ?xs = "map NVar (rev ns) :: 'c paper_named_term list"
  let ?ys = "map NVar (rev ms) :: 'c paper_named_term list"
  have typed: "has_stype paper_logical_type \<Gamma> M \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have al: "named_in_language paper_logical_type signature stock ?A \<tau>"
    by (rule source_to_named_language[OF language first stock_rich])
  have bl: "named_in_language paper_logical_type signature stock ?B \<tau>"
    by (rule source_to_named_language[OF language second stock_rich])
  have fl: "named_in_language paper_logical_type signature stock ?F (sarrow_type (rev \<Gamma>) \<tau>)"
    by (rule source_to_named_closed_abstraction_language[OF language first stock_rich])
  have hl: "named_in_language paper_logical_type signature stock ?H (sarrow_type (rev \<Gamma>) \<tau>)"
    by (rule source_to_named_closed_abstraction_language[OF language second stock_rich])
  have fc: "named_fv ?F = {}"
    by (rule source_to_named_closed_abstraction_fv[OF typed first stock_rich])
  have hc: "named_fv ?H = {}"
    by (rule source_to_named_closed_abstraction_fv[OF typed second stock_rich])
  have gt: "named_env_typed domain stock ?g"
    by (rule named_chart_assignment_typed[OF first env])
  have ht: "named_env_typed domain stock ?h"
    by (rule named_chart_assignment_typed[OF second env])
  have fa: "named_adequate ?g ?F" and ha: "named_adequate ?h ?H"
    by (simp_all add: named_adequate_def fc hc)
  have aa: "named_adequate ?g ?A" by (rule chart_decoder_adequate[OF typed first])
  have ba: "named_adequate ?h ?B" by (rule chart_decoder_adequate[OF typed second])
  have xs_a: "\<And>A. A \<in> set ?xs \<Longrightarrow> named_adequate ?g A"
    by (rule chart_named_vector_argument_adequate)
  have ys_a: "\<And>B. B \<in> set ?ys \<Longrightarrow> named_adequate ?h B"
    by (rule chart_named_vector_argument_adequate)
  have xa: "named_adequate ?g (named_app_vec ?F ?xs)"
    by (rule chart_named_app_vec_adequate[OF fa xs_a])
  have ya: "named_adequate ?h (named_app_vec ?H ?ys)"
    by (rule chart_named_app_vec_adequate[OF ha ys_a])
  have xs_l: "list_all2 (\<lambda>A \<sigma>. named_in_language paper_logical_type signature stock A \<sigma>)
    ?xs (rev \<Gamma>)"
    using named_vector_variables_language[where L=paper_logical_type and \<Sigma>=signature
      and G=stock and ns="rev ns"]
    by (simp only: rev_map[symmetric] named_chart_map_types[OF first])
  have ys_l: "list_all2 (\<lambda>A \<sigma>. named_in_language paper_logical_type signature stock A \<sigma>)
    ?ys (rev \<Gamma>)"
    using named_vector_variables_language[where L=paper_logical_type and \<Sigma>=signature
      and G=stock and ns="rev ms"]
    by (simp only: rev_map[symmetric] named_chart_map_types[OF second])
  have alpha: "named_alpha stock ?F ?H"
    by (rule named_chart_closed_abstractions_alpha[OF typed first second stock_rich])
  have heads: "denote ?g ?F = denote ?h ?H"
    by (rule paper_named_closed_alpha_denote[OF alpha fl fc gt ht])
  have arguments: "list_all2 (\<lambda>A B. denote ?g A = denote ?h B) ?xs ?ys"
    by (rule chart_reverse_variable_values[OF first second env])
  have applied: "denote ?g (named_app_vec ?F ?xs) = denote ?h (named_app_vec ?H ?ys)"
    by (rule paper_named_app_vec_cong[OF xs_l ys_l fl hl gt ht fa ha xs_a ys_a heads arguments])
  have left_beta: "denote ?g (named_app_vec ?F ?xs) = denote ?g ?A"
    by (rule paper_named_vector_self_denote[OF al gt aa xa])
  have right_beta: "denote ?h (named_app_vec ?H ?ys) = denote ?h ?B"
    by (rule paper_named_vector_self_denote[OF bl ht ba ya])
  have equality: "denote ?g ?A = denote ?h ?B"
    by (rule trans[OF sym[OF left_beta] trans[OF applied right_beta]])
  show ?thesis using equality by (simp only: chart_denote_def)
qed

end

end
