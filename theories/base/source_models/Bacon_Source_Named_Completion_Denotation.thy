theory Bacon_Source_Named_Completion_Denotation
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Representation
begin

section \<open>Denotation of adequate partial named assignments\<close>

text \<open>
  For A:σ and a typed partial assignment g adequate for A, define ⟦A⟧ᴹᵍ
  using a total typed completion h of g. Every such completion gives the
  same value: their values agree on FV(A), and source locality applies in
  a common finite prefix of G.

  Source role: the adequate-assignment convention of Bacon–Dorr
  Definition 3.1, pp.43–44. Representation: named_to_source G [] A retains
  exactly the free names of A. The definition below uses HOL choice only
  after a separate completion-existence theorem is available.

  Status: all results are conditional on the weak paper_db_bbk_structure.
  No named-model predicate, H theorem, richer coherent-model assumption,
  richness of G, or countability is used. This leaf establishes
  completion-independent denotation, not equivalence of model classes.
\<close>

context paper_db_bbk_structure
begin

lemma paper_db_named_total_locality:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and first: "paper_global_env_typed domain G h"
    and second: "paper_global_env_typed domain G k"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> h n = k n"
  shows "denote h (named_to_source G [] A) = denote k (named_to_source G [] A)"
proof -
  let ?E = "named_to_source G [] A"
  let ?\<Gamma> = "source_prefix G (source_free_bound ?E)"
  have global_language: "sgterm_in_language paper_logical_type signature G ?E \<sigma>"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
  have finite_language: "sterm_in_language paper_logical_type signature ?\<Gamma> ?E \<sigma>"
    by (rule source_language_in_prefix[OF global_language]) (rule order_refl)
  have h_env: "pbbk_env_typed domain ?\<Gamma> h"
    by (rule paper_global_env_prefix[OF first])
  have k_env: "pbbk_env_typed domain ?\<Gamma> k"
    by (rule paper_global_env_prefix[OF second])
  show ?thesis
  proof (rule denote_locality[OF finite_language finite_language h_env k_env])
    fix n
    assume member: "n \<in> sfv ?E"
    have named_member: "n \<in> named_fv A"
      using member by (simp only: named_to_source_empty_fv)
    show "h n = k n" by (rule agree[OF named_member])
  qed
qed

theorem paper_db_named_completion_independent:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and adequate: "named_adequate g A"
    and first: "named_completion domain G g h"
    and second: "named_completion domain G g k"
  shows "denote h (named_to_source G [] A) = denote k (named_to_source G [] A)"
proof (rule paper_db_named_total_locality[OF language
    named_completion_typed[OF first] named_completion_typed[OF second]])
  fix n
  assume member: "n \<in> named_fv A"
  show "h n = k n" by (rule named_completions_agree[OF adequate first second member])
qed

text \<open>
  The independence lemma does not separately assume that g is typed:
  its two completion premises already supply the total typed assignments
  needed by locality. Typing of g is required below to obtain a completion.
  Outside the stated guards, HOL still assigns a value to named_denote,
  but no semantic clause is claimed for that value.
\<close>

definition named_denote ::
  "sgcontext \<Rightarrow> 'v named_assignment \<Rightarrow> ('c, paper_logical) named_term \<Rightarrow> 'v"
where
  "named_denote G g A =
    denote (SOME h. named_completion domain G g h) (named_to_source G [] A)"

lemma paper_db_named_chosen_completion:
  assumes typed: "named_env_typed domain G g"
  shows "named_completion domain G g (SOME h. named_completion domain G g h)"
proof -
  have exists_completion: "\<exists>h. named_completion domain G g h"
    by (rule named_assignment_completion_exists[where D=domain and G=G, OF domain_nonempty typed])
  show ?thesis by (rule someI_ex[OF exists_completion])
qed

theorem paper_db_named_denote_completion:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g A"
    and completion: "named_completion domain G g h"
  shows "named_denote G g A = denote h (named_to_source G [] A)"
  unfolding named_denote_def
  by (rule paper_db_named_completion_independent[OF language adequate
    paper_db_named_chosen_completion[OF typed] completion])

section \<open>Typing, variables, and locality for partial assignments\<close>

text \<open>
  The value ⟦A⟧ᴹᵍ lies in Dσ when A:σ and g is typed and adequate.
  For a variable x assigned a, its value is a. If two adequate typed
  partial assignments agree on FV(A), they give A the same value.
  Representation: these clauses are derived from the weak source fields,
  not stipulated as new axioms for named_denote.
\<close>

theorem paper_db_named_denote_type:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g A"
  shows "named_denote G g A \<in> domain \<sigma>"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  have completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF typed])
  have global_language:
    "sgterm_in_language paper_logical_type signature G (named_to_source G [] A) \<sigma>"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
  have member: "denote ?h (named_to_source G [] A) \<in> domain \<sigma>"
    by (rule paper_db_global_denote_type[OF global_language
      named_completion_typed[OF completion]])
  show ?thesis using member by (simp only: named_denote_def)
qed

theorem paper_db_named_denote_variable:
  assumes typed: "named_env_typed domain G g" and assigned: "g n = Some a"
  shows "named_denote G g (NVar n) = a"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  have completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF typed])
  have env: "pbbk_env_typed domain (source_prefix G (Suc n)) ?h"
    by (rule paper_global_env_prefix[OF named_completion_typed[OF completion]])
  have index: "lookup (source_prefix G (Suc n)) n = Some (G n)"
    by (rule source_prefix_lookup) simp
  have variable_value: "denote ?h (SVar n) = ?h n"
    by (rule denote_var[OF index env])
  have chosen_value: "?h n = a" by (rule named_completion_value[OF completion assigned])
  show ?thesis using trans[OF variable_value chosen_value]
    by (simp only: named_denote_def named_to_source.simps named_index.simps)
qed

theorem paper_db_named_denote_locality:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and g_typed: "named_env_typed domain G g"
    and j_typed: "named_env_typed domain G j"
    and g_adequate: "named_adequate g A"
    and j_adequate: "named_adequate j A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = j n"
  shows "named_denote G g A = named_denote G j A"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  let ?k = "SOME k. named_completion domain G j k"
  have h_completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF g_typed])
  have k_completion: "named_completion domain G j ?k"
    by (rule paper_db_named_chosen_completion[OF j_typed])
  have same: "denote ?h (named_to_source G [] A) = denote ?k (named_to_source G [] A)"
  proof (rule paper_db_named_total_locality[OF language
      named_completion_typed[OF h_completion] named_completion_typed[OF k_completion]])
    fix n
    assume member: "n \<in> named_fv A"
    obtain a where at_g: "g n = Some a"
      by (rule named_adequate_value[OF g_adequate member])
    have at_j: "j n = Some a" by (rule trans[OF sym[OF agree[OF member]] at_g])
    have h_value: "?h n = a" by (rule named_completion_value[OF h_completion at_g])
    have k_value: "?k n = a" by (rule named_completion_value[OF k_completion at_j])
    show "?h n = ?k n" by (rule trans[OF h_value sym[OF k_value]])
  qed
  show ?thesis using same by (simp only: named_denote_def)
qed

text \<open>
  The guarded value is now independent of total completion. Application,
  binding and logical truth clauses for partial named assignments, and the
  converse model transport with its Γ-erasure obligations, remain separate
  proof stages. In particular no named-model-class equivalence follows
  merely from the definition above.
\<close>

end

end
