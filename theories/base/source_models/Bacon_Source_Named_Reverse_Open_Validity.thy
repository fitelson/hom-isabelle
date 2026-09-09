theory Bacon_Source_Named_Reverse_Open_Validity
  imports Bacon_Source_Named_Reverse_Completion_Truth Bacon_Source_Named_Reverse_Open_Truth
begin

section \<open>Open named validity agrees with validity of its finite-prefix encoding\<close>

text \<open>
  Let A:t be a named formula and let m cover every free name of A.
  Then A holds at every adequate typed named assignment exactly when
  its source encoding holds at every typed environment for G↾m in the
  constructed reverse model. Source: Bacon–Dorr Definition 3.1's validity
  convention, pp.43–44.

  Representation: forward transport extracts the finite partial assignment
  from an arbitrary prefix environment. Reverse transport completes an
  arbitrary adequate partial assignment, then tags the completion's values.
  No condition is imposed on a forward environment outside its finite
  prefix. The completion in the reverse argument exists by nonempty domains.

  Status: a model-relative validity equivalence in an arbitrary independent
  named model. The reverse carrier is explicitly otype × value; this is
  neither a raw-model isomorphism nor named H proof correspondence.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_reverse_open_valid_iff:
  assumes language: "named_in_language paper_logical_type signature stock A Prop"
    and bound: "source_free_bound (named_to_source stock [] A) \<le> m"
  shows "named_valid A \<longleftrightarrow>
    paper_db_bbk_structure.paper_db_valid signature (named_tag_domain domain)
      (named_erased_denote stock model_tag_denote) model_tag_valuation
      (source_prefix stock m) (named_to_source stock [] A)"
proof -
  interpret Reverse: paper_db_bbk_structure signature "named_tag_domain domain"
    "named_erased_denote stock model_tag_denote" model_tag_valuation
    by (rule paper_named_to_db_model)
  let ?E = "named_to_source stock [] A"
  let ?\<Gamma> = "source_prefix stock m"
  have source_language: "sterm_in_language paper_logical_type signature ?\<Gamma> ?E Prop"
    by (rule named_encoding_prefix_language[OF language bound])
  have support: "named_fv A \<subseteq> {..<m}"
  proof
    fix n
    assume free: "n \<in> named_fv A"
    show "n \<in> {..<m}" using named_prefix_free_name[OF bound free] by simp
  qed
  show ?thesis
  proof
    assume valid: "named_valid A"
    have all_named: "\<And>g. named_env_typed domain stock g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> valuation (denote g A)"
      using valid unfolding named_valid_def named_satisfies_def by blast
    show "Reverse.paper_db_valid ?\<Gamma> ?E"
    proof (unfold Reverse.paper_db_valid_def, rule conjI[OF source_language], intro allI impI)
      fix \<rho>
      assume env: "pbbk_env_typed (named_tag_domain domain) ?\<Gamma> \<rho>"
      let ?q = "named_untag_assignment (named_prefix_assignment m \<rho>)"
      have qt: "named_env_typed domain stock ?q"
        by (rule named_untagged_prefix_typed[OF env])
      have qa: "named_adequate ?q A"
        by (rule named_untagged_prefix_adequate[OF support])
      have truth: "valuation (denote ?q A)" by (rule all_named[OF qt qa])
      have transport: "model_tag_valuation (named_erased_denote stock model_tag_denote \<rho> ?E) =
        valuation (denote ?q A)"
        by (rule paper_named_reverse_prefix_truth[OF language bound env])
      show "Reverse.paper_db_satisfies \<rho> ?E"
        by (simp only: Reverse.paper_db_satisfies_def transport; rule truth)
    qed
  next
    assume valid: "Reverse.paper_db_valid ?\<Gamma> ?E"
    have all_source: "\<And>\<rho>. pbbk_env_typed (named_tag_domain domain) ?\<Gamma> \<rho> \<Longrightarrow>
      model_tag_valuation (named_erased_denote stock model_tag_denote \<rho> ?E)"
      using valid unfolding Reverse.paper_db_valid_def Reverse.paper_db_satisfies_def by blast
    show "named_valid A"
    proof (unfold named_valid_def, rule conjI[OF language], intro allI impI)
      fix g
      assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
      obtain h where completion: "named_completion domain stock g h"
        using named_assignment_completion_exists[OF domain_nonempty typed] by (elim exE)
      let ?\<rho> = "\<lambda>n. (stock n, h n)"
      have env: "pbbk_env_typed (named_tag_domain domain) ?\<Gamma> ?\<rho>"
        by (rule named_tagged_prefix_env_from_completion[OF completion])
      have truth: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> ?E)"
        by (rule all_source[OF env])
      have transport: "model_tag_valuation (named_erased_denote stock model_tag_denote ?\<rho> ?E) =
        valuation (denote g A)"
        by (rule paper_named_reverse_completion_truth[OF language bound typed adequate completion])
      show "named_satisfies g A" using truth
        by (simp only: named_satisfies_def transport)
    qed
  qed
qed

end

end
