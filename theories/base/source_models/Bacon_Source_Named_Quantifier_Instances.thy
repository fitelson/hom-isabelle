theory Bacon_Source_Named_Quantifier_Instances
  imports Bacon_Source_Named_Denotation_Basics
    Bacon_Source_Vocabulary_Development.Bacon_Source_BBK_Binding
    Bacon_Source_Vocabulary_Development.Bacon_Source_BBK_Renaming_Derived
begin

section \<open>A fresh named argument represents the source quantifier slot\<close>

text \<open>
  Let F:σ → t, with x:σ absent from FV(F), and let h complete the
  adequate typed partial assignment g. For a ∈ Dσ, the completion
  h[x↦a] interprets Fx under g[x↦a]. Its value equals the source value
  of F↑ applied to slot zero under a prepended assignment.
  Source: Bacon–Dorr Definition 3.1(iii.d–e), pp.43–44.

  Representation: a finite prefix contains both the support of F and
  the name x. Derived weak-structure renaming, locality, and application
  congruence compare the two applications. No coherent-model or named-model
  premise is added, and no quantifier truth conclusion is yet needed.
\<close>

context paper_db_bbk_structure
begin

lemma paper_db_named_quantifier_frame:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and n_type: "G n = \<sigma>"
  obtains m where
    "sterm_in_language paper_logical_type signature (source_prefix G m)
      (named_to_source G [] F) (Arr \<sigma> Prop)"
    "lookup (source_prefix G m) n = Some \<sigma>"
proof -
  let ?m = "max (source_free_bound (named_to_source G [] F)) (Suc n)"
  have f_language: "sterm_in_language paper_logical_type signature (source_prefix G ?m)
    (named_to_source G [] F) (Arr \<sigma> Prop)"
    by (rule paper_db_named_language_prefix[OF language]) simp
  have bound: "n < ?m" by simp
  have index: "lookup (source_prefix G ?m) n = Some \<sigma>"
    using source_prefix_lookup[OF bound, where G=G] by (simp only: n_type)
  show thesis by (rule that[OF f_language index])
qed

theorem paper_db_named_quantifier_instance:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and finite_language: "sterm_in_language paper_logical_type signature (source_prefix G m)
      (named_to_source G [] F) (Arr \<sigma> Prop)"
    and index: "lookup (source_prefix G m) n = Some \<sigma>"
    and n_type: "G n = \<sigma>"
    and fresh: "n \<notin> named_fv F"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g F"
    and completion: "named_completion domain G g h"
    and member: "a \<in> domain \<sigma>"
  shows "denote (pbbk_extend a h)
      (SApp (sshift (named_to_source G [] F)) (SVar 0)) =
    named_denote G (g(n := Some a)) (NApp F (NVar n))"
proof -
  let ?E = "named_to_source G [] F"
  let ?\<Gamma> = "source_prefix G m"
  let ?j = "h(n := a)"
  have member_n: "a \<in> domain (G n)" using member by (simp only: n_type)
  have updated_completion: "named_completion domain G (g(n := Some a)) ?j"
    by (rule named_completion_update[OF completion member_n])
  have env: "pbbk_env_typed domain ?\<Gamma> h"
    by (rule paper_global_env_prefix[OF named_completion_typed[OF completion]])
  have updated_env: "pbbk_env_typed domain ?\<Gamma> ?j"
    by (rule paper_global_env_prefix[OF named_completion_typed[OF updated_completion]])
  have extended_env: "pbbk_env_typed domain (\<sigma> # ?\<Gamma>) (pbbk_extend a h)"
    by (rule pbbk_env_extend[OF env member])
  have shifted_language: "sterm_in_language paper_logical_type signature (\<sigma> # ?\<Gamma>)
    (sshift ?E) (Arr \<sigma> Prop)"
    by (rule paper_db_shift_language[OF finite_language])
  have zero_language: "sterm_in_language paper_logical_type signature (\<sigma> # ?\<Gamma>)
    (SVar 0) \<sigma>"
    unfolding sterm_in_language_def
    by (rule conjI) (rule has_stype.Var[OF lookup_Cons_0], simp)
  have n_language: "sterm_in_language paper_logical_type signature ?\<Gamma> (SVar n) \<sigma>"
    unfolding sterm_in_language_def
    by (rule conjI) (rule has_stype.Var[OF index], simp)
  have ren: "\<And>i \<rho>. lookup ?\<Gamma> i = Some \<rho> \<Longrightarrow>
    lookup (\<sigma> # ?\<Gamma>) (Suc i) = Some \<rho>" by simp
  have renamed:
    "denote (pbbk_extend a h) (srename Suc ?E) =
      denote (\<lambda>i. pbbk_extend a h (Suc i)) ?E"
    by (rule paper_db_rename_derived[OF finite_language extended_env ren])
  have shifted: "denote (pbbk_extend a h) (sshift ?E) = denote h ?E"
    using renamed by (simp only: sshift_def pbbk_extend_Suc)
  have unchanged: "denote h ?E = denote ?j ?E"
  proof (rule denote_locality[OF finite_language finite_language env updated_env])
    fix i
    assume fv: "i \<in> sfv ?E"
    have named_fv: "i \<in> named_fv F" using fv by (simp only: named_to_source_empty_fv)
    have distinct: "i \<noteq> n" using fresh named_fv by blast
    show "h i = ?j i" by (simp add: distinct)
  qed
  have heads: "denote (pbbk_extend a h) (sshift ?E) = denote ?j ?E"
    by (rule trans[OF shifted unchanged])
  have zero_value: "denote (pbbk_extend a h) (SVar 0) = a"
    using denote_var[OF lookup_Cons_0 extended_env] by (simp only: pbbk_extend_zero)
  have n_value: "denote ?j (SVar n) = a"
    using denote_var[OF index updated_env] by simp
  have arguments: "denote (pbbk_extend a h) (SVar 0) = denote ?j (SVar n)"
    by (rule trans[OF zero_value sym[OF n_value]])
  have application:
    "denote (pbbk_extend a h) (SApp (sshift ?E) (SVar 0)) =
      denote ?j (SApp ?E (SVar n))"
    by (rule denote_application_cong[OF shifted_language zero_language
      finite_language n_language extended_env updated_env heads arguments])
  have f_type: "has_ntype paper_logical_type G F (Arr \<sigma> Prop)"
    using language unfolding named_in_language_def by (rule conjunct1)
  have f_names: "named_in_signature signature F"
    using language unfolding named_in_language_def by (rule conjunct2)
  have var_type: "has_ntype paper_logical_type G (NVar n) \<sigma>"
    using has_ntype.Var[where L=paper_logical_type and G=G and n=n]
    by (simp only: n_type)
  have app_language: "named_in_language paper_logical_type signature G (NApp F (NVar n)) Prop"
    unfolding named_in_language_def
    by (rule conjI[OF has_ntype.App[OF f_type var_type]])
      (simp only: named_in_signature.simps f_names)
  have updated_type: "named_env_typed domain G (g(n := Some a))"
    by (rule named_assignment_update_typed[OF typed member_n])
  have updated_adequate: "named_adequate (g(n := Some a)) (NApp F (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  have completed:
    "named_denote G (g(n := Some a)) (NApp F (NVar n)) =
      denote ?j (named_to_source G [] (NApp F (NVar n)))"
    by (rule paper_db_named_denote_completion[OF app_language updated_type
      updated_adequate updated_completion])
  have right: "denote ?j (SApp ?E (SVar n)) =
    named_denote G (g(n := Some a)) (NApp F (NVar n))"
    using sym[OF completed] by (simp only: named_to_source.simps named_index.simps)
  show ?thesis by (rule trans[OF application right])
qed

end

end
