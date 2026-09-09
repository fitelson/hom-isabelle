theory Bacon_Book_BBK_Application
  imports Bacon_Book_Applicative_Structure
    Bacon_Parametric_Signature_Development.Bacon_Parametric_BBK_Semantics
begin

section \<open>A typed application operation extracted from a BBK interpretation\<close>

text \<open>
  Represent arbitrary f ∈ Dσ→τ and a ∈ Dσ by two variables, and set
  Appστ(f,a) = J⟨a,f⟩(v₁v₀). Cross-context application congruence shows
  that this agrees with Jg(FA) whenever Jg(F)=f and Jg(A)=a.
  Source role: constructing the typed applicative structure of Bacon's
  Definition 14.1, p.290, from the represented Bacon–Dorr BBK clauses.

  Representation. Only the two-slot context [σ,σ→τ] is used. The
  remaining values are arbitrary defaults, never required to be typed.
  No closed term denoting f or a, Functionality, total book assignment,
  alternative model, or changed carrier is needed. The original BBK
  signature, domains, interpretation and valuation remain fixed; this
  leaf supplies application only, not the book environment or model.
\<close>

context pbbk_model
begin

definition pbbk_book_app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
  "pbbk_book_app \<sigma> \<tau> f a =
    denote (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined))) (PApp (PVar 1) (PVar 0))"

lemma pbbk_book_app_environment:
  assumes function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and argument_member: "a \<in> domain \<sigma>"
  shows "pbbk_env_typed domain [\<sigma>, Arr \<sigma> \<tau>] (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined)))"
proof -
  have empty: "pbbk_env_typed domain [] (\<lambda>_. undefined)" by (rule pbbk_env_empty)
  have head: "pbbk_env_typed domain [Arr \<sigma> \<tau>] (pbbk_extend f (\<lambda>_. undefined))"
    by (rule pbbk_env_extend[OF empty function_member])
  show ?thesis by (rule pbbk_env_extend[OF head argument_member])
qed

lemma pbbk_book_app_head_type:
  "has_ptype [\<sigma>, Arr \<sigma> \<tau>] (PVar 1 :: 'c pterm) (Arr \<sigma> \<tau>)"
  by (rule has_ptype.PVar) (simp add: lookup_def)

lemma pbbk_book_app_argument_type:
  "has_ptype [\<sigma>, Arr \<sigma> \<tau>] (PVar 0 :: 'c pterm) \<sigma>"
  by (rule has_ptype.PVar) simp

lemma pbbk_book_app_head_value:
  assumes function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and argument_member: "a \<in> domain \<sigma>"
  shows "denote (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined))) (PVar 1) = f"
proof -
  have look: "lookup [\<sigma>, Arr \<sigma> \<tau>] 1 = Some (Arr \<sigma> \<tau>)" by (simp add: lookup_def)
  have env: "pbbk_env_typed domain [\<sigma>, Arr \<sigma> \<tau>] (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined)))"
    by (rule pbbk_book_app_environment[OF function_member argument_member])
  show ?thesis using denote_var[OF look env] by (simp add: One_nat_def)
qed

lemma pbbk_book_app_argument_value:
  assumes function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and argument_member: "a \<in> domain \<sigma>"
  shows "denote (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined))) (PVar 0) = a"
proof -
  have look: "lookup [\<sigma>, Arr \<sigma> \<tau>] 0 = Some \<sigma>" by simp
  have env: "pbbk_env_typed domain [\<sigma>, Arr \<sigma> \<tau>] (pbbk_extend a (pbbk_extend f (\<lambda>_. undefined)))"
    by (rule pbbk_book_app_environment[OF function_member argument_member])
  show ?thesis using denote_var[OF look env] by simp
qed

theorem pbbk_book_app_type:
  assumes function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and argument_member: "a \<in> domain \<sigma>"
  shows "pbbk_book_app \<sigma> \<tau> f a \<in> domain \<tau>"
proof -
  have typed: "has_ptype [\<sigma>, Arr \<sigma> \<tau>] (PApp (PVar 1) (PVar 0) :: 'c pterm) \<tau>"
    by (rule has_ptype.PApp[OF pbbk_book_app_head_type pbbk_book_app_argument_type])
  have names: "pterm_in_signature signature (PApp (PVar 1) (PVar 0))" by simp
  show ?thesis unfolding pbbk_book_app_def
    by (rule denote_type[OF typed names pbbk_book_app_environment[OF function_member argument_member]])
qed

theorem pbbk_book_app_represents:
  assumes ft: "has_ptype \<Gamma> F (Arr \<sigma> \<tau>)" and at: "has_ptype \<Gamma> A \<sigma>"
    and fs: "pterm_in_signature signature F" and asig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "denote g (PApp F A) = pbbk_book_app \<sigma> \<tau> (denote g F) (denote g A)"
proof -
  let ?f = "denote g F"
  let ?a = "denote g A"
  let ?h = "pbbk_extend ?a (pbbk_extend ?f (\<lambda>_. undefined))"
  have fm: "?f \<in> domain (Arr \<sigma> \<tau>)" by (rule denote_type[OF ft fs env])
  have am: "?a \<in> domain \<sigma>" by (rule denote_type[OF at asig env])
  have hen: "pbbk_env_typed domain [\<sigma>, Arr \<sigma> \<tau>] ?h" by (rule pbbk_book_app_environment[OF fm am])
  have first_names: "pterm_in_signature signature (PApp F A)" using fs asig by simp
  have second_names: "pterm_in_signature signature (PApp (PVar 1) (PVar 0))" by simp
  have heads: "denote g F = denote ?h (PVar 1)" by (rule sym[OF pbbk_book_app_head_value[OF fm am]])
  have arguments: "denote g A = denote ?h (PVar 0)" by (rule sym[OF pbbk_book_app_argument_value[OF fm am]])
  have equal: "denote g (PApp F A) = denote ?h (PApp (PVar 1) (PVar 0))"
    by (rule denote_application_cong[OF ft at pbbk_book_app_head_type pbbk_book_app_argument_type
      first_names second_names env hen heads arguments])
  show ?thesis using equal by (simp only: pbbk_book_app_def)
qed

theorem pbbk_book_applicative_structure:
  "book_applicative_structure domain pbbk_book_app"
  by unfold_locales (rule pbbk_book_app_type; assumption)

end

end
