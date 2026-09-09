theory Bacon_Source_Relational_Universal_Closure_Language
  imports Bacon_Source_Relational_Universal_Closure_Syntax
    Bacon_Source_Relational_Assignment_Extension
begin

section \<open>A closed universal prefix for each R formula\<close>

lemma paper_R_language_closed_universal:
  assumes language: "paper_R_in_language \<Sigma> G P Prop"
  obtains ns where "distinct ns" "set ns = named_fv P"
    "list_all paper_R_type (map G ns)"
    "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    "named_fv (paper_R_all_vec G ns P) = {}"
proof -
  obtain ns where cover: "set ns = named_fv P" and distinct: "distinct ns"
    using finite_distinct_list[OF named_fv_finite[of P]] by blast
  have types: "paper_R_type (G n)" if "n \<in> set ns" for n
    by (rule paper_R_language_fv_type[OF language]; use that in \<open>simp only: cover\<close>)
  have binders: "list_all paper_R_type (map G ns)" using types by (simp add: list_all_iff)
  have whole: "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    by (rule paper_R_all_vec_language[OF language binders])
  have closed: "named_fv (paper_R_all_vec G ns P) = {}"
    by (simp only: paper_R_all_vec_fv cover; simp)
  show thesis by (rule that[OF distinct cover binders whole closed])
qed

text \<open>
  The formula need not belong to a theory. Its finite free-variable
  set supplies the prefix, and its typing supplies all binder types.
  No consistency, richness or semantic premise is needed. This is
  the syntactic closure used to reduce open nonmembership to the
  sentence-set form of Theorem 3.2.
\<close>

end
