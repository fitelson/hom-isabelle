theory Bacon_Source_Relational_Vector_Syntax
  imports Bacon_Source_Relational_Application_Morphism
begin

section \<open>Typed vectors for independent R application\<close>

text \<open>
  For σ₁,…,σₙ∈R, argument vectors satisfy aᵢ∈Dσᵢ.
  Finite curried application ends at t, and the empty vector returns
  its head. Source: Bacon–Dorr Definition 3.3, pp.45–46.
  The raw list operations below are total; their semantic theorems
  separately require an R model and an R-type list. No F-model record,
  total-assignment completion or fullness premise is introduced.
\<close>

definition paper_R_vector_args :: "(otype \<Rightarrow> 'v set) \<Rightarrow> otype list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "paper_R_vector_args D \<sigma>s xs \<longleftrightarrow> list_all2 (\<lambda>\<sigma> a. a \<in> D \<sigma>) \<sigma>s xs"

lemma paper_R_vector_args_Nil [simp]:
  "paper_R_vector_args D [] xs \<longleftrightarrow> xs = []"
  by (cases xs) (simp_all add: paper_R_vector_args_def)

lemma paper_R_vector_args_Cons_Nil [simp]:
  "\<not> paper_R_vector_args D (\<sigma>#\<sigma>s) []"
  by (simp add: paper_R_vector_args_def)

lemma paper_R_vector_args_Cons [simp]:
  "paper_R_vector_args D (\<sigma>#\<sigma>s) (a#xs) \<longleftrightarrow> a \<in> D \<sigma> \<and> paper_R_vector_args D \<sigma>s xs"
  by (simp add: paper_R_vector_args_def)

lemma paper_R_vector_args_length:
  "paper_R_vector_args D \<sigma>s xs \<Longrightarrow> length \<sigma>s = length xs"
  unfolding paper_R_vector_args_def by (rule list_all2_lengthD)

fun paper_R_apply_vector ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    otype list \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v" where
  "paper_R_apply_vector \<Sigma> G D J [] d [] = d"
| "paper_R_apply_vector \<Sigma> G D J [] d (a#xs) = undefined"
| "paper_R_apply_vector \<Sigma> G D J (\<sigma>#\<sigma>s) d [] = undefined"
| "paper_R_apply_vector \<Sigma> G D J (\<sigma>#\<sigma>s) d (a#xs) =
    paper_R_apply_vector \<Sigma> G D J \<sigma>s
      (paper_R_application \<Sigma> G D J \<sigma> (paper_type_vector \<sigma>s Prop) d a) xs"

definition paper_R_map_vector_args ::
  "(otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> otype list \<Rightarrow> 'v list \<Rightarrow> 'w list" where
  "paper_R_map_vector_args h \<sigma>s xs = map (\<lambda>(\<sigma>,a). h \<sigma> a) (zip \<sigma>s xs)"

lemma paper_R_map_vector_args_Nil [simp]:
  "paper_R_map_vector_args h [] xs = []"
  by (simp add: paper_R_map_vector_args_def)

lemma paper_R_map_vector_args_Cons [simp]:
  "paper_R_map_vector_args h (\<sigma>#\<sigma>s) (a#xs) = h \<sigma> a # paper_R_map_vector_args h \<sigma>s xs"
  by (simp add: paper_R_map_vector_args_def)

text \<open>
  The zip-based map is single-pass. Typed argument vectors have the
  same length as their type lists, so none of their entries is truncated.
  Argument typing transports through the independent R homomorphism.
\<close>

theorem paper_R_map_vector_args_type:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and args: "paper_R_vector_args D \<sigma>s xs"
  shows "paper_R_vector_args E \<sigma>s (paper_R_map_vector_args h \<sigma>s xs)"
  using args
proof (induction \<sigma>s arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  obtain a ys where shape: "xs = a#ys" and am: "a \<in> D \<sigma>" and tail: "paper_R_vector_args D \<sigma>s ys"
    using Cons.prems by (cases xs) auto
  have hm: "h \<sigma> a \<in> E \<sigma>"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] am])
  have mapped_tail: "paper_R_vector_args E \<sigma>s (paper_R_map_vector_args h \<sigma>s ys)"
    by (rule Cons.IH[OF tail])
  show ?case by (simp only: shape paper_R_map_vector_args_Cons paper_R_vector_args_Cons;
    rule conjI[OF hm mapped_tail])
qed

end
