theory Bacon_Source_BBK_Vector_Application
  imports Bacon_Source_BBK_Application_Morphism Bacon_Source_Relational_Types
begin

section \<open>Typed argument vectors and finite curried application\<close>

text \<open>
  For d∈Mσ₁→⋯→σₙ→t and aᵢ∈Mσᵢ, successively apply d
  to a₁,…,aₙ; the result lies in Mₜ. The empty vector returns
  d itself. Source: Bacon–Dorr Definition 3.3, pp.45–46.

  Representation: two lists carry the types and values, with list_all2
  enforcing equal lengths and every domain guard. The total application
  function is undefined on arity mismatches. The recursion uses the
  reconstructed application operation, not an additional model field.
  These are full-F operations. No R-language or R-model bridge follows
  merely from placing R guards on the argument-type list.
\<close>

definition paper_bbk_vector_args ::
  "('c,'v) paper_bbk_model_data \<Rightarrow> otype list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "paper_bbk_vector_args M \<sigma>s xs \<longleftrightarrow> list_all2 (\<lambda>\<sigma> a. a \<in> paper_bbk_domain M \<sigma>) \<sigma>s xs"

lemma paper_bbk_vector_args_Nil [simp]:
  "paper_bbk_vector_args M [] xs \<longleftrightarrow> xs = []"
  by (cases xs) (simp_all add: paper_bbk_vector_args_def)

lemma paper_bbk_vector_args_Cons_Nil [simp]:
  "\<not> paper_bbk_vector_args M (\<sigma>#\<sigma>s) []"
  by (simp add: paper_bbk_vector_args_def)

lemma paper_bbk_vector_args_Cons [simp]:
  "paper_bbk_vector_args M (\<sigma>#\<sigma>s) (a#xs) \<longleftrightarrow>
    a \<in> paper_bbk_domain M \<sigma> \<and> paper_bbk_vector_args M \<sigma>s xs"
  by (simp add: paper_bbk_vector_args_def)

lemma paper_bbk_vector_args_length:
  assumes args: "paper_bbk_vector_args M \<sigma>s xs"
  shows "length \<sigma>s = length xs"
  by (rule list_all2_lengthD[OF args[unfolded paper_bbk_vector_args_def]])

fun paper_bbk_apply_vector ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow>
    otype list \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v" where
  "paper_bbk_apply_vector \<Sigma> G M [] d [] = d"
| "paper_bbk_apply_vector \<Sigma> G M [] d (a#xs) = undefined"
| "paper_bbk_apply_vector \<Sigma> G M (\<sigma>#\<sigma>s) d [] = undefined"
| "paper_bbk_apply_vector \<Sigma> G M (\<sigma>#\<sigma>s) d (a#xs) =
    paper_bbk_apply_vector \<Sigma> G M \<sigma>s
      (paper_bbk_application \<Sigma> G M \<sigma> (paper_type_vector \<sigma>s Prop) d a) xs"

theorem paper_bbk_apply_vector_type:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and head: "d \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    and args: "paper_bbk_vector_args M \<sigma>s xs"
  shows "paper_bbk_apply_vector \<Sigma> G M \<sigma>s d xs \<in> paper_bbk_domain M Prop"
  using head args
proof (induction \<sigma>s arbitrary: d xs)
  case Nil
  have empty: "xs = []" using Nil.prems(2) by simp
  show ?case using Nil.prems(1) by (simp only: empty paper_bbk_apply_vector.simps paper_type_vector.simps)
next
  case (Cons \<sigma> \<sigma>s)
  obtain a ys where shape: "xs = a#ys" and am: "a \<in> paper_bbk_domain M \<sigma>"
    and tail: "paper_bbk_vector_args M \<sigma>s ys"
    using Cons.prems(2) by (cases xs) auto
  have dt: "d \<in> paper_bbk_domain M (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using Cons.prems(1) by (simp only: paper_type_vector.simps)
  have applied: "paper_bbk_application \<Sigma> G M \<sigma> (paper_type_vector \<sigma>s Prop) d a \<in>
      paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    by (rule paper_bbk_application_type[OF valid dt am])
  have result: "paper_bbk_apply_vector \<Sigma> G M \<sigma>s
      (paper_bbk_application \<Sigma> G M \<sigma> (paper_type_vector \<sigma>s Prop) d a) ys \<in> paper_bbk_domain M Prop"
    by (rule Cons.IH[OF applied tail])
  show ?case by (simp only: shape paper_bbk_apply_vector.simps; rule result)
qed

section \<open>Transporting each argument at its own type\<close>

text \<open>
  The transported vector is ⟨hσ₁(a₁),…,hσₙ(aₙ)⟩. A zip
  specifies this operation on total lists; the typed-vector premise
  prevents truncation from discarding an argument in any claimed result.
  Different source and target HOL value carriers are permitted.
\<close>

definition paper_bbk_map_vector_args ::
  "(otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> otype list \<Rightarrow> 'v list \<Rightarrow> 'w list" where
  "paper_bbk_map_vector_args h \<sigma>s xs = map (\<lambda>(\<sigma>,a). h \<sigma> a) (zip \<sigma>s xs)"

lemma paper_bbk_map_vector_args_Nil [simp]:
  "paper_bbk_map_vector_args h [] xs = []"
  by (simp add: paper_bbk_map_vector_args_def)

lemma paper_bbk_map_vector_args_Cons [simp]:
  "paper_bbk_map_vector_args h (\<sigma>#\<sigma>s) (a#xs) =
    h \<sigma> a # paper_bbk_map_vector_args h \<sigma>s xs"
  by (simp add: paper_bbk_map_vector_args_def)

theorem paper_bbk_map_vector_args_type:
  assumes morphism: "paper_bbk_data_morphism \<Sigma> G M N h"
    and args: "paper_bbk_vector_args M \<sigma>s xs"
  shows "paper_bbk_vector_args N \<sigma>s (paper_bbk_map_vector_args h \<sigma>s xs)"
  using args
proof (induction \<sigma>s arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  obtain a ys where shape: "xs = a#ys" and am: "a \<in> paper_bbk_domain M \<sigma>"
    and tail: "paper_bbk_vector_args M \<sigma>s ys"
    using Cons.prems by (cases xs) auto
  have hm: "h \<sigma> a \<in> paper_bbk_domain N \<sigma>"
    by (rule paper_bbk_homomorphism_domain[OF paper_bbk_data_morphism_raw[OF morphism] am])
  have mapped_tail: "paper_bbk_vector_args N \<sigma>s (paper_bbk_map_vector_args h \<sigma>s ys)"
    by (rule Cons.IH[OF tail])
  show ?case by (simp only: shape paper_bbk_map_vector_args_Cons paper_bbk_vector_args_Cons;
    rule conjI[OF hm mapped_tail])
qed

section \<open>Homomorphisms commute with every finite application vector\<close>

text \<open>
  hₜ(d a₁⋯aₙ)=(hσ₁→⋯→σₙ→t(d)) hσ₁(a₁)⋯hσₙ(aₙ).
  This follows by induction from application preservation (p.49).
  The intermediate head remains typed at each remaining arrow vector.
  No relation-intension, injectivity, fullness or valuation-preservation
  assertion is made here.
\<close>

theorem paper_bbk_apply_vector_morphism:
  fixes M :: "('c,'v) paper_bbk_model_data"
    and N :: "('c,'w) paper_bbk_model_data"
  assumes morphism: "paper_bbk_data_morphism \<Sigma> G M N h"
    and head: "d \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    and args: "paper_bbk_vector_args M \<sigma>s xs"
  shows "h Prop (paper_bbk_apply_vector \<Sigma> G M \<sigma>s d xs) =
    paper_bbk_apply_vector \<Sigma> G N \<sigma>s
      (h (paper_type_vector \<sigma>s Prop) d) (paper_bbk_map_vector_args h \<sigma>s xs)"
  using head args
proof (induction \<sigma>s arbitrary: d xs)
  case Nil
  have empty: "xs = []" using Nil.prems(2) by simp
  show ?case by (simp only: empty paper_type_vector.simps paper_bbk_apply_vector.simps paper_bbk_map_vector_args_Nil)
next
  case (Cons \<sigma> \<sigma>s)
  obtain a ys where shape: "xs = a#ys" and am: "a \<in> paper_bbk_domain M \<sigma>"
    and tail: "paper_bbk_vector_args M \<sigma>s ys"
    using Cons.prems(2) by (cases xs) auto
  have dt: "d \<in> paper_bbk_domain M (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using Cons.prems(1) by (simp only: paper_type_vector.simps)
  let ?b = "paper_bbk_application \<Sigma> G M \<sigma> (paper_type_vector \<sigma>s Prop) d a"
  have bt: "?b \<in> paper_bbk_domain M (paper_type_vector \<sigma>s Prop)"
    by (rule paper_bbk_application_type[OF paper_bbk_data_morphism_source[OF morphism] dt am])
  have step: "h (paper_type_vector \<sigma>s Prop) ?b =
    paper_bbk_application \<Sigma> G N \<sigma> (paper_type_vector \<sigma>s Prop)
      (h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d) (h \<sigma> a)"
    by (rule paper_bbk_application_morphism[OF morphism dt am])
  have induction_step: "h Prop (paper_bbk_apply_vector \<Sigma> G M \<sigma>s ?b ys) =
    paper_bbk_apply_vector \<Sigma> G N \<sigma>s
      (h (paper_type_vector \<sigma>s Prop) ?b) (paper_bbk_map_vector_args h \<sigma>s ys)"
    by (rule Cons.IH[OF bt tail])
  show ?case by (simp only: shape paper_bbk_apply_vector.simps paper_bbk_map_vector_args_Cons
    paper_type_vector.simps induction_step step)
qed

end
