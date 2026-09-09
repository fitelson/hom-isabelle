theory Bacon_Book_Typed_Name_Map
  imports Bacon_Book_Environment_Development.Bacon_Book_Constant_Renaming
begin

section \<open>Changing a constant name according to its declared occurrence type\<close>

fun book_typed_name_map :: "(otype \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('d,'l) named_term" where
  "book_typed_name_map \<rho> (NVar n) = NVar n"
| "book_typed_name_map \<rho> (NConst c \<sigma>) = NConst (\<rho> \<sigma> c) \<sigma>"
| "book_typed_name_map \<rho> (NLogical l) = NLogical l"
| "book_typed_name_map \<rho> (NApp F A) = NApp (book_typed_name_map \<rho> F) (book_typed_name_map \<rho> A)"
| "book_typed_name_map \<rho> (NLam n A) = NLam n (book_typed_name_map \<rho> A)"

lemma book_typed_name_map_id:
  "book_typed_name_map (\<lambda>\<sigma> c. c) A = A"
  by (induction A) simp_all

lemma book_typed_name_map_comp:
  "book_typed_name_map \<pi> (book_typed_name_map \<rho> A) = book_typed_name_map (\<lambda>\<sigma> c. \<pi> \<sigma> (\<rho> \<sigma> c)) A"
  by (induction A) simp_all

lemma book_typed_name_map_uniform:
  "book_typed_name_map (\<lambda>_. f) A = book_constant_rename f A"
  by (induction A) simp_all

lemma book_typed_name_map_fv:
  "named_fv (book_typed_name_map \<rho> A) = named_fv A"
  by (induction A) simp_all

lemma book_typed_name_map_vars:
  "named_vars (book_typed_name_map \<rho> A) = named_vars A"
  by (induction A) simp_all

lemma book_typed_name_map_subst:
  "book_typed_name_map \<rho> (named_subst n B A) =
    named_subst n (book_typed_name_map \<rho> B) (book_typed_name_map \<rho> A)"
  by (induction A) (simp_all split: if_splits)

lemma book_typed_name_map_free_for:
  "named_free_for (book_typed_name_map \<rho> B) n (book_typed_name_map \<rho> A) = named_free_for B n A"
  by (induction A) (simp_all add: book_typed_name_map_fv)

lemma book_typed_name_map_logicals:
  "named_logical_occurrences (book_typed_name_map \<rho> A) = named_logical_occurrences A"
  by (induction A) simp_all

theorem book_typed_name_map_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_ntype L G (book_typed_name_map \<rho> A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case Var
  show ?case by (simp only: book_typed_name_map.simps; rule has_ntype.Var)
next
  case Const
  show ?case by (simp only: book_typed_name_map.simps; rule has_ntype.Const)
next
  case Logical
  show ?case by (simp only: book_typed_name_map.simps; rule has_ntype.Logical)
next
  case App
  show ?case by (simp only: book_typed_name_map.simps; rule has_ntype.App[OF App.IH])
next
  case Lam
  show ?case by (simp only: book_typed_name_map.simps; rule has_ntype.Lam[OF Lam.IH])
qed

lemma book_typed_name_map_signature:
  assumes names: "named_in_signature \<Sigma> A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "named_in_signature \<Omega> (book_typed_name_map \<rho> A)"
  using names by (induction A) (auto intro: maps)

theorem book_typed_name_map_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "book_in_language L \<Lambda> \<Omega> G (book_typed_name_map \<rho> A) \<tau>"
proof -
  have typed: "has_ntype L G (book_typed_name_map \<rho> A) \<tau>"
    by (rule book_typed_name_map_type[OF book_language_type[OF language]])
  have names: "named_in_signature \<Omega> (book_typed_name_map \<rho> A)"
    by (rule book_typed_name_map_signature[OF book_language_signature[OF language] maps])
  have logicals: "named_logical_occurrences (book_typed_name_map \<rho> A) \<subseteq> \<Lambda>"
    by (simp only: book_typed_name_map_logicals; rule book_language_logical_occurrences[OF language])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

theorem book_typed_name_map_roundtrip:
  assumes names: "named_in_signature \<Sigma> A"
    and inverse: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<pi> \<sigma> (\<rho> \<sigma> c) = c"
  shows "book_typed_name_map \<pi> (book_typed_name_map \<rho> A) = A"
  using names by (induction A) (auto intro: inverse)

text \<open>
  The symbol c:σ is sent to ρσ(c):σ. Variables, binders, logical
  symbols and their types stay fixed. The raw term operation is
  independent of H/C and of the choice of logical basis. Inverse
  equations are required only on the declared constants, not every
  element of the ambient carrier. This permits type-indexed, old-name-
  preserving transport in the canonical language construction.
\<close>

end
