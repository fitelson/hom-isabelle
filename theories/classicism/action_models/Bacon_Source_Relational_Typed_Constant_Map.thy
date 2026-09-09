theory Bacon_Source_Relational_Typed_Constant_Map
  imports Bacon_Source_Relational_Constant_Map
begin

section \<open>Constant-name transport indexed by the occurrence type\<close>

fun paper_R_typed_constant_map ::
  "(otype \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('d,'l) named_term" where
  "paper_R_typed_constant_map \<rho> (NVar n) = NVar n"
| "paper_R_typed_constant_map \<rho> (NConst c \<sigma>) = NConst (\<rho> \<sigma> c) \<sigma>"
| "paper_R_typed_constant_map \<rho> (NLogical l) = NLogical l"
| "paper_R_typed_constant_map \<rho> (NApp F A) =
    NApp (paper_R_typed_constant_map \<rho> F) (paper_R_typed_constant_map \<rho> A)"
| "paper_R_typed_constant_map \<rho> (NLam n A) = NLam n (paper_R_typed_constant_map \<rho> A)"

lemma paper_R_typed_constant_map_id:
  "paper_R_typed_constant_map (\<lambda>\<sigma> c. c) A = A"
  by (induction A) simp_all

lemma paper_R_typed_constant_map_comp:
  "paper_R_typed_constant_map \<pi> (paper_R_typed_constant_map \<rho> A) =
    paper_R_typed_constant_map (\<lambda>\<sigma> c. \<pi> \<sigma> (\<rho> \<sigma> c)) A"
  by (induction A) simp_all

lemma paper_R_typed_constant_map_uniform:
  "paper_R_typed_constant_map (\<lambda>_. f) A = paper_R_constant_map f A"
  by (induction A) simp_all

lemma paper_R_typed_constant_map_fv:
  "named_fv (paper_R_typed_constant_map \<rho> A) = named_fv A"
  by (induction A) simp_all

lemma paper_R_typed_constant_map_vars:
  "named_vars (paper_R_typed_constant_map \<rho> A) = named_vars A"
  by (induction A) simp_all

lemma paper_R_typed_constant_map_signature_cong:
  assumes names: "named_in_signature \<Sigma> A"
    and agree: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c = \<pi> \<sigma> c"
  shows "paper_R_typed_constant_map \<rho> A = paper_R_typed_constant_map \<pi> A"
  using names by (induction A) (auto intro: agree)

theorem paper_R_typed_constant_map_type:
  assumes typed: "paper_R_has_type G A \<tau>"
  shows "paper_R_has_type G (paper_R_typed_constant_map \<rho> A) \<tau>"
  using typed
proof (induction rule: paper_R_has_type.induct)
  case (Var n)
  show ?case by (simp only: paper_R_typed_constant_map.simps;
    rule paper_R_has_type.Var[where G=G and n=n, OF Var.hyps])
next
  case Const
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule paper_R_has_type.Const[OF Const.hyps])
next
  case Logical
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule paper_R_has_type.Logical[OF Logical.hyps])
next
  case App
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule paper_R_has_type.App[OF App.IH])
next
  case Lam
  show ?case by (simp only: paper_R_typed_constant_map.simps;
    rule paper_R_has_type.Lam[OF Lam.IH Lam.hyps(2,3)])
qed

lemma paper_R_typed_constant_map_signature:
  assumes names: "named_in_signature \<Sigma> A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "named_in_signature \<Omega> (paper_R_typed_constant_map \<rho> A)"
  using names by (induction A) (auto intro: maps)

theorem paper_R_typed_constant_map_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> \<Omega> \<sigma>"
  shows "paper_R_in_language \<Omega> G (paper_R_typed_constant_map \<rho> A) \<tau>"
proof -
  have typed: "paper_R_has_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
    using language unfolding paper_R_in_language_def by blast+
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_typed_constant_map_type[OF typed]
      paper_R_typed_constant_map_signature[OF names maps]])
qed

text \<open>
  Only the name at NConst(c,σ) changes, to ρσ(c); its occurrence
  type σ is retained. The same bare name may therefore be renamed
  differently at different types. All variables, binders and logical
  symbols remain literal. No injection, richness or domain assumption
  is needed for these forward syntactic facts.

  Source role: typed nonlogical signatures in §1.1 and prospective
  finite-formula signature compression. This leaf does not assert
  H/C proof transport, model transport or compression of an infinite theory.
\<close>

end
