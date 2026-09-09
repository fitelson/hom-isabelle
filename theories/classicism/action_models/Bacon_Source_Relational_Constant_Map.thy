theory Bacon_Source_Relational_Constant_Map
  imports Bacon_Source_Relational_Conversion
begin

section \<open>Change only the carrier of nonlogical constant names\<close>

text \<open>
  The datatype map sends c:σ to f(c):σ and leaves variables, their
  stock G, binders and logical symbols unchanged. Source role: the
  expanded language in Theorem 3.2, p.45 n.64. Both name carriers
  are arbitrary; forward transport requires no injection or richness.
\<close>

abbreviation paper_R_constant_map :: "('c \<Rightarrow> 'd) \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('d,'l) named_term" where
  "paper_R_constant_map f \<equiv> map_named_term f id"

lemma paper_R_constant_map_simps [simp]:
  "paper_R_constant_map f (NVar n) = NVar n"
  "paper_R_constant_map f (NConst c \<sigma>) = NConst (f c) \<sigma>"
  "paper_R_constant_map f (NLogical l) = NLogical l"
  "paper_R_constant_map f (NApp A B) = NApp (paper_R_constant_map f A) (paper_R_constant_map f B)"
  "paper_R_constant_map f (NLam n A) = NLam n (paper_R_constant_map f A)"
  by simp_all

lemma paper_R_constant_map_id: "paper_R_constant_map id A = A"
  by (induction A) simp_all

lemma paper_R_constant_map_comp:
  "paper_R_constant_map g (paper_R_constant_map f A) = paper_R_constant_map (g \<circ> f) A"
  by (induction A) simp_all

lemma paper_R_constant_map_fv: "named_fv (paper_R_constant_map f A) = named_fv A"
  by (induction A) simp_all

lemma paper_R_constant_map_vars: "named_vars (paper_R_constant_map f A) = named_vars A"
  by (induction A) simp_all

theorem paper_R_constant_map_type:
  assumes typed: "paper_R_has_type G A \<tau>"
  shows "paper_R_has_type G (paper_R_constant_map f A) \<tau>"
  using typed
proof (induction rule: paper_R_has_type.induct)
  case (Var n)
  show ?case by (simp only: paper_R_constant_map_simps; rule paper_R_has_type.Var[where G=G and n=n, OF Var.hyps])
next
  case (Const \<sigma> c)
  show ?case by (simp only: paper_R_constant_map_simps; rule paper_R_has_type.Const[OF Const.hyps])
next
  case (Logical l)
  show ?case by (simp only: paper_R_constant_map_simps; rule paper_R_has_type.Logical[OF Logical.hyps])
next
  case (App F \<sigma> \<tau> B)
  show ?case by (simp only: paper_R_constant_map_simps; rule paper_R_has_type.App[OF App.IH])
next
  case (Lam B \<tau> n)
  show ?case by (simp only: paper_R_constant_map_simps; rule paper_R_has_type.Lam[OF Lam.IH Lam.hyps(2,3)])
qed

lemma paper_R_constant_map_signature:
  assumes names: "named_in_signature \<Sigma> A"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "named_in_signature \<Omega> (paper_R_constant_map f A)"
  using names by (induction A) (auto intro: maps)

lemma paper_R_constant_map_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "paper_R_in_language \<Omega> G (paper_R_constant_map f A) \<tau>"
proof -
  have typed: "paper_R_has_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
    using language unfolding paper_R_in_language_def by blast+
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_constant_map_type[OF typed] paper_R_constant_map_signature[OF names maps]])
qed

end
