theory Bacon_Source_Relational_Admitted_Terms_Countable
  imports Bacon_Source_Relational_Syntax
    Bacon_Parametric_Countable_Development.Bacon_Parametric_Countable_Coding
begin

section \<open>Count finite syntax over a countable set of admitted names\<close>

text \<open>
  Only C⊆'c is assumed countable, not the ambient name carrier 'c.
  A finite tree records every AST constructor, variable and binder name,
  constant type, and logical symbol. The existing pHct_tree and its
  type-label injection are reused purely as codes for finite syntax;
  no parametric F theoremhood, consistency or model theorem is used.
  Source role: the countable-language clause of Theorem 3.2, p.45 n.64.
\<close>

fun paper_R_logical_count_tree :: "paper_logical \<Rightarrow> pHct_tree" where
  "paper_R_logical_count_tree SNot = pHct_Atom 0"
| "paper_R_logical_count_tree SAnd = pHct_Atom 1"
| "paper_R_logical_count_tree SOr = pHct_Atom 2"
| "paper_R_logical_count_tree (SAll \<sigma>) = pHct_Unary 3 (pHct_Atom (pHct_type_code \<sigma>))"
| "paper_R_logical_count_tree (SEx \<sigma>) = pHct_Unary 4 (pHct_Atom (pHct_type_code \<sigma>))"
| "paper_R_logical_count_tree (SEq \<sigma>) = pHct_Unary 5 (pHct_Atom (pHct_type_code \<sigma>))"

lemma paper_R_logical_count_tree_eq [simp]:
  "paper_R_logical_count_tree l = paper_R_logical_count_tree k \<longleftrightarrow> l = k"
  by (cases l; cases k; simp)

fun paper_R_named_count_tree :: "('c \<Rightarrow> nat) \<Rightarrow> 'c paper_named_term \<Rightarrow> pHct_tree" where
  "paper_R_named_count_tree k (NVar n) = pHct_Unary 0 (pHct_Atom n)"
| "paper_R_named_count_tree k (NConst c \<sigma>) = pHct_Binary 1 (pHct_Atom (k c)) (pHct_Atom (pHct_type_code \<sigma>))"
| "paper_R_named_count_tree k (NLogical l) = pHct_Unary 2 (paper_R_logical_count_tree l)"
| "paper_R_named_count_tree k (NApp F A) = pHct_Binary 3 (paper_R_named_count_tree k F) (paper_R_named_count_tree k A)"
| "paper_R_named_count_tree k (NLam n A) = pHct_Binary 4 (pHct_Atom n) (paper_R_named_count_tree k A)"

lemma paper_R_named_count_tree_reflects:
  assumes injective: "inj_on k C" and first: "named_in_signature (\<lambda>_. C) A"
    and second: "named_in_signature (\<lambda>_. C) B" and equal: "paper_R_named_count_tree k A = paper_R_named_count_tree k B"
  shows "A = B"
  using first second equal
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case using NVar.prems by (cases B) auto
next
  case (NConst c \<sigma>)
  show ?case using NConst.prems injective by (cases B) (auto simp: inj_on_def)
next
  case (NLogical l)
  show ?case using NLogical.prems by (cases B) auto
next
  case (NApp F A)
  show ?case using NApp.prems NApp.IH by (cases B) auto
next
  case (NLam n A)
  show ?case using NLam.prems NLam.IH by (cases B) auto
qed

theorem paper_R_names_terms_countable:
  assumes names: "countable C"
  shows "countable {A :: 'c paper_named_term. named_in_signature (\<lambda>_. C) A}"
proof -
  obtain k :: "'c \<Rightarrow> nat" where injective: "inj_on k C" by (rule countableE[OF names])
  show ?thesis
  proof (rule countableI'[where f="paper_R_named_count_tree k"], rule inj_onI)
    fix A B
    assume first: "A \<in> {A :: 'c paper_named_term. named_in_signature (\<lambda>_. C) A}"
      and second: "B \<in> {A :: 'c paper_named_term. named_in_signature (\<lambda>_. C) A}"
      and equal: "paper_R_named_count_tree k A = paper_R_named_count_tree k B"
    have al: "named_in_signature (\<lambda>_. C) A" and bl: "named_in_signature (\<lambda>_. C) B" using first second by simp_all
    show "A = B" by (rule paper_R_named_count_tree_reflects[OF injective al bl equal])
  qed
qed

lemma paper_R_signature_names_in_union:
  assumes names: "named_in_signature \<Sigma> A"
  shows "named_in_signature (\<lambda>_. \<Union>\<rho>. \<Sigma> \<rho>) A"
  using names by (induction A) auto

theorem paper_R_admitted_terms_countable:
  assumes names: "countable (\<Union>\<rho>. \<Sigma> \<rho>)"
  shows "countable {A :: 'c paper_named_term. named_in_signature \<Sigma> A}"
proof -
  have subset: "{A :: 'c paper_named_term. named_in_signature \<Sigma> A} \<subseteq>
      {A. named_in_signature (\<lambda>_. \<Union>\<rho>. \<Sigma> \<rho>) A}"
    using paper_R_signature_names_in_union by blast
  show ?thesis by (rule countable_subset[OF subset paper_R_names_terms_countable[OF names]])
qed

end
