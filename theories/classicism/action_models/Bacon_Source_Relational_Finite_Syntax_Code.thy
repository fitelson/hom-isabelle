theory Bacon_Source_Relational_Finite_Syntax_Code
  imports Bacon_Source_Relational_Syntax "HOL-Library.Nat_Bijection"
begin

section \<open>Finite codes retaining the actual constant names\<close>

text \<open>
  A term is coded by a finite list over 'c + nat. Constant names remain
  literal left-hand labels; only types, logical symbols, variable names,
  and constructor tags are coded numerically. Thus this construction does
  not require the ambient constant-name carrier to be countable.
  It is a syntax bound for the cardinal argument in p.51 n.73, not a
  model construction or a bound on arbitrary semantic domains.
\<close>

fun paper_R_type_nat_code :: "otype \<Rightarrow> nat" where
  "paper_R_type_nat_code Ind = 0"
| "paper_R_type_nat_code Prop = 1"
| "paper_R_type_nat_code (Arr \<sigma> \<tau>) =
    2 + prod_encode (paper_R_type_nat_code \<sigma>, paper_R_type_nat_code \<tau>)"

lemma paper_R_type_nat_code_eq [simp]:
  "paper_R_type_nat_code \<sigma> = paper_R_type_nat_code \<tau> \<longleftrightarrow> \<sigma> = \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case Ind
  show ?case by (cases \<tau>) auto
next
  case Prop
  show ?case by (cases \<tau>) auto
next
  case (Arr \<sigma> \<rho>)
  show ?case using Arr.IH by (cases \<tau>) auto
qed

fun paper_R_logical_nat_code :: "paper_logical \<Rightarrow> nat" where
  "paper_R_logical_nat_code SNot = prod_encode (0, 0)"
| "paper_R_logical_nat_code SAnd = prod_encode (1, 0)"
| "paper_R_logical_nat_code SOr = prod_encode (2, 0)"
| "paper_R_logical_nat_code (SAll \<sigma>) = prod_encode (3, paper_R_type_nat_code \<sigma>)"
| "paper_R_logical_nat_code (SEx \<sigma>) = prod_encode (4, paper_R_type_nat_code \<sigma>)"
| "paper_R_logical_nat_code (SEq \<sigma>) = prod_encode (5, paper_R_type_nat_code \<sigma>)"

lemma paper_R_logical_nat_code_eq [simp]:
  "paper_R_logical_nat_code l = paper_R_logical_nat_code k \<longleftrightarrow> l = k"
  by (cases l; cases k) simp_all

fun paper_R_finite_syntax_code :: "'c paper_named_term \<Rightarrow> ('c + nat) list" where
  "paper_R_finite_syntax_code (NVar n) = [Inr 0, Inr n]"
| "paper_R_finite_syntax_code (NConst c \<sigma>) = [Inr 1, Inl c, Inr (paper_R_type_nat_code \<sigma>)]"
| "paper_R_finite_syntax_code (NLogical l) = [Inr 2, Inr (paper_R_logical_nat_code l)]"
| "paper_R_finite_syntax_code (NApp F A) =
    [Inr 3, Inr (length (paper_R_finite_syntax_code F))] @
      paper_R_finite_syntax_code F @ paper_R_finite_syntax_code A"
| "paper_R_finite_syntax_code (NLam n A) =
    [Inr 4, Inr n] @ paper_R_finite_syntax_code A"

lemma paper_R_finite_syntax_code_reflects:
  assumes equal: "paper_R_finite_syntax_code A = paper_R_finite_syntax_code B"
  shows "A = B"
  using equal
proof (induction A arbitrary: B)
  case (NVar n)
  then show ?case by (cases B) auto
next
  case (NConst c \<sigma>)
  then show ?case by (cases B) auto
next
  case (NLogical l)
  then show ?case by (cases B) auto
next
  case (NApp F A)
  note subterms = NApp.IH
  note code_equal = NApp.prems
  show ?case
  proof (cases B)
    case (NApp H C)
    have lengths: "length (paper_R_finite_syntax_code F) = length (paper_R_finite_syntax_code H)"
      and tails: "paper_R_finite_syntax_code F @ paper_R_finite_syntax_code A =
        paper_R_finite_syntax_code H @ paper_R_finite_syntax_code C"
      using code_equal unfolding NApp by simp_all
    have pieces: "paper_R_finite_syntax_code F = paper_R_finite_syntax_code H \<and>
        paper_R_finite_syntax_code A = paper_R_finite_syntax_code C"
      using tails lengths by simp
    have left: "paper_R_finite_syntax_code F = paper_R_finite_syntax_code H"
      and right: "paper_R_finite_syntax_code A = paper_R_finite_syntax_code C"
      using pieces by blast+
    show ?thesis using subterms(1)[OF left] subterms(2)[OF right] unfolding NApp by simp
  qed (use code_equal in auto)
next
  case (NLam n A)
  then show ?case by (cases B) auto
qed

lemma paper_R_finite_syntax_code_injective:
  "inj paper_R_finite_syntax_code"
  by (rule injI, rule paper_R_finite_syntax_code_reflects)

lemma paper_R_finite_syntax_code_labels:
  assumes names: "named_in_signature \<Sigma> A"
  shows "set (paper_R_finite_syntax_code A) \<subseteq> (\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)"
  using names by (induction A) auto

lemma paper_R_finite_syntax_code_lists:
  assumes names: "named_in_signature \<Sigma> A"
  shows "paper_R_finite_syntax_code A \<in> lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))"
  using paper_R_finite_syntax_code_labels[OF names] by (auto simp: in_lists_conv_set)

end
