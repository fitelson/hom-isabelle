theory Bacon_Source_Propositional
  imports Bacon_Source_Logical_Applications
begin

section \<open>The paper's propositional operations and abbreviations\<close>

text \<open>
  ¬A, A ∧ B, and A ∨ B abbreviate applications of primitive constants.
  Figure 1 defines → as λpq.¬p ∨ q and ↔ as
  λpq.(¬p ∨ q) ∧ (¬q ∨ p) (Bacon–Dorr p. 6).

  Isabelle representation: paper_imp and paper_iff apply those literal
  closed λ-terms.  They are not expanded target PImp constructors.
  Status: the paper basis only; other Figure 1 abbreviations and the
  distinct book basis are outside this file.
\<close>

definition paper_not :: "'c paper_term \<Rightarrow> 'c paper_term" where
  "paper_not A = SApp (SLogical SNot) A"
definition paper_and :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> 'c paper_term" where
  "paper_and A B = SApp (SApp (SLogical SAnd) A) B"
definition paper_or :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> 'c paper_term" where
  "paper_or A B = SApp (SApp (SLogical SOr) A) B"
definition paper_imp_const :: "'c paper_term" where
  "paper_imp_const = SLam Prop (SLam Prop (paper_or (paper_not (SVar 1)) (SVar 0)))"
definition paper_imp :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> 'c paper_term" where
  "paper_imp A B = SApp (SApp paper_imp_const A) B"
definition paper_iff_const :: "'c paper_term" where
  "paper_iff_const = SLam Prop (SLam Prop
    (paper_and (paper_or (paper_not (SVar 1)) (SVar 0))
      (paper_or (paper_not (SVar 0)) (SVar 1))))"
definition paper_iff :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> 'c paper_term" where
  "paper_iff A B = SApp (SApp paper_iff_const A) B"

lemma paper_unary_logical_type:
  assumes head: "paper_logical_type l = Arr \<sigma> \<tau>"
    and arg: "has_stype paper_logical_type \<Gamma> A \<sigma>"
  shows "has_stype paper_logical_type \<Gamma> (SApp (SLogical l) A) \<tau>"
proof -
  have ht: "has_stype paper_logical_type \<Gamma> (SLogical l) (Arr \<sigma> \<tau>)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=l]
    by (simp only: head)
  show ?thesis by (rule has_stype.App[OF ht arg])
qed

lemma paper_binary_logical_type:
  assumes head: "paper_logical_type l = Arr \<sigma> (Arr \<rho> \<tau>)"
    and A: "has_stype paper_logical_type \<Gamma> A \<sigma>"
    and B: "has_stype paper_logical_type \<Gamma> B \<rho>"
  shows "has_stype paper_logical_type \<Gamma> (SApp (SApp (SLogical l) A) B) \<tau>"
  by (rule has_stype.App[OF paper_unary_logical_type[OF head A] B])

lemma paper_not_type:
  assumes A: "has_stype paper_logical_type \<Gamma> A Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_not A) Prop"
  unfolding paper_not_def
  by (rule paper_unary_logical_type[OF paper_logical_type.simps(1) A])

lemma paper_and_type:
  assumes A: "has_stype paper_logical_type \<Gamma> A Prop"
    and B: "has_stype paper_logical_type \<Gamma> B Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_and A B) Prop"
  unfolding paper_and_def
  by (rule paper_binary_logical_type[OF paper_logical_type.simps(2) A B])

lemma paper_or_type:
  assumes A: "has_stype paper_logical_type \<Gamma> A Prop"
    and B: "has_stype paper_logical_type \<Gamma> B Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_or A B) Prop"
  unfolding paper_or_def
  by (rule paper_binary_logical_type[OF paper_logical_type.simps(3) A B])

lemma paper_imp_const_type:
  "has_stype paper_logical_type \<Gamma> paper_imp_const (Arr Prop (Arr Prop Prop))"
  unfolding paper_imp_const_def
  by (intro has_stype.Lam paper_or_type paper_not_type has_stype.Var)
    (simp_all add: lookup_def)

lemma paper_iff_const_type:
  "has_stype paper_logical_type \<Gamma> paper_iff_const (Arr Prop (Arr Prop Prop))"
  unfolding paper_iff_const_def
  by (intro has_stype.Lam paper_and_type paper_or_type paper_not_type has_stype.Var)
    (simp_all add: lookup_def)

lemma paper_imp_type:
  assumes A: "has_stype paper_logical_type \<Gamma> A Prop"
    and B: "has_stype paper_logical_type \<Gamma> B Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_imp A B) Prop"
  unfolding paper_imp_def
  by (rule has_stype.App[OF has_stype.App[OF paper_imp_const_type A] B])

lemma paper_iff_type:
  assumes A: "has_stype paper_logical_type \<Gamma> A Prop"
    and B: "has_stype paper_logical_type \<Gamma> B Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_iff A B) Prop"
  unfolding paper_iff_def
  by (rule has_stype.App[OF has_stype.App[OF paper_iff_const_type A] B])

lemma paper_not_signature[simp]:
  "sterm_in_signature \<Sigma> (paper_not A) = sterm_in_signature \<Sigma> A"
  by (simp add: paper_not_def)
lemma paper_and_signature[simp]:
  "sterm_in_signature \<Sigma> (paper_and A B) =
    (sterm_in_signature \<Sigma> A \<and> sterm_in_signature \<Sigma> B)"
  by (simp add: paper_and_def)
lemma paper_or_signature[simp]:
  "sterm_in_signature \<Sigma> (paper_or A B) =
    (sterm_in_signature \<Sigma> A \<and> sterm_in_signature \<Sigma> B)"
  by (simp add: paper_or_def)
lemma paper_imp_const_signature[simp]: "sterm_in_signature \<Sigma> paper_imp_const"
  by (simp add: paper_imp_const_def)
lemma paper_iff_const_signature[simp]: "sterm_in_signature \<Sigma> paper_iff_const"
  by (simp add: paper_iff_const_def)
lemma paper_imp_signature[simp]:
  "sterm_in_signature \<Sigma> (paper_imp A B) =
    (sterm_in_signature \<Sigma> A \<and> sterm_in_signature \<Sigma> B)"
  by (simp add: paper_imp_def)
lemma paper_iff_signature[simp]:
  "sterm_in_signature \<Sigma> (paper_iff A B) =
    (sterm_in_signature \<Sigma> A \<and> sterm_in_signature \<Sigma> B)"
  by (simp add: paper_iff_def)

section \<open>Propositional templates for PC\<close>

text \<open>
  PC includes each substitution instance of a classical propositional
  tautology (Bacon–Dorr Figure 2, p. 8).

  Isabelle representation: a finite sprop_template has schematic atom labels
  of an arbitrary type.  SPImp and SPIff are template operations, not added
  primitive source constants.  Their instances use the Figure 1 λ-terms.
  sprop_eval is Boolean evaluation of a template, not source denotation.

  Status: independent PC infrastructure with typing/signature preservation.
  Deriving translated template tautologies in pH requires a separate
  propositional/conversion bridge.  No H proof relation is defined here.
\<close>

datatype 'a sprop_template =
    SPAtom 'a
  | SPNot "'a sprop_template"
  | SPAnd "'a sprop_template" "'a sprop_template"
  | SPOr "'a sprop_template" "'a sprop_template"
  | SPImp "'a sprop_template" "'a sprop_template"
  | SPIff "'a sprop_template" "'a sprop_template"

fun sprop_atoms :: "'a sprop_template \<Rightarrow> 'a set" where
  "sprop_atoms (SPAtom a) = {a}"
| "sprop_atoms (SPNot P) = sprop_atoms P"
| "sprop_atoms (SPAnd P Q) = sprop_atoms P \<union> sprop_atoms Q"
| "sprop_atoms (SPOr P Q) = sprop_atoms P \<union> sprop_atoms Q"
| "sprop_atoms (SPImp P Q) = sprop_atoms P \<union> sprop_atoms Q"
| "sprop_atoms (SPIff P Q) = sprop_atoms P \<union> sprop_atoms Q"

fun sprop_eval :: "('a \<Rightarrow> bool) \<Rightarrow> 'a sprop_template \<Rightarrow> bool" where
  "sprop_eval v (SPAtom a) = v a"
| "sprop_eval v (SPNot P) = (\<not> sprop_eval v P)"
| "sprop_eval v (SPAnd P Q) = (sprop_eval v P \<and> sprop_eval v Q)"
| "sprop_eval v (SPOr P Q) = (sprop_eval v P \<or> sprop_eval v Q)"
| "sprop_eval v (SPImp P Q) = (sprop_eval v P \<longrightarrow> sprop_eval v Q)"
| "sprop_eval v (SPIff P Q) = (sprop_eval v P = sprop_eval v Q)"

definition sprop_tautology :: "'a sprop_template \<Rightarrow> bool" where
  "sprop_tautology P \<longleftrightarrow> (\<forall>v. sprop_eval v P)"

fun paper_prop_instance :: "('a \<Rightarrow> 'c paper_term) \<Rightarrow> 'a sprop_template \<Rightarrow> 'c paper_term"
  where
  "paper_prop_instance v (SPAtom a) = v a"
| "paper_prop_instance v (SPNot P) = paper_not (paper_prop_instance v P)"
| "paper_prop_instance v (SPAnd P Q) = paper_and (paper_prop_instance v P) (paper_prop_instance v Q)"
| "paper_prop_instance v (SPOr P Q) = paper_or (paper_prop_instance v P) (paper_prop_instance v Q)"
| "paper_prop_instance v (SPImp P Q) = paper_imp (paper_prop_instance v P) (paper_prop_instance v Q)"
| "paper_prop_instance v (SPIff P Q) = paper_iff (paper_prop_instance v P) (paper_prop_instance v Q)"

lemma paper_prop_instance_type:
  assumes atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> has_stype paper_logical_type \<Gamma> (v a) Prop"
  shows "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
  using atoms
proof (induction P)
  case (SPAtom a)
  show ?case using SPAtom.prems[of a] by simp
next
  case (SPNot P)
  have p: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
    by (rule SPNot.IH; rule SPNot.prems; simp_all)
  show ?case unfolding paper_prop_instance.simps by (rule paper_not_type[OF p])
next
  case (SPAnd P Q)
  have p: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
    by (rule SPAnd.IH(1); rule SPAnd.prems; simp_all)
  have q: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v Q) Prop"
    by (rule SPAnd.IH(2); rule SPAnd.prems; simp_all)
  show ?case unfolding paper_prop_instance.simps by (rule paper_and_type[OF p q])
next
  case (SPOr P Q)
  have p: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
    by (rule SPOr.IH(1); rule SPOr.prems; simp_all)
  have q: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v Q) Prop"
    by (rule SPOr.IH(2); rule SPOr.prems; simp_all)
  show ?case unfolding paper_prop_instance.simps by (rule paper_or_type[OF p q])
next
  case (SPImp P Q)
  have p: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
    by (rule SPImp.IH(1); rule SPImp.prems; simp_all)
  have q: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v Q) Prop"
    by (rule SPImp.IH(2); rule SPImp.prems; simp_all)
  show ?case unfolding paper_prop_instance.simps by (rule paper_imp_type[OF p q])
next
  case (SPIff P Q)
  have p: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
    by (rule SPIff.IH(1); rule SPIff.prems; simp_all)
  have q: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v Q) Prop"
    by (rule SPIff.IH(2); rule SPIff.prems; simp_all)
  show ?case unfolding paper_prop_instance.simps by (rule paper_iff_type[OF p q])
qed

lemma paper_prop_instance_signature_iff:
  "sterm_in_signature \<Sigma> (paper_prop_instance v P) \<longleftrightarrow>
    (\<forall>a\<in>sprop_atoms P. sterm_in_signature \<Sigma> (v a))"
  by (induction P) auto

lemma paper_prop_instance_language:
  assumes atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_prop_instance v P) Prop"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop"
  proof (rule paper_prop_instance_type)
    fix a
    assume member: "a \<in> sprop_atoms P"
    show "has_stype paper_logical_type \<Gamma> (v a) Prop"
      using atoms[OF member] unfolding sterm_in_language_def by (rule conjunct1)
  qed
  have names: "sterm_in_signature \<Sigma> (paper_prop_instance v P)"
  proof (rule iffD2[OF paper_prop_instance_signature_iff], rule ballI)
    fix a
    assume member: "a \<in> sprop_atoms P"
    show "sterm_in_signature \<Sigma> (v a)"
      using atoms[OF member] unfolding sterm_in_language_def by (rule conjunct2)
  qed
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF typed names])
qed

text \<open>
  PC is a property of a well-formed formula A ∈ ℒ(Σ): A instantiates a
  tautological template.  The atom carrier is nat because a template has
  finitely many schematic positions; this does not restrict the arbitrary
  carrier of nonlogical source names.

  Isabelle representation: paper_PC guards the instantiated formula itself.
  Status: an axiom-instance predicate ready for an independent source H;
  no target pH theorem is assumed in its definition.
\<close>

definition paper_PC :: "'c ssignature \<Rightarrow> ctx \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_PC \<Sigma> \<Gamma> A \<longleftrightarrow> sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<and>
    (\<exists>P :: nat sprop_template. \<exists>v. sprop_tautology P \<and> A = paper_prop_instance v P)"

lemma paper_PC_language:
  assumes "paper_PC \<Sigma> \<Gamma> A"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
  using assms unfolding paper_PC_def by (rule conjunct1)

lemma paper_PC_instance:
  fixes P :: "nat sprop_template"
  assumes taut: "sprop_tautology P"
    and atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow>
      sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
  shows "paper_PC \<Sigma> \<Gamma> (paper_prop_instance v P)"
  unfolding paper_PC_def
proof (rule conjI[OF paper_prop_instance_language[OF atoms]])
  show "\<exists>Q :: nat sprop_template. \<exists>w. sprop_tautology Q \<and>
    paper_prop_instance v P = paper_prop_instance w Q"
    by (rule exI[where x=P], rule exI[where x=v], rule conjI[OF taut refl])
qed

end
