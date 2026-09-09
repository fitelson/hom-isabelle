theory Bacon_Parametric_Fresh_Constant
  imports Bacon_Parametric_Local_Derivability
begin

section \<open>Replacing a fresh constant by a typed term\<close>

text \<open>
  For a constant c:σ and a term N:σ, write M[N/c] for capture-avoiding
  replacement of c.  A fresh constant can be turned into an eigenvariable
  by first shifting the free variables and then substituting the new
  variable for c.  These are the syntactic operations needed in the
  consistency argument of Bacon--Dorr, p.45 n.64, and Bacon, Chapter 15,
  Proposition 15.4.

  Isabelle representation.  Only the typed pair (c,σ) is replaced.  Under
  λ, ∀, or ∃, the replacement term is shifted.  The name carrier remains
  arbitrary.  The disjoint PHOriginal/PHWitness constructors, not an
  enumeration or an unused old name, establish freshness below.

  Status.  This file proves the structural replacement and abstraction
  facts and the local deduction step after abstraction.  Preservation of
  pH proofs by open-term constant replacement and the eigenvariable
  elimination theorem are still needed before fresh witness consistency
  can be concluded.  Neither is assumed as an axiom or admissibility field.
\<close>

fun pconst_subst :: "'c \<Rightarrow> otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "pconst_subst c \<sigma> N (PVar n) = PVar n"
| "pconst_subst c \<sigma> N (PConst d \<tau>) = (if c = d \<and> \<sigma> = \<tau> then N else PConst d \<tau>)"
| "pconst_subst c \<sigma> N (PApp F A) = PApp (pconst_subst c \<sigma> N F) (pconst_subst c \<sigma> N A)"
| "pconst_subst c \<sigma> N (PLam \<tau> M) = PLam \<tau> (pconst_subst c \<sigma> (pshift N) M)"
| "pconst_subst c \<sigma> N (PEq \<tau> A B) = PEq \<tau> (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
| "pconst_subst c \<sigma> N (PNeg A) = PNeg (pconst_subst c \<sigma> N A)"
| "pconst_subst c \<sigma> N (PConj A B) = PConj (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
| "pconst_subst c \<sigma> N (PDisj A B) = PDisj (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
| "pconst_subst c \<sigma> N (PImp A B) = PImp (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
| "pconst_subst c \<sigma> N (PForall \<tau> A) = PForall \<tau> (pconst_subst c \<sigma> (pshift N) A)"
| "pconst_subst c \<sigma> N (PExists \<tau> A) = PExists \<tau> (pconst_subst c \<sigma> (pshift N) A)"

lemma pconst_subst_same[simp]: "pconst_subst c \<sigma> N (PConst c \<sigma>) = N"
  by simp

lemma pconst_subst_type:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and replacement: "has_ptype \<Gamma> N \<sigma>"
  shows "has_ptype \<Gamma> (pconst_subst c \<sigma> N M) \<tau>"
  using typed replacement
proof (induction arbitrary: N rule: has_ptype.induct)
  case (PLam \<rho> \<Gamma> M \<tau>)
  have shifted: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>"
    by (rule pshift_preserves_typing[OF PLam.prems])
  have body: "has_ptype (\<rho> # \<Gamma>) (pconst_subst c \<sigma> (pshift N) M) \<tau>"
    by (rule PLam.IH[where N="pshift N", OF shifted])
  show ?case by (simp only: pconst_subst.simps) (rule has_ptype.PLam[OF body])
next
  case (PForall \<rho> \<Gamma> A)
  have shifted: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>"
    by (rule pshift_preserves_typing[OF PForall.prems])
  have body: "has_ptype (\<rho> # \<Gamma>) (pconst_subst c \<sigma> (pshift N) A) Prop"
    by (rule PForall.IH[where N="pshift N", OF shifted])
  show ?case by (simp only: pconst_subst.simps) (rule has_ptype.PForall[OF body])
next
  case (PExists \<rho> \<Gamma> A)
  have shifted: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>"
    by (rule pshift_preserves_typing[OF PExists.prems])
  have body: "has_ptype (\<rho> # \<Gamma>) (pconst_subst c \<sigma> (pshift N) A) Prop"
    by (rule PExists.IH[where N="pshift N", OF shifted])
  show ?case by (simp only: pconst_subst.simps) (rule has_ptype.PExists[OF body])
qed (auto split: if_splits)

lemma pconst_subst_signature:
  assumes sigM: "pterm_in_signature \<Sigma> M" and sigN: "pterm_in_signature \<Sigma> N"
  shows "pterm_in_signature \<Sigma> (pconst_subst c \<sigma> N M)"
  using sigM sigN
  by (induction M arbitrary: N) (auto simp add: pshift_def split: if_splits)

lemma phenkin_names_prename:
  "phenkin_names (prename r M) = phenkin_names M"
  by (induction M arbitrary: r) simp_all

lemma phenkin_names_pshift[simp]: "phenkin_names (pshift M) = phenkin_names M"
  by (simp only: pshift_def phenkin_names_prename)

lemma pconst_subst_fresh:
  assumes fresh: "c \<notin> phenkin_names M"
  shows "pconst_subst c \<sigma> N M = M"
  using fresh by (induction M arbitrary: N) auto

lemma pconst_subst_fresh_theory:
  assumes fresh: "\<And>A. A \<in> S \<Longrightarrow> c \<notin> phenkin_names A"
  shows "pconst_subst c \<sigma> N ` S = S"
proof -
  have fixed: "pconst_subst c \<sigma> N A = A" if member: "A \<in> S" for A
    by (rule pconst_subst_fresh[OF fresh[OF member]])
  show ?thesis using fixed by auto
qed

lemma pconst_subst_embedded_fresh:
  "pconst_subst (PHWitness \<sigma> A) \<tau> N (phenkin_embed B) = phenkin_embed B"
  by (rule pconst_subst_fresh[OF phenkin_witness_fresh])

subsection \<open>Turning a disjoint witness name into the new variable\<close>

definition pabstract_const :: "'c \<Rightarrow> otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "pabstract_const c \<sigma> A = pconst_subst c \<sigma> (PVar 0) (pshift A)"

lemma pabstract_const_type:
  assumes typed: "has_ptype \<Gamma> A \<tau>"
  shows "has_ptype (\<sigma> # \<Gamma>) (pabstract_const c \<sigma> A) \<tau>"
proof -
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift A) \<tau>" by (rule pshift_preserves_typing[OF typed])
  have zero: "has_ptype (\<sigma> # \<Gamma>) (PVar 0) \<sigma>" by (rule has_ptype.PVar) simp
  show ?thesis unfolding pabstract_const_def by (rule pconst_subst_type[OF shifted zero])
qed

lemma pabstract_const_signature:
  assumes sig: "pterm_in_signature \<Sigma> A"
  shows "pterm_in_signature \<Sigma> (pabstract_const c \<sigma> A)"
proof -
  have shifted: "pterm_in_signature \<Sigma> (pshift A)" using sig by (simp add: pshift_def)
  show ?thesis unfolding pabstract_const_def by (rule pconst_subst_signature[OF shifted]) simp
qed

lemma pabstract_const_fresh:
  assumes "c \<notin> phenkin_names A"
  shows "pabstract_const c \<sigma> A = pshift A"
  unfolding pabstract_const_def by (rule pconst_subst_fresh) (simp add: assms)

lemma pabstract_const_fresh_theory:
  assumes fresh: "\<And>A. A \<in> S \<Longrightarrow> c \<notin> phenkin_names A"
  shows "pabstract_const c \<sigma> ` S = pshift ` S"
proof -
  have fixed: "pabstract_const c \<sigma> A = pshift A" if member: "A \<in> S" for A
    by (rule pabstract_const_fresh[OF fresh[OF member]])
  show ?thesis using fixed by auto
qed

theorem pabstract_fresh_embedded_theory:
  "pabstract_const (PHWitness \<sigma> A) \<sigma> ` (phenkin_embed ` S) = pshift ` (phenkin_embed ` S)"
proof (rule pabstract_const_fresh_theory)
  fix B
  assume member: "B \<in> phenkin_embed ` S"
  obtain C where B: "B = phenkin_embed C" using member by blast
  show "PHWitness \<sigma> A \<notin> phenkin_names B" by (simp add: B phenkin_witness_fresh)
qed

subsection \<open>Local deduction after the witness has been abstracted\<close>

lemma pH_eigen_witness_deduction:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sigA: "pterm_in_signature \<Sigma> A"
    and d: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
      (insert (PImp (pshift (PExists \<sigma> A)) A) (pshift ` S)) PObjFalse"
  shows "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (pshift ` S)
    (PImp (PImp (pshift (PExists \<sigma> A)) A) PObjFalse)"
proof -
  have exists_type: "has_ptype \<Gamma> (PExists \<sigma> A) Prop" by (rule has_ptype.PExists[OF body])
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift (PExists \<sigma> A)) Prop"
    by (rule pshift_preserves_typing[OF exists_type])
  have premise_type: "has_ptype (\<sigma> # \<Gamma>) (PImp (pshift (PExists \<sigma> A)) A) Prop"
    by (rule has_ptype.PImp[OF shifted body])
  have premise_sig: "pterm_in_signature \<Sigma> (PImp (pshift (PExists \<sigma> A)) A)"
    using sigA by (simp add: pshift_def)
  show ?thesis by (rule pH_set_deduction[OF premise_type premise_sig d])
qed

text \<open>
  Exact remaining elimination statement: if c is absent from S and A,
  and Σ; Γ; S ∪ {(∃x:σ.A) → A[c/x]} ⊢H ⊥₀, then
  Σ; Γ; S ⊢H ⊥₀, with the stated typing and signature conditions.
  Here ⊥₀ is PObjFalse.

  The missing derivational links are: open-term constant substitution and
  free-slot renaming preserve pH proofs; abstraction of the witness axiom
  yields (∃x:σ.A) → A(x) in the extended context; the local Inst rule
  descends through the finitely many shifted assumptions; and
  Σ; Γ ⊢H ∃x:σ.((∃y:σ.A(y)) → A(x)).  The structural results above
  establish freshness and typing, not those derivational links.  No
  consistency-preservation theorem for adjoining witnesses is claimed yet.
\<close>

end
