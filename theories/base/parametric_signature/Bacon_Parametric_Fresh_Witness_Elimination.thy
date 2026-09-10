theory Bacon_Parametric_Fresh_Witness_Elimination
  imports Bacon_Parametric_Proof_Substitution
    Bacon_Parametric_Local_Quantifiers
    Bacon_Parametric_Existential_Witness_Theorem
begin

section \<open>One fresh witness preserves consistency\<close>

text \<open>
  Let c:σ be absent from S and A.  If
    Σ; Γ; S ∪ {(∃v:σ.A) → A[c/v]} ⊢H ⊥₀,
  then Σ; Γ; S ⊢H ⊥₀.  This is the fresh-witness step in Bacon,
  Proposition 15.4, and Bacon–Dorr, Theorem 3.2, p.45 n.64.

  Isabelle representation: shift the proof, replace c:σ by PVar 0, discharge
  the abstracted witness premise, descend by local Inst, and apply the proved
  existential implication theorem.  The proof uses the named transport and
  eigenvariable lemmas; no admissibility is postulated.

  Status: elimination and consistency preservation for one fresh witness.
  Consistency under arbitrary signature expansion and iteration of witness
  additions remain separate obligations.
\<close>

definition pH_fresh_witness_axiom ::
    "'c \<Rightarrow> otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "pH_fresh_witness_axiom c \<sigma> A =
    PImp (PExists \<sigma> A) (psubst0 (PConst c \<sigma>) A)"

subsection \<open>Proof transport to the eigenvariable context\<close>

lemma pH_set_pshift:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
  shows "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
proof -
  have ren: "lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<tau>"
    if index: "lookup \<Gamma> n = Some \<tau>" for n \<tau>
    using index by simp
  have shifted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image (prename Suc) S) (prename Suc A)"
    by (rule pH_set_prename[OF d ren])
  have shift_function: "pshift = prename Suc"
    by (rule ext) (simp only: pshift_def)
  show ?thesis using shifted by (simp only: shift_function)
qed

lemma pH_set_pabstract_const:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
  shows "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
    (image (pabstract_const c \<sigma>) S) (pabstract_const c \<sigma> A)"
proof -
  have shifted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
    by (rule pH_set_pshift[OF d])
  have zero_type: "has_ptype (\<sigma> # \<Gamma>) (PVar 0) \<sigma>"
    by (rule has_ptype.PVar) simp
  have zero_sig: "pterm_in_signature \<Sigma> (PVar 0)" by simp
  have substituted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
    (image (pconst_subst c \<sigma> (PVar 0)) (image pshift S))
    (pconst_subst c \<sigma> (PVar 0) (pshift A))"
    by (rule pH_set_pconst[OF shifted zero_type zero_sig])
  have abstraction_function:
    "pabstract_const c \<sigma> = (\<lambda>B. pconst_subst c \<sigma> (PVar 0) (pshift B))"
    by (rule ext) (simp only: pabstract_const_def)
  have transported_assumptions:
    "image (pconst_subst c \<sigma> (PVar 0)) (image pshift S) =
      image (pabstract_const c \<sigma>) S"
    by (simp only: image_image abstraction_function)
  have transported_conclusion:
    "pconst_subst c \<sigma> (PVar 0) (pshift A) = pabstract_const c \<sigma> A"
    by (simp only: pabstract_const_def)
  show ?thesis using substituted
    by (simp only: transported_assumptions transported_conclusion)
qed

lemma pabstract_const_PObjFalse:
  "pabstract_const c \<sigma> PObjFalse = PObjFalse"
  by (simp add: pabstract_const_def pshift_def PObjFalse_def PObjTrue_def)

lemma pabstract_fresh_witness_premise:
  assumes fresh: "c \<notin> phenkin_names A"
  shows "pabstract_const c \<sigma> (pH_fresh_witness_axiom c \<sigma> A) =
    PImp (pshift (PExists \<sigma> A)) A"
  unfolding pH_fresh_witness_axiom_def
  by (rule pproof_abstract_witness_axiom[OF fresh])

subsection \<open>Exact fresh-witness elimination\<close>

theorem pH_fresh_witness_elimination:
  assumes typed_S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and body: "has_ptype (\<sigma> # \<Gamma>) A Prop"
    and sigA: "pterm_in_signature \<Sigma> A"
    and fresh_S: "\<And>B. B \<in> S \<Longrightarrow> c \<notin> phenkin_names B"
    and fresh_A: "c \<notin> phenkin_names A"
    and contradiction: "pH_set_derivable \<Sigma> \<Gamma>
      (insert (pH_fresh_witness_axiom c \<sigma> A) S) PObjFalse"
  shows "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
proof -
  let ?W = "PImp (pshift (PExists \<sigma> A)) A"
  have abstracted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
    (image (pabstract_const c \<sigma>) (insert (pH_fresh_witness_axiom c \<sigma> A) S))
    (pabstract_const c \<sigma> PObjFalse)"
    by (rule pH_set_pabstract_const[OF contradiction])
  have unchanged_S: "image (pabstract_const c \<sigma>) S = image pshift S"
    by (rule pabstract_const_fresh_theory[OF fresh_S])
  have abstracted_axiom:
    "pabstract_const c \<sigma> (pH_fresh_witness_axiom c \<sigma> A) = ?W"
    by (rule pabstract_fresh_witness_premise[OF fresh_A])
  have eigen_contradiction: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
    (insert ?W (image pshift S)) PObjFalse"
    using abstracted
    by (simp only: image_insert unchanged_S abstracted_axiom pabstract_const_PObjFalse)
  have descended: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PExists \<sigma> ?W) PObjFalse)"
    by (rule pH_eigen_witness_descend[OF typed_S body sigA eigen_contradiction])
  have existential_theorem: "pH_proves \<Sigma> \<Gamma> (PExists \<sigma> ?W)"
    by (rule pH_exists_imp_shift_exists[OF body sigA])
  have local_existential: "pH_set_derivable \<Sigma> \<Gamma> S (PExists \<sigma> ?W)"
    by (rule pH_set_Theorem[OF existential_theorem])
  show ?thesis by (rule pH_set_MP[OF local_existential descended])
qed

lemma pH_fresh_witness_consistency:
  assumes typed_S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and consistent_S: "pH_consistent \<Sigma> \<Gamma> S"
    and body: "has_ptype (\<sigma> # \<Gamma>) A Prop"
    and sigA: "pterm_in_signature \<Sigma> A"
    and fresh_S: "\<And>B. B \<in> S \<Longrightarrow> c \<notin> phenkin_names B"
    and fresh_A: "c \<notin> phenkin_names A"
  shows "pH_consistent \<Sigma> \<Gamma> (insert (pH_fresh_witness_axiom c \<sigma> A) S)"
proof (unfold pH_consistent_def, rule notI)
  assume extended_bad: "pH_set_derivable \<Sigma> \<Gamma>
    (insert (pH_fresh_witness_axiom c \<sigma> A) S) PObjFalse"
  have original_bad: "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
    by (rule pH_fresh_witness_elimination[OF typed_S body sigA fresh_S fresh_A extended_bad])
  show False by (rule notE[OF consistent_S[unfolded pH_consistent_def] original_bad])
qed

subsection \<open>A declared witness gives a typed consistent extension\<close>

lemma pH_fresh_witness_axiom_language:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop"
    and sigA: "pterm_in_signature \<Sigma> A" and declared: "c \<in> \<Sigma> \<sigma>"
  shows "pterm_in_language \<Sigma> \<Gamma> (pH_fresh_witness_axiom c \<sigma> A) Prop"
proof -
  have constant_type: "has_ptype \<Gamma> (PConst c \<sigma>) \<sigma>" by (rule has_ptype.PConst)
  have constant_sig: "pterm_in_signature \<Sigma> (PConst c \<sigma>)" using declared by simp
  have instance_type: "has_ptype \<Gamma> (psubst0 (PConst c \<sigma>) A) Prop"
    by (rule psubst0_preserves_typing[OF body constant_type])
  have typed: "has_ptype \<Gamma> (pH_fresh_witness_axiom c \<sigma> A) Prop"
    unfolding pH_fresh_witness_axiom_def
    by (rule has_ptype.PImp[OF has_ptype.PExists[OF body] instance_type])
  have instance_sig: "pterm_in_signature \<Sigma> (psubst0 (PConst c \<sigma>) A)"
    by (rule psubst0_signature[OF sigA constant_sig])
  have guarded: "pterm_in_signature \<Sigma> (pH_fresh_witness_axiom c \<sigma> A)"
    unfolding pH_fresh_witness_axiom_def
    using sigA instance_sig by simp
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed guarded])
qed

theorem pH_adjoin_fresh_witness:
  assumes typed_S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and consistent_S: "pH_consistent \<Sigma> \<Gamma> S"
    and body: "has_ptype (\<sigma> # \<Gamma>) A Prop"
    and sigA: "pterm_in_signature \<Sigma> A" and declared: "c \<in> \<Sigma> \<sigma>"
    and fresh_S: "\<And>B. B \<in> S \<Longrightarrow> c \<notin> phenkin_names B"
    and fresh_A: "c \<notin> phenkin_names A"
  shows "pH_typed_theory \<Sigma> \<Gamma> (insert (pH_fresh_witness_axiom c \<sigma> A) S)"
    and "pH_consistent \<Sigma> \<Gamma> (insert (pH_fresh_witness_axiom c \<sigma> A) S)"
proof -
  note axiom_parts = pH_fresh_witness_axiom_language[OF body sigA declared,
    unfolded pterm_in_language_def]
  show "pH_typed_theory \<Sigma> \<Gamma> (insert (pH_fresh_witness_axiom c \<sigma> A) S)"
  proof (unfold pH_typed_theory_def, intro ballI)
    fix B
    assume member: "B \<in> insert (pH_fresh_witness_axiom c \<sigma> A) S"
    show "has_ptype \<Gamma> B Prop \<and> pterm_in_signature \<Sigma> B"
    proof (cases "B = pH_fresh_witness_axiom c \<sigma> A")
      case True
      show ?thesis unfolding True by (rule axiom_parts)
    next
      case False
      have old_member: "B \<in> S" using member False by simp
      show ?thesis by (rule bspec[OF typed_S[unfolded pH_typed_theory_def] old_member])
    qed
  qed
  show "pH_consistent \<Sigma> \<Gamma> (insert (pH_fresh_witness_axiom c \<sigma> A) S)"
    by (rule pH_fresh_witness_consistency[OF typed_S consistent_S body sigA fresh_S fresh_A])
qed

text \<open>
  Elimination itself does not require c ∈ Σσ. If substitution leaves an
  occurrence of the undeclared constant in the witness axiom, the signature
  guard excludes that axiom as a local assumption. For a vacuous binder,
  however, the axiom may be constant-free and pass the guard: A = PObjTrue
  gives (∃xσ. PObjTrue) → PObjTrue. The final extension theorem
  includes that declaration condition and proves both typing and consistency.
  Freshness excludes the name c at every type, a sufficient explicit condition.

  Status: one-axiom preservation in a fixed signature containing the witness.
  To start from an arbitrary old signature, consistency of its disjoint
  embedding must still be proved before this theorem can be applied there.
\<close>

end
