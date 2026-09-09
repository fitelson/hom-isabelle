theory Bacon_Parametric_Proof_Substitution
  imports Bacon_Parametric_Theorem_Substitution
begin

section \<open>Local and set consequence under proof substitution\<close>

text \<open>
  The theorem transports extend to Σ; Γ; S ⊢H A by transporting each
  finite list of assumptions supporting the derivation.  Source: the
  finite-proof argument in Bacon--Dorr p.45 n.64 and Bacon, Proposition 15.4.
  This wrapper retains the earlier public theorem names after splitting
  the algebra, conversion, and theorem-level checks into smaller theories.
\<close>

subsection \<open>Transport of finite and arbitrary sets of local assumptions\<close>

lemma pproof_local_transport:
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A"
    and thms: "\<And>B. pH_proves \<Sigma> \<Gamma> B \<Longrightarrow> pH_proves \<Omega> \<Delta> (f B)"
    and types: "\<And>B. has_ptype \<Gamma> B Prop \<Longrightarrow> has_ptype \<Delta> (f B) Prop"
    and sigs: "\<And>B. pterm_in_signature \<Sigma> B \<Longrightarrow> pterm_in_signature \<Omega> (f B)"
    and implication: "\<And>B C. f (PImp B C) = PImp (f B) (f C)"
  shows "pH_derivable \<Omega> \<Delta> (map f L) (f A)"
  using d
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have member: "f A \<in> set (map f L)" by (simp only: set_map) (rule imageI[OF Assumption.hyps(1)])
  show ?case by (rule pH_derivable.Assumption[OF member types[OF Assumption.hyps(2)] sigs[OF Assumption.hyps(3)]])
next
  case (Theorem A)
  show ?case by (rule pH_derivable.Theorem[OF thms[OF Theorem.hyps]])
next
  case (MP A B)
  have right: "pH_derivable \<Omega> \<Delta> (map f L) (PImp (f A) (f B))" using MP.IH(2) by (simp only: implication)
  show ?case by (rule pH_derivable.MP[OF MP.IH(1) right])
qed

lemma pH_derivable_prename:
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "pH_derivable \<Sigma> \<Delta> (map (prename r) L) (prename r A)"
proof (rule pproof_local_transport[where f="prename r" and \<Omega>=\<Sigma> and \<Delta>=\<Delta>, OF d])
  fix B
  assume theorem_B: "pH_proves \<Sigma> \<Gamma> B"
  show "pH_proves \<Sigma> \<Delta> (prename r B)" by (rule pH_proves_prename[OF theorem_B ren])
next
  fix B
  assume typed_B: "has_ptype \<Gamma> B Prop"
  show "has_ptype \<Delta> (prename r B) Prop" by (rule prename_preserves_typing[OF typed_B ren])
next
  fix B
  assume sig_B: "pterm_in_signature \<Sigma> B"
  show "pterm_in_signature \<Sigma> (prename r B)" by (rule pproof_signature_prenameI[OF sig_B])
next
  fix B C
  show "prename r (PImp B C) = PImp (prename r B) (prename r C)" by (rule prename.simps)
qed

lemma pH_derivable_pconst:
  fixes c :: 'a and N :: "'a pterm" and \<Sigma> :: "'a psignature"
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A" and typed: "has_ptype \<Gamma> N \<sigma>" and sig: "pterm_in_signature \<Sigma> N"
  shows "pH_derivable \<Sigma> \<Gamma> (map (pconst_subst c \<sigma> N) L) (pconst_subst c \<sigma> N A)"
proof (rule pproof_local_transport[where f="pconst_subst c \<sigma> N" and \<Omega>=\<Sigma> and \<Delta>=\<Gamma>, OF d])
  fix B :: "'a pterm"
  assume theorem_B: "pH_proves \<Sigma> \<Gamma> B"
  show "pH_proves \<Sigma> \<Gamma> (pconst_subst c \<sigma> N B)" by (rule pH_proves_pconst[OF theorem_B typed sig])
next
  fix B :: "'a pterm"
  assume typed_B: "has_ptype \<Gamma> B Prop"
  show "has_ptype \<Gamma> (pconst_subst c \<sigma> N B) Prop" by (rule pconst_subst_type[OF typed_B typed])
next
  fix B :: "'a pterm"
  assume sig_B: "pterm_in_signature \<Sigma> B"
  show "pterm_in_signature \<Sigma> (pconst_subst c \<sigma> N B)" by (rule pconst_subst_signature[OF sig_B sig])
next
  fix B C :: "'a pterm"
  show "pconst_subst c \<sigma> N (PImp B C) = PImp (pconst_subst c \<sigma> N B) (pconst_subst c \<sigma> N C)"
    by (rule pconst_subst.simps)
qed

lemma pproof_set_transport:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and lists: "\<And>L B. pH_derivable \<Sigma> \<Gamma> L B \<Longrightarrow> pH_derivable \<Omega> \<Delta> (map f L) (f B)"
  shows "pH_set_derivable \<Omega> \<Delta> (f ` S) (f A)"
  using d unfolding pH_set_derivable_def
proof (elim exE conjE)
  fix L
  assume subset: "set L \<subseteq> S" and local: "pH_derivable \<Sigma> \<Gamma> L A"
  have mapped: "pH_derivable \<Omega> \<Delta> (map f L) (f A)" by (rule lists[OF local])
  have mapped_subset: "set (map f L) \<subseteq> f ` S"
    using image_mono[where f=f, OF subset] by (simp only: set_map)
  show "\<exists>L. set L \<subseteq> f ` S \<and> pH_derivable \<Omega> \<Delta> L (f A)"
    by (rule exI[where x="map f L"], rule conjI) (rule mapped_subset, rule mapped)
qed

lemma pH_set_prename:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "pH_set_derivable \<Sigma> \<Delta> (prename r ` S) (prename r A)"
proof (rule pproof_set_transport[where f="prename r" and \<Omega>=\<Sigma> and \<Delta>=\<Delta>, OF d])
  fix L B
  assume local: "pH_derivable \<Sigma> \<Gamma> L B"
  show "pH_derivable \<Sigma> \<Delta> (map (prename r) L) (prename r B)"
    by (rule pH_derivable_prename[OF local ren])
qed

lemma pH_set_pconst:
  fixes c :: 'a and N :: "'a pterm" and \<Sigma> :: "'a psignature"
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A" and typed: "has_ptype \<Gamma> N \<sigma>" and sig: "pterm_in_signature \<Sigma> N"
  shows "pH_set_derivable \<Sigma> \<Gamma> (pconst_subst c \<sigma> N ` S) (pconst_subst c \<sigma> N A)"
proof (rule pproof_set_transport[where f="pconst_subst c \<sigma> N" and \<Omega>=\<Sigma> and \<Delta>=\<Gamma>, OF d])
  fix L :: "'a pterm list" and B :: "'a pterm"
  assume local: "pH_derivable \<Sigma> \<Gamma> L B"
  show "pH_derivable \<Sigma> \<Gamma> (map (pconst_subst c \<sigma> N) L) (pconst_subst c \<sigma> N B)"
    by (rule pH_derivable_pconst[OF local typed sig])
qed

subsection \<open>Stable names for the split proof infrastructure\<close>

lemmas pproof_lift_ren_comp = Bacon_Parametric_Renaming_Algebra.pproof_lift_ren_comp
lemmas pproof_prename_comp = Bacon_Parametric_Renaming_Algebra.pproof_prename_comp
lemmas pproof_prename_lift_shift = Bacon_Parametric_Renaming_Algebra.pproof_prename_lift_shift
lemmas pproof_psubst_prename = Bacon_Parametric_Renaming_Algebra.pproof_psubst_prename
lemmas pproof_prename_psubst = Bacon_Parametric_Renaming_Algebra.pproof_prename_psubst
lemmas pproof_psubst_lift_shift = Bacon_Parametric_Renaming_Algebra.pproof_psubst_lift_shift
lemmas pproof_prename_psubst0 = Bacon_Parametric_Renaming_Algebra.pproof_prename_psubst0
lemmas pproof_pconst_prename = Bacon_Parametric_Constant_Substitution_Algebra.pproof_pconst_prename
lemmas pproof_pconst_shift = Bacon_Parametric_Constant_Substitution_Algebra.pproof_pconst_shift
lemmas pproof_pconst_lift = Bacon_Parametric_Constant_Substitution_Algebra.pproof_pconst_lift
lemmas pproof_pconst_psubst = Bacon_Parametric_Constant_Substitution_Algebra.pproof_pconst_psubst
lemmas pproof_pconst_psubst0 = Bacon_Parametric_Constant_Substitution_Algebra.pproof_pconst_psubst0
lemmas pproof_beta_prename = Bacon_Parametric_Conversion_Substitution.pproof_beta_prename
lemmas pproof_eta_prename = Bacon_Parametric_Conversion_Substitution.pproof_eta_prename
lemmas pproof_compatible_prename = Bacon_Parametric_Conversion_Substitution.pproof_compatible_prename
lemmas pproof_beta_pconst = Bacon_Parametric_Conversion_Substitution.pproof_beta_pconst
lemmas pproof_eta_pconst = Bacon_Parametric_Conversion_Substitution.pproof_eta_pconst
lemmas pproof_compatible_pconst = Bacon_Parametric_Conversion_Substitution.pproof_compatible_pconst
lemmas pproof_prop_eval_prename = Bacon_Parametric_Conversion_Substitution.pproof_prop_eval_prename
lemmas pproof_prop_eval_pconst = Bacon_Parametric_Conversion_Substitution.pproof_prop_eval_pconst
lemmas pproof_taut_prename = Bacon_Parametric_Conversion_Substitution.pproof_taut_prename
lemmas pproof_taut_pconst = Bacon_Parametric_Conversion_Substitution.pproof_taut_pconst
lemmas pH_proves_prename = Bacon_Parametric_Theorem_Substitution.pH_proves_prename
lemmas pH_proves_pconst = Bacon_Parametric_Theorem_Substitution.pH_proves_pconst
lemmas pproof_abstract_fresh_instance = Bacon_Parametric_Constant_Substitution_Algebra.pproof_abstract_fresh_instance
lemmas pproof_abstract_witness_axiom = Bacon_Parametric_Constant_Substitution_Algebra.pproof_abstract_witness_axiom

end
