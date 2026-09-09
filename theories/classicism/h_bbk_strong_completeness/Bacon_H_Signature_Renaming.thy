theory Bacon_H_Signature_Renaming
  imports Bacon_H_BBK_Canonical_Development.Bacon_H_BBK_Completeness
begin

section \<open>Reserving names before Henkin extension\<close>

text \<open>
  ι(c) = O·c, ω(c) = W·c, with disjoint ranges and a left inverse to ι. Bacon,
  Proposition 15.4, p. 319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: H_rename_constants uniformly renames constants without
  changing object types. Original formulas move to the O-prefixed stock, leaving
  W-prefixed strings available.

  Status: Derivability and consistency transport for arbitrary starting sets; Henkin
  extension is the next stage.
\<close>

definition H_original_name :: "string \<Rightarrow> string" where
  "H_original_name c = ''O'' @ c"

definition H_witness_name :: "string \<Rightarrow> string" where
  "H_witness_name c = ''W'' @ c"

definition H_unprefix_name :: "string \<Rightarrow> string" where
  "H_unprefix_name c = tl c"

lemma H_original_name_inverse[simp]:
  "H_unprefix_name (H_original_name c) = c"
  by (simp add: H_unprefix_name_def H_original_name_def)

lemma H_original_name_injective: "inj H_original_name"
  unfolding inj_def H_original_name_def by simp

lemma H_witness_name_injective: "inj H_witness_name"
  unfolding inj_def H_witness_name_def by simp

lemma H_name_namespaces_disjoint:
  "range H_original_name \<inter> range H_witness_name = {}"
  by (auto simp add: H_original_name_def H_witness_name_def)

subsection \<open>Uniform, type-preserving renaming of constants\<close>

text \<open>
  ι(M[N/x]) = ι(M)[ι(N)/x], and Γ ⊢ M : τ ⇒ Γ ⊢ ι(M) : τ. Bacon, Proposition 15.4, p.
  319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: The constant map commutes with the term constructors and de
  Bruijn substitution; it does not rename variable slots.

  Status: Syntactic transport only; the disjoint reserve supplies freshness later.
\<close>

fun H_rename_constants :: "(string \<Rightarrow> string) \<Rightarrow> oterm \<Rightarrow> oterm" where
  "H_rename_constants f (Var n) = Var n"
| "H_rename_constants f (Const c \<sigma>) = Const (f c) \<sigma>"
| "H_rename_constants f (App M N) = App (H_rename_constants f M) (H_rename_constants f N)"
| "H_rename_constants f (Lam \<sigma> M) = Lam \<sigma> (H_rename_constants f M)"
| "H_rename_constants f (Eq \<sigma> M N) = Eq \<sigma> (H_rename_constants f M) (H_rename_constants f N)"
| "H_rename_constants f (Neg A) = Neg (H_rename_constants f A)"
| "H_rename_constants f (Conj A B) = Conj (H_rename_constants f A) (H_rename_constants f B)"
| "H_rename_constants f (Disj A B) = Disj (H_rename_constants f A) (H_rename_constants f B)"
| "H_rename_constants f (Imp A B) = Imp (H_rename_constants f A) (H_rename_constants f B)"
| "H_rename_constants f (Forall \<sigma> A) = Forall \<sigma> (H_rename_constants f A)"
| "H_rename_constants f (Exists \<sigma> A) = Exists \<sigma> (H_rename_constants f A)"

lemma H_rename_constants_infer:
  "infer_type \<Gamma> (H_rename_constants f M) = infer_type \<Gamma> M"
proof (induction M arbitrary: \<Gamma>)
  case (App M N)
  have left: "infer_type \<Gamma> (H_rename_constants f M) = infer_type \<Gamma> M"
    by (rule App.IH(1))
  have right: "infer_type \<Gamma> (H_rename_constants f N) = infer_type \<Gamma> N"
    by (rule App.IH(2))
  show ?case
    by (cases "infer_type \<Gamma> M"; cases "infer_type \<Gamma> N")
      (simp_all add: left right split: otype.splits)
qed simp_all

lemma H_rename_constants_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> H_rename_constants f M : \<sigma>"
proof -
  have "infer_type \<Gamma> (H_rename_constants f M) = Some \<sigma>"
    by (simp only: H_rename_constants_infer infer_type_complete[OF typed])
  then show ?thesis by (rule infer_type_sound)
qed

lemma H_rename_constants_inverse:
  assumes inverse: "\<And>c. g (f c) = c"
  shows "H_rename_constants g (H_rename_constants f M) = M"
  by (induction M) (simp_all add: inverse)

lemma H_rename_constants_rename:
  "H_rename_constants f (rename r M) = rename r (H_rename_constants f M)"
  by (induction M arbitrary: r) simp_all

lemma H_rename_constants_shift:
  "H_rename_constants f (shift M) = shift (H_rename_constants f M)"
  by (simp only: shift_def H_rename_constants_rename)

lemma H_rename_constants_lift:
  "(\<lambda>n. H_rename_constants f (lift_subst s n)) = lift_subst (\<lambda>n. H_rename_constants f (s n))"
proof (rule ext)
  fix n
  show "H_rename_constants f (lift_subst s n) = lift_subst (\<lambda>n. H_rename_constants f (s n)) n"
    by (cases n) (simp_all add: H_rename_constants_rename)
qed

lemma H_rename_constants_subst:
  "H_rename_constants f (subst s M) = subst (\<lambda>n. H_rename_constants f (s n)) (H_rename_constants f M)"
  by (induction M arbitrary: s) (simp_all add: H_rename_constants_lift)

lemma H_rename_constants_subst0:
  "H_rename_constants f (subst0 N M) = subst0 (H_rename_constants f N) (H_rename_constants f M)"
proof -
  have maps: "(\<lambda>n. H_rename_constants f (case_nat N Var n)) = case_nat (H_rename_constants f N) Var"
  proof (rule ext)
    fix n
    show "H_rename_constants f (case_nat N Var n) = case_nat (H_rename_constants f N) Var n"
      by (cases n) simp_all
  qed
  show ?thesis by (simp only: subst0_def H_rename_constants_subst maps)
qed

lemma H_rename_constants_ObjFalse[simp]: "H_rename_constants f ObjFalse = ObjFalse"
  by (simp add: ObjFalse_def ObjTrue_def)

lemma H_rename_constants_consts:
  "consts_of (H_rename_constants f M) = f ` consts_of M"
  by (induction M) auto

lemma H_original_theory_avoids_witness_names:
  "H_witness_name w \<notin> consts_of_set (H_rename_constants H_original_name ` S)"
  unfolding consts_of_set_def
  using H_name_namespaces_disjoint
  by (auto simp add: H_rename_constants_consts)

subsection \<open>Propositional axioms and conversion commute with renaming\<close>

text \<open>
  M →βη N ⇒ ι(M) →βη ι(N); propositional tautologies remain tautologies under ι.
  Bacon, Proposition 15.4, p. 319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: The lemmas separately transport Boolean evaluation and
  compatible β/η steps through the constant map.

  Status: These facts justify the conversion and PC cases of the following H-proof
  induction.
\<close>

lemma H_rename_constants_prop_eval:
  "prop_eval v (H_rename_constants f A) = prop_eval (\<lambda>B. v (H_rename_constants f B)) A"
  by (induction A) simp_all

lemma H_rename_constants_tautology:
  assumes taut: "prop_tautology \<Gamma> A"
  shows "prop_tautology \<Gamma> (H_rename_constants f A)"
proof -
  have typed: "\<Gamma> \<turnstile> A : Prop" and valuations: "\<forall>v. prop_eval v A"
    using taut unfolding prop_tautology_def by blast+
  have mapped_type: "\<Gamma> \<turnstile> H_rename_constants f A : Prop"
    by (rule H_rename_constants_type[OF typed])
  have mapped_truth: "\<forall>v. prop_eval v (H_rename_constants f A)"
  proof (rule allI)
    fix v
    have truth: "prop_eval (\<lambda>B. v (H_rename_constants f B)) A"
      using valuations by (rule spec[where x="\<lambda>B. v (H_rename_constants f B)"])
    show "prop_eval v (H_rename_constants f A)"
      by (simp only: H_rename_constants_prop_eval truth)
  qed
  show ?thesis using mapped_type mapped_truth unfolding prop_tautology_def by blast
qed

lemma H_rename_constants_beta:
  assumes "beta_contract M N"
  shows "beta_contract (H_rename_constants f M) (H_rename_constants f N)"
  using assms by (cases rule: beta_contract.cases)
    (simp add: H_rename_constants_subst0 beta_contract.beta)

lemma H_rename_constants_eta:
  assumes "eta_contract M N"
  shows "eta_contract (H_rename_constants f M) (H_rename_constants f N)"
  using assms by (cases rule: eta_contract.cases)
    (simp add: H_rename_constants_shift eta_contract.eta)

lemma H_rename_constants_compatible:
  assumes step: "compatible_step R M N"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> R (H_rename_constants f X) (H_rename_constants f Y)"
  shows "compatible_step R (H_rename_constants f M) (H_rename_constants f N)"
  using step by (induction rule: compatible_step.induct)
    (auto intro: compatible_step.intros roots)

lemma H_rename_constants_beta_step:
  "compatible_step beta_contract M N \<Longrightarrow>
    compatible_step beta_contract (H_rename_constants f M) (H_rename_constants f N)"
  by (rule H_rename_constants_compatible) (assumption, rule H_rename_constants_beta)

lemma H_rename_constants_eta_step:
  "compatible_step eta_contract M N \<Longrightarrow>
    compatible_step eta_contract (H_rename_constants f M) (H_rename_constants f N)"
  by (rule H_rename_constants_compatible) (assumption, rule H_rename_constants_eta)

subsection \<open>Preservation of H derivations\<close>

text \<open>
  Γ ⊢ₕ A ⇒ Γ ⊢ₕ ι(A); a left inverse gives reflection. Bacon, Proposition 15.4, p.
  319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: The proof transports each H constructor. Applied to the
  reserve embedding, it preserves consistency before witnesses are added.

  Status: No countable enumeration of the initial theory or finite-theory assumption
  is used.
\<close>

lemma H_rename_constants_proves:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>H A"
  shows "\<Gamma> \<turnstile>\<^sub>H H_rename_constants f A"
  using derivation
proof (induction rule: H_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule H_proves.PC[OF H_rename_constants_tautology[OF PC.hyps]])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (simp only: H_rename_constants.simps) (rule H_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  have body: "\<sigma> # \<Gamma> \<turnstile> H_rename_constants f A : Prop"
    by (rule H_rename_constants_type[OF UI.hyps(1)])
  have arg: "\<Gamma> \<turnstile> H_rename_constants f T : \<sigma>"
    by (rule H_rename_constants_type[OF UI.hyps(2)])
  show ?case by (simp only: H_rename_constants.simps H_rename_constants_subst0)
    (rule H_proves.UI[OF body arg])
next
  case (EG \<sigma> \<Gamma> A T)
  have body: "\<sigma> # \<Gamma> \<turnstile> H_rename_constants f A : Prop"
    by (rule H_rename_constants_type[OF EG.hyps(1)])
  have arg: "\<Gamma> \<turnstile> H_rename_constants f T : \<sigma>"
    by (rule H_rename_constants_type[OF EG.hyps(2)])
  show ?case by (simp only: H_rename_constants.simps H_rename_constants_subst0)
    (rule H_proves.EG[OF body arg])
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.Ref[OF H_rename_constants_type[OF Ref.hyps]])
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.LL[OF H_rename_constants_type[OF LL.hyps(1)]
      H_rename_constants_type[OF LL.hyps(2)] H_rename_constants_type[OF LL.hyps(3)]])
next
  case (Beta \<Gamma> A B)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.Beta[OF H_rename_constants_type[OF Beta.hyps(1)]
      H_rename_constants_type[OF Beta.hyps(2)] H_rename_constants_beta_step[OF Beta.hyps(3)]])
next
  case (Eta \<Gamma> A B)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.Eta[OF H_rename_constants_type[OF Eta.hyps(1)]
      H_rename_constants_type[OF Eta.hyps(2)] H_rename_constants_eta_step[OF Eta.hyps(3)]])
next
  case (MP \<Gamma> A B)
  have implication: "\<Gamma> \<turnstile>\<^sub>H Imp (H_rename_constants f A) (H_rename_constants f B)"
    using MP.IH(2) by (simp only: H_rename_constants.simps)
  show ?case by (rule H_proves.MP[OF MP.IH(1) implication])
next
  case (Gen \<Gamma> P \<sigma> Q)
  have implication: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift (H_rename_constants f P)) (H_rename_constants f Q)"
    using Gen.IH by (simp only: H_rename_constants.simps H_rename_constants_shift)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.Gen[OF H_rename_constants_type[OF Gen.hyps(1)]
      H_rename_constants_type[OF Gen.hyps(2)] implication])
next
  case (Inst \<sigma> \<Gamma> P Q)
  have implication: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (H_rename_constants f P) (shift (H_rename_constants f Q))"
    using Inst.IH by (simp only: H_rename_constants.simps H_rename_constants_shift)
  show ?case by (simp only: H_rename_constants.simps)
    (rule H_proves.Inst[OF H_rename_constants_type[OF Inst.hyps(1)]
      H_rename_constants_type[OF Inst.hyps(2)] implication])
qed

lemma H_rename_constants_proves_reflect:
  assumes inverse: "\<And>c. g (f c) = c"
    and derivation: "\<Gamma> \<turnstile>\<^sub>H H_rename_constants f A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
  using H_rename_constants_proves[OF derivation, where f=g]
  by (simp only: H_rename_constants_inverse[where f=f and g=g and M=A, OF inverse])

lemma H_rename_constants_derivable:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; map (H_rename_constants f) \<Delta> \<turnstile>\<^sub>H H_rename_constants f A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  have member: "H_rename_constants f A \<in> set (map (H_rename_constants f) \<Delta>)"
    by (simp only: set_map) (rule imageI[OF Assumption.hyps(1)])
  show ?case by (rule H_derivable.Assumption[OF member H_rename_constants_type[OF Assumption.hyps(2)]])
next
  case (Theorem \<Gamma> A \<Delta>)
  show ?case by (rule H_derivable.Theorem[OF H_rename_constants_proves[OF Theorem.hyps]])
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have implication: "\<Gamma> ; map (H_rename_constants f) \<Delta> \<turnstile>\<^sub>H
      Imp (H_rename_constants f A) (H_rename_constants f B)"
    using Derive_MP.IH(2) by (simp only: H_rename_constants.simps)
  show ?case by (rule H_derivable.Derive_MP[OF Derive_MP.IH(1) implication])
qed

lemma H_rename_constants_set_derivable:
  assumes derivation: "\<Gamma> ; S \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<Gamma> ; H_rename_constants f ` S \<turnstile>\<^sub>H\<^sub>s H_rename_constants f A"
proof -
  obtain \<Delta> where subset: "set \<Delta> \<subseteq> S" and local: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    using derivation unfolding H_set_derivable_def by blast
  have mapped_subset: "set (map (H_rename_constants f) \<Delta>) \<subseteq> H_rename_constants f ` S"
    using subset by auto
  have mapped: "\<Gamma> ; map (H_rename_constants f) \<Delta> \<turnstile>\<^sub>H H_rename_constants f A"
    by (rule H_rename_constants_derivable[OF local])
  show ?thesis unfolding H_set_derivable_def
    by (rule exI[where x="map (H_rename_constants f) \<Delta>"], rule conjI) (rule mapped_subset, rule mapped)
qed

lemma H_rename_constants_image_inverse:
  assumes inverse: "\<And>c. g (f c) = c"
  shows "H_rename_constants g ` (H_rename_constants f ` S) = S"
proof -
  have terms: "H_rename_constants g (H_rename_constants f M) = M" for M
    by (rule H_rename_constants_inverse[where f=f and g=g and M=M, OF inverse])
  show ?thesis by (simp add: image_image terms)
qed

lemma H_rename_constants_consistent_iff:
  assumes inverse: "\<And>c. g (f c) = c"
  shows "H_consistent \<Gamma> (H_rename_constants f ` S) \<longleftrightarrow> H_consistent \<Gamma> S"
proof
  assume mapped: "H_consistent \<Gamma> (H_rename_constants f ` S)"
  show "H_consistent \<Gamma> S"
  proof (unfold H_consistent_def, intro notI)
    assume bad: "\<Gamma> ; S \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    have "\<Gamma> ; H_rename_constants f ` S \<turnstile>\<^sub>H\<^sub>s ObjFalse"
      using H_rename_constants_set_derivable[OF bad, where f=f] by simp
    then show False using mapped unfolding H_consistent_def by blast
  qed
next
  assume original: "H_consistent \<Gamma> S"
  show "H_consistent \<Gamma> (H_rename_constants f ` S)"
  proof (unfold H_consistent_def, intro notI)
    assume bad: "\<Gamma> ; H_rename_constants f ` S \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    have "\<Gamma> ; S \<turnstile>\<^sub>H\<^sub>s ObjFalse"
      using H_rename_constants_set_derivable[OF bad, where f=g]
      by (simp only: H_rename_constants_image_inverse[where f=f and g=g and S=S, OF inverse]
            H_rename_constants_ObjFalse)
    then show False using original unfolding H_consistent_def by blast
  qed
qed

lemma H_original_theory_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma> (H_rename_constants H_original_name ` S)"
  using assms H_rename_constants_type unfolding typed_theory_def by blast

theorem H_original_theory_consistent_iff:
  "H_consistent \<Gamma> (H_rename_constants H_original_name ` S) \<longleftrightarrow> H_consistent \<Gamma> S"
  by (rule H_rename_constants_consistent_iff[where g=H_unprefix_name]) simp

end
