theory Bacon_H_Identity_Local
  imports "Bacon_Classicism.Bacon_Clean_Canonical_Base"
begin

section \<open>H-only local reasoning for material Identity Identity\<close>

text \<open>
  We use PC, Ref, LL, β, and MP to obtain symmetry of =σ and
  a =σ b → (Fa ↔ Fb).  Local assumptions are discharged by the
  MP-only H deduction theorem before any quantifier rule is applied.
  Source: Bacon--Dorr Figure 2, p.8; preparation for deriving the
  material biconditional corresponding to Figure 4 Identity Identity.

  Isabelle representation.  H_derivable is the existing finite-list,
  theorem-and-MP local relation.  We reuse H_derivable_deduction and
  H_derivable_empty_imp_proves from the historical canonical file.
  Their proofs are H-only syntax inductions; no canonical-model or
  completeness theorem is used.  The import has broader historical
  dependencies, but every logical inference in this leaf is in H.
  Status.  These results do not assert identity of logical operations.
\<close>

lemma H_only_deduction:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and local_derivation: "\<Gamma> ; [A] \<turnstile>\<^sub>H B"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp A B"
proof -
  have discharged: "\<Gamma> ; [] \<turnstile>\<^sub>H Imp A B"
    by (rule H_derivable_deduction[OF A local_derivation])
  show ?thesis by (rule H_derivable_empty_imp_proves[OF discharged]) (rule refl)
qed

lemma H_only_local_theorem_MP:
  assumes implication: "\<Gamma> \<turnstile>\<^sub>H Imp A B" and premise: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H B"
  by (rule H_derivable.Derive_MP[OF premise H_derivable.Theorem[OF implication]])

lemma H_only_local_conj:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and left: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H A" and right: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H B"
  shows "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H Conj A B"
proof -
  have schema: "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp B (Conj A B))"
    by (rule H_proves.PC[OF prop_tautology_conj_intro[OF A B]])
  have implication: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H Imp B (Conj A B)"
    by (rule H_only_local_theorem_MP[OF schema left])
  show ?thesis by (rule H_derivable.Derive_MP[OF right implication])
qed

lemma H_only_local_bicond_left:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and biconditional: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
    and premise: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H B"
proof -
  have PC: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    unfolding prop_tautology_def using A B by auto
  have implication: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H Imp A B"
    by (rule H_only_local_theorem_MP[OF H_proves.PC[OF PC] biconditional])
  show ?thesis by (rule H_derivable.Derive_MP[OF premise implication])
qed

lemma H_only_local_bicond_right:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and biconditional: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
    and premise: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H B"
  shows "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H A"
proof -
  have PC: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    unfolding prop_tautology_def using A B by auto
  have implication: "\<Gamma> ; \<Lambda> \<turnstile>\<^sub>H Imp B A"
    by (rule H_only_local_theorem_MP[OF H_proves.PC[OF PC] biconditional])
  show ?thesis by (rule H_derivable.Derive_MP[OF premise implication])
qed

lemma H_only_beta_application:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H (App (Lam \<sigma> P) T \<longleftrightarrow>\<^sub>o subst0 T P)"
proof -
  have function_type: "\<Gamma> \<turnstile> Lam \<sigma> P : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF P])
  have source: "\<Gamma> \<turnstile> App (Lam \<sigma> P) T : Prop" by (rule has_type.App[OF function_type T])
  have target_type: "\<Gamma> \<turnstile> subst0 T P : Prop" by (rule subst0_preserves_typing[OF P T])
  have step: "compatible_step beta_contract (App (Lam \<sigma> P) T) (subst0 T P)"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  show ?thesis by (rule H_proves.Beta[OF source target_type step])
qed

lemma H_only_equality_symmetry:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Eq \<sigma> a b) (Eq \<sigma> b a)"
proof -
  let ?E = "Eq \<sigma> a b"
  let ?R = "Lam \<sigma> (Eq \<sigma> (Var 0) (shift a))"
  have E: "\<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Eq[OF a b])
  have aa: "\<Gamma> \<turnstile> Eq \<sigma> a a : Prop" by (rule has_type.Eq[OF a a])
  have ba: "\<Gamma> \<turnstile> Eq \<sigma> b a : Prop" by (rule has_type.Eq[OF b a])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift a : \<sigma>" by (rule weakening_front[OF a])
  have body: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (Var 0) (shift a) : Prop"
    by (rule has_type.Eq[OF variable shifted])
  have R: "\<Gamma> \<turnstile> ?R : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF body])
  have Ra: "\<Gamma> \<turnstile> App ?R a : Prop" by (rule has_type.App[OF R a])
  have Rb: "\<Gamma> \<turnstile> App ?R b : Prop" by (rule has_type.App[OF R b])
  have beta_a: "\<Gamma> \<turnstile>\<^sub>H (App ?R a \<longleftrightarrow>\<^sub>o Eq \<sigma> a a)"
    using H_only_beta_application[OF body a] by (simp add: subst0_def)
  have beta_b: "\<Gamma> \<turnstile>\<^sub>H (App ?R b \<longleftrightarrow>\<^sub>o Eq \<sigma> b a)"
    using H_only_beta_application[OF body b] by (simp add: subst0_def)
  have equality: "\<Gamma> ; [?E] \<turnstile>\<^sub>H ?E"
    by (rule H_derivable.Assumption[OF _ E]) simp
  have reflexivity: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Eq \<sigma> a a"
    by (rule H_derivable.Theorem[OF H_proves.Ref[OF a]])
  have Ra_local: "\<Gamma> ; [?E] \<turnstile>\<^sub>H App ?R a"
    by (rule H_only_local_bicond_right[OF Ra aa H_derivable.Theorem[OF beta_a] reflexivity])
  have LL: "\<Gamma> \<turnstile>\<^sub>H Imp ?E (Imp (App ?R a) (App ?R b))"
    by (rule H_proves.LL[OF a b R])
  have implication: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Imp (App ?R a) (App ?R b)"
    by (rule H_only_local_theorem_MP[OF LL equality])
  have Rb_local: "\<Gamma> ; [?E] \<turnstile>\<^sub>H App ?R b"
    by (rule H_derivable.Derive_MP[OF Ra_local implication])
  have conclusion: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Eq \<sigma> b a"
    by (rule H_only_local_bicond_left[OF Rb ba H_derivable.Theorem[OF beta_b] Rb_local])
  show ?thesis by (rule H_only_deduction[OF E conclusion])
qed

lemma H_only_equality_predicate_biconditional:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
    and F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Eq \<sigma> a b) (App F a \<longleftrightarrow>\<^sub>o App F b)"
proof -
  let ?E = "Eq \<sigma> a b"
  have E: "\<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Eq[OF a b])
  have Fa: "\<Gamma> \<turnstile> App F a : Prop" by (rule has_type.App[OF F a])
  have Fb: "\<Gamma> \<turnstile> App F b : Prop" by (rule has_type.App[OF F b])
  have equality: "\<Gamma> ; [?E] \<turnstile>\<^sub>H ?E" by (rule H_derivable.Assumption[OF _ E]) simp
  have forward: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Imp (App F a) (App F b)"
    by (rule H_only_local_theorem_MP[OF H_proves.LL[OF a b F] equality])
  have symmetric: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Eq \<sigma> b a"
    by (rule H_only_local_theorem_MP[OF H_only_equality_symmetry[OF a b] equality])
  have backward: "\<Gamma> ; [?E] \<turnstile>\<^sub>H Imp (App F b) (App F a)"
    by (rule H_only_local_theorem_MP[OF H_proves.LL[OF b a F] symmetric])
  have local_biconditional: "\<Gamma> ; [?E] \<turnstile>\<^sub>H (App F a \<longleftrightarrow>\<^sub>o App F b)"
    by (rule H_only_local_conj[OF has_type.Imp[OF Fa Fb] has_type.Imp[OF Fb Fa] forward backward])
  show ?thesis by (rule H_only_deduction[OF E local_biconditional])
qed

end
