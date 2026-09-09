theory Bacon_C_PC_Atom_Map
  imports Bacon_C_PC_Beta_Congruence
begin

section \<open>Uniform substitution for propositional atoms\<close>

text \<open>
  Replace each propositional atom a of A by f(a), leaving the Boolean
  structure unchanged. A tautology remains a tautology under this
  substitution. This is the propositional substitution step in
  Bacon--Dorr Appendix A.2(i), p.65.

  Isabelle representation: C_PC_map_atoms follows exactly prop_eval and
  C_PC_atoms. Applications, quantifiers, and identity formulas are opaque
  at their outermost occurrence. The replacement formulas may live in a
  different variable context from the original formula: their typing is
  the only typing needed to construct the resulting Boolean formula.
  This allows replacing atoms by projections of one tuple variable.

  Status: syntactic substitution, typing, and propositional validity.
  No C identity is inferred from validity here. The checked one-binder PC
  theorem will supply the operation identity in the subsequent construction.
\<close>

fun C_PC_map_atoms :: "(oterm \<Rightarrow> oterm) \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_PC_map_atoms f (Neg A) = Neg (C_PC_map_atoms f A)"
| "C_PC_map_atoms f (Conj A B) = Conj (C_PC_map_atoms f A) (C_PC_map_atoms f B)"
| "C_PC_map_atoms f (Disj A B) = Disj (C_PC_map_atoms f A) (C_PC_map_atoms f B)"
| "C_PC_map_atoms f (Imp A B) = Imp (C_PC_map_atoms f A) (C_PC_map_atoms f B)"
| "C_PC_map_atoms f A = f A"

lemma C_PC_map_atoms_eval:
  "prop_eval w (C_PC_map_atoms f A) = prop_eval (\<lambda>a. prop_eval w (f a)) A"
  by (induction A) simp_all

lemma C_PC_map_atoms_agreement:
  assumes "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> f a = g a"
  shows "C_PC_map_atoms f A = C_PC_map_atoms g A"
  using assms by (induction A) auto

lemma C_PC_map_atoms_identity:
  assumes "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> f a = a"
  shows "C_PC_map_atoms f A = A"
  using assms by (induction A) auto

lemma C_PC_map_atoms_rename:
  "rename r (C_PC_map_atoms f A) = C_PC_map_atoms (\<lambda>a. rename r (f a)) A"
  by (induction A) simp_all

lemma C_PC_map_atoms_subst:
  "subst s (C_PC_map_atoms f A) = C_PC_map_atoms (\<lambda>a. subst s (f a)) A"
  by (induction A) simp_all

lemma C_PC_map_atoms_type:
  assumes atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> \<Gamma> \<turnstile> f a : Prop"
  shows "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
  using atoms
proof (induction A)
  case (Neg A)
  have body: "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
    by (rule Neg.IH) (rule Neg.prems, simp)
  show ?case by (simp only: C_PC_map_atoms.simps; rule has_type.Neg[OF body])
next
  case (Conj A B)
  have left: "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
    by (rule Conj.IH(1)) (rule Conj.prems, simp)
  have right: "\<Gamma> \<turnstile> C_PC_map_atoms f B : Prop"
    by (rule Conj.IH(2)) (rule Conj.prems, simp)
  show ?case by (simp only: C_PC_map_atoms.simps; rule has_type.Conj[OF left right])
next
  case (Disj A B)
  have left: "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
    by (rule Disj.IH(1)) (rule Disj.prems, simp)
  have right: "\<Gamma> \<turnstile> C_PC_map_atoms f B : Prop"
    by (rule Disj.IH(2)) (rule Disj.prems, simp)
  show ?case by (simp only: C_PC_map_atoms.simps; rule has_type.Disj[OF left right])
next
  case (Imp A B)
  have left: "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
    by (rule Imp.IH(1)) (rule Imp.prems, simp)
  have right: "\<Gamma> \<turnstile> C_PC_map_atoms f B : Prop"
    by (rule Imp.IH(2)) (rule Imp.prems, simp)
  show ?case by (simp only: C_PC_map_atoms.simps; rule has_type.Imp[OF left right])
next
  case (Var n)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Var.prems) simp
next
  case (Const c \<tau>)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Const.prems) simp
next
  case (App F B)
  show ?case by (simp only: C_PC_map_atoms.simps; rule App.prems) simp
next
  case (Lam \<tau> B)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Lam.prems) simp
next
  case (Eq \<tau> B D)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Eq.prems) simp
next
  case (Forall \<tau> B)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Forall.prems) simp
next
  case (Exists \<tau> B)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Exists.prems) simp
qed

theorem C_PC_map_atoms_tautology:
  assumes tautology: "prop_tautology \<Delta> A"
    and atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> \<Gamma> \<turnstile> f a : Prop"
  shows "prop_tautology \<Gamma> (C_PC_map_atoms f A)"
proof -
  have typed: "\<Gamma> \<turnstile> C_PC_map_atoms f A : Prop"
    by (rule C_PC_map_atoms_type[OF atoms])
  have valid: "\<forall>w. prop_eval w A"
    using tautology unfolding prop_tautology_def by (rule conjunct2)
  have mapped: "\<forall>w. prop_eval w (C_PC_map_atoms f A)"
  proof (rule allI)
    fix w
    have truth: "prop_eval (\<lambda>a. prop_eval w (f a)) A"
      by (rule spec[where x="\<lambda>a. prop_eval w (f a)", OF valid])
    show "prop_eval w (C_PC_map_atoms f A)"
      using truth by (simp only: C_PC_map_atoms_eval)
  qed
  show ?thesis unfolding prop_tautology_def by (rule conjI[OF typed mapped])
qed

section \<open>Projection conversions propagate through the whole formula\<close>

lemma C_PC_map_atoms_conversion:
  assumes atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> beta_eta_equiv \<Gamma> Prop (f a) (g a)"
  shows "beta_eta_equiv \<Gamma> Prop (C_PC_map_atoms f A) (C_PC_map_atoms g A)"
  using atoms
proof (induction A)
  case (Neg A)
  show ?case
    by (simp only: C_PC_map_atoms.simps; rule C_PC_beta_eta_Neg)
      (rule Neg.IH; rule Neg.prems; simp)
next
  case (Conj A B)
  show ?case
    by (simp only: C_PC_map_atoms.simps; rule C_PC_beta_eta_Conj;
      (rule Conj.IH(1) | rule Conj.IH(2)); rule Conj.prems; simp)
next
  case (Disj A B)
  show ?case
    by (simp only: C_PC_map_atoms.simps; rule C_PC_beta_eta_Disj;
      (rule Disj.IH(1) | rule Disj.IH(2)); rule Disj.prems; simp)
next
  case (Imp A B)
  show ?case
    by (simp only: C_PC_map_atoms.simps; rule C_PC_beta_eta_Imp;
      (rule Imp.IH(1) | rule Imp.IH(2)); rule Imp.prems; simp)
next
  case (Var n)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Var.prems) simp
next
  case (Const c \<tau>)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Const.prems) simp
next
  case (App M N)
  show ?case by (simp only: C_PC_map_atoms.simps; rule App.prems) simp
next
  case (Lam \<tau> M)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Lam.prems) simp
next
  case (Eq \<tau> M N)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Eq.prems) simp
next
  case (Forall \<tau> M)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Forall.prems) simp
next
  case (Exists \<tau> M)
  show ?case by (simp only: C_PC_map_atoms.simps; rule Exists.prems) simp
qed

corollary C_PC_map_atoms_projection:
  assumes projections: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> beta_eta_equiv \<Gamma> Prop (f a) a"
  shows "beta_eta_equiv \<Gamma> Prop (C_PC_map_atoms f A) A"
proof -
  have conversions: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> beta_eta_equiv \<Gamma> Prop (f a) (id a)"
    using projections by simp
  have mapped: "beta_eta_equiv \<Gamma> Prop (C_PC_map_atoms f A) (C_PC_map_atoms id A)"
    by (rule C_PC_map_atoms_conversion[OF conversions])
  show ?thesis using mapped by (simp only: C_PC_map_atoms_identity[where f=id, OF id_apply])
qed

definition C_PC_atom_index :: "oterm list \<Rightarrow> oterm \<Rightarrow> nat" where
  "C_PC_atom_index xs a = (SOME i. i < length xs \<and> xs ! i = a)"

lemma C_PC_atom_index_spec:
  assumes member: "a \<in> set xs"
  shows "C_PC_atom_index xs a < length xs \<and> xs ! C_PC_atom_index xs a = a"
proof -
  have witness: "\<exists>i. i < length xs \<and> xs ! i = a"
    using member by (simp only: in_set_conv_nth)
  show ?thesis unfolding C_PC_atom_index_def by (rule someI_ex[OF witness])
qed

end
