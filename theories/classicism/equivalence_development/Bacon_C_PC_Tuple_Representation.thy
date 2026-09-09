theory Bacon_C_PC_Tuple_Representation
  imports Bacon_C_PC_Atom_Map Bacon_C_Church_Tuples
begin

section \<open>Representing a Boolean formula by one tuple argument\<close>

text \<open>
  Enumerate the opaque propositional atoms of A by xs = [a₁,…,aₙ].
  Replace aᵢ by z πᵢⁿ to obtain A*(z), and put F := λz:Tₙ.A*(z),
  G := λz:Tₙ.⊤₀.  These are closed operations even when the aᵢ have
  free variables.  Moreover, F⟨xs⟩ ≡βη A and G⟨xs⟩ ≡β ⊤₀.
  Source role: the encoding step for Bacon–Dorr Appendix A.2(i), p.65.

  Isabelle representation.  Atom indexing is used only after proving
  membership in set xs.  Coverage, rather than a positive-length or
  distinctness hypothesis, suffices.  In the n = 0 case there is no atom
  at which a projection is requested.  All conversion lemmas below are
  typed syntactic βη statements; the one-abstraction PC theorem supplies
  the single operation identity F = G.
\<close>

definition C_PC_tuple_atom :: "oterm list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_PC_tuple_atom xs a = App (Var 0) (C_Church_selector (length xs) (C_PC_atom_index xs a))"

definition C_PC_tuple_body :: "oterm list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_PC_tuple_body xs A = C_PC_map_atoms (C_PC_tuple_atom xs) A"

definition C_PC_tuple_operation :: "oterm list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_PC_tuple_operation xs A = Lam (C_Church_tuple_type (length xs)) (C_PC_tuple_body xs A)"

definition C_PC_tuple_truth_operation :: "nat \<Rightarrow> oterm" where
  "C_PC_tuple_truth_operation n = Lam (C_Church_tuple_type n) ObjTrue"

lemma C_PC_tuple_atom_type:
  assumes member: "a \<in> set xs"
  shows "C_Church_tuple_type (length xs) # \<Gamma> \<turnstile> C_PC_tuple_atom xs a : Prop"
proof -
  let ?n = "length xs"
  have index: "C_PC_atom_index xs a < ?n" by (rule conjunct1[OF C_PC_atom_index_spec[OF member]])
  have variable: "C_Church_tuple_type ?n # \<Gamma> \<turnstile> Var 0 : C_Church_argument_type ?n \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: C_Church_tuple_type_def)
  have selector: "C_Church_tuple_type ?n # \<Gamma> \<turnstile>
    C_Church_selector ?n (C_PC_atom_index xs a) : C_Church_argument_type ?n"
    by (rule C_Church_selector_type[OF index])
  show ?thesis unfolding C_PC_tuple_atom_def by (rule has_type.App[OF variable selector])
qed

lemma C_PC_tuple_body_type:
  assumes coverage: "C_PC_atoms A \<subseteq> set xs"
  shows "C_Church_tuple_type (length xs) # \<Gamma> \<turnstile> C_PC_tuple_body xs A : Prop"
  unfolding C_PC_tuple_body_def
  by (rule C_PC_map_atoms_type, rule C_PC_tuple_atom_type, rule subsetD[OF coverage], assumption)

lemma C_PC_tuple_operation_type:
  assumes "C_PC_atoms A \<subseteq> set xs"
  shows "\<Gamma> \<turnstile> C_PC_tuple_operation xs A : C_Church_tuple_type (length xs) \<rightarrow>\<^sub>o Prop"
  unfolding C_PC_tuple_operation_def by (rule has_type.Lam[OF C_PC_tuple_body_type[OF assms]])

lemma C_PC_tuple_truth_operation_type:
  "\<Gamma> \<turnstile> C_PC_tuple_truth_operation n : C_Church_tuple_type n \<rightarrow>\<^sub>o Prop"
  unfolding C_PC_tuple_truth_operation_def by (rule has_type.Lam[OF typed_ObjTrue])

lemma C_PC_tuple_body_tautology:
  assumes tautology: "prop_tautology \<Xi> A" and coverage: "C_PC_atoms A \<subseteq> set xs"
  shows "prop_tautology (C_Church_tuple_type (length xs) # \<Gamma>) (C_PC_tuple_body xs A)"
  unfolding C_PC_tuple_body_def
  by (rule C_PC_map_atoms_tautology[OF tautology], rule C_PC_tuple_atom_type,
    rule subsetD[OF coverage], assumption)

lemma C_PC_tuple_operation_identity:
  assumes tautology: "prop_tautology \<Xi> A" and coverage: "C_PC_atoms A \<subseteq> set xs"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (C_Church_tuple_type (length xs) \<rightarrow>\<^sub>o Prop)
    (C_PC_tuple_operation xs A) (C_PC_tuple_truth_operation (length xs))"
  unfolding C_PC_tuple_operation_def C_PC_tuple_truth_operation_def
  by (rule C_PC_single_abstraction[OF C_PC_tuple_body_tautology[OF tautology coverage]])

subsection \<open>The operation templates have no free slots\<close>

lemma C_PC_tuple_atom_lift_rename:
  "rename (lift_ren r) (C_PC_tuple_atom xs a) = C_PC_tuple_atom xs a"
  by (simp only: C_PC_tuple_atom_def rename.simps lift_ren.simps C_Church_selector_closed)

lemma C_PC_tuple_body_lift_rename:
  "rename (lift_ren r) (C_PC_tuple_body xs A) = C_PC_tuple_body xs A"
  unfolding C_PC_tuple_body_def C_PC_map_atoms_rename
  by (rule C_PC_map_atoms_agreement) (rule C_PC_tuple_atom_lift_rename)

lemma C_PC_tuple_operation_closed:
  "rename r (C_PC_tuple_operation xs A) = C_PC_tuple_operation xs A"
  by (simp only: C_PC_tuple_operation_def rename.simps C_PC_tuple_body_lift_rename)

lemma C_PC_tuple_operation_raise:
  "C_vector_raise n (C_PC_tuple_operation xs A) = C_PC_tuple_operation xs A"
  by (induction n) (simp_all only: C_vector_raise.simps C_PC_tuple_operation_closed)

lemma C_PC_tuple_truth_operation_closed:
  "rename r (C_PC_tuple_truth_operation n) = C_PC_tuple_truth_operation n"
  by (simp add: C_PC_tuple_truth_operation_def ObjTrue_def)

lemma C_PC_tuple_truth_operation_raise:
  "C_vector_raise k (C_PC_tuple_truth_operation n) = C_PC_tuple_truth_operation n"
  by (induction k) (simp_all only: C_vector_raise.simps C_PC_tuple_truth_operation_closed)

subsection \<open>Substitution turns abstract atoms into tuple projections\<close>

lemma C_PC_tuple_body_subst0:
  "subst0 W (C_PC_tuple_body xs A) =
    C_PC_map_atoms (\<lambda>a. App W (C_Church_selector (length xs) (C_PC_atom_index xs a))) A"
  by (simp add: subst0_def C_PC_tuple_body_def C_PC_map_atoms_subst
    C_PC_tuple_atom_def C_Church_selector_subst)

lemma C_PC_tuple_instance_conversion:
  assumes args: "\<And>a. a \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> a : Prop"
    and coverage: "C_PC_atoms A \<subseteq> set xs"
  shows "beta_eta_equiv \<Gamma> Prop (subst0 (C_Church_tuple xs) (C_PC_tuple_body xs A)) A"
proof -
  have projection: "beta_eta_equiv \<Gamma> Prop
    (App (C_Church_tuple xs) (C_Church_selector (length xs) (C_PC_atom_index xs a))) a"
    if atom: "a \<in> C_PC_atoms A" for a
  proof -
    have member: "a \<in> set xs" by (rule subsetD[OF coverage atom])
    have index: "C_PC_atom_index xs a < length xs" and selected: "xs ! C_PC_atom_index xs a = a"
      using C_PC_atom_index_spec[OF member] by blast+
    have raw: "beta_eta_equiv \<Gamma> Prop
      (App (C_Church_tuple xs) (C_Church_selector (length xs) (C_PC_atom_index xs a)))
      (xs ! C_PC_atom_index xs a)"
      by (rule C_Church_tuple_projection[OF args index])
    show ?thesis using raw by (simp only: selected)
  qed
  show ?thesis unfolding C_PC_tuple_body_subst0 by (rule C_PC_map_atoms_projection[OF projection])
qed

lemma C_PC_tuple_application_conversion:
  assumes args: "\<And>a. a \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> a : Prop"
    and coverage: "C_PC_atoms A \<subseteq> set xs"
  shows "beta_eta_equiv \<Gamma> Prop (App (C_PC_tuple_operation xs A) (C_Church_tuple xs)) A"
proof -
  have operator: "\<Gamma> \<turnstile> C_PC_tuple_operation xs A : C_Church_tuple_type (length xs) \<rightarrow>\<^sub>o Prop"
    by (rule C_PC_tuple_operation_type[OF coverage])
  have tuple: "\<Gamma> \<turnstile> C_Church_tuple xs : C_Church_tuple_type (length xs)" by (rule C_Church_tuple_type[OF args])
  have source: "\<Gamma> \<turnstile> App (C_PC_tuple_operation xs A) (C_Church_tuple xs) : Prop"
    by (rule has_type.App[OF operator tuple])
  have projections: "beta_eta_equiv \<Gamma> Prop (subst0 (C_Church_tuple xs) (C_PC_tuple_body xs A)) A"
    by (rule C_PC_tuple_instance_conversion[OF args coverage])
  have middle: "\<Gamma> \<turnstile> subst0 (C_Church_tuple xs) (C_PC_tuple_body xs A) : Prop"
    by (rule beta_eta_equiv_left_type[OF projections])
  have step: "compatible_step beta_contract (App (C_PC_tuple_operation xs A) (C_Church_tuple xs))
    (subst0 (C_Church_tuple xs) (C_PC_tuple_body xs A))"
    unfolding C_PC_tuple_operation_def by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  show ?thesis by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle step] projections])
qed

lemma C_PC_tuple_truth_application_conversion:
  assumes tuple: "\<Gamma> \<turnstile> W : C_Church_tuple_type n"
  shows "beta_eta_equiv \<Gamma> Prop (App (C_PC_tuple_truth_operation n) W) ObjTrue"
proof -
  have source: "\<Gamma> \<turnstile> App (C_PC_tuple_truth_operation n) W : Prop"
    by (rule has_type.App[OF C_PC_tuple_truth_operation_type tuple])
  have raw: "compatible_step beta_contract (App (C_PC_tuple_truth_operation n) W) (subst0 W ObjTrue)"
    unfolding C_PC_tuple_truth_operation_def by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have step: "compatible_step beta_contract (App (C_PC_tuple_truth_operation n) W) ObjTrue"
    using raw by (simp add: subst0_def ObjTrue_def)
  show ?thesis by (rule beta_eta_equiv.Beta[OF source typed_ObjTrue step])
qed

end
