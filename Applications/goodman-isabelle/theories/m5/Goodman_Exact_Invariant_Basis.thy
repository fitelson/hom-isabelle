theory Goodman_Exact_Invariant_Basis
  imports Goodman_Integration_Exact_M.Goodman_Exact_M3_Algebra
begin

section \<open>A countable invariant basis in Bacon's unchanged exact carriers\<close>

definition gi_basis_pure ::
  "(otype \<Rightarrow> ZF set) \<Rightarrow> otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "gi_basis_pure B \<sigma> w x \<longleftrightarrow>
    Elem x (pp_e_domain \<sigma>) \<and> (\<exists>a\<in>B \<sigma>. pp_e_eqv \<sigma> w x a)"

locale gi_exact_invariant_basis =
  fixes B :: "otype \<Rightarrow> ZF set"
  assumes basis_member: "\<And>\<sigma> x. x \<in> B \<sigma> \<Longrightarrow> Elem x (pp_e_domain \<sigma>)"
    and basis_invariant: "\<And>\<sigma> x i. x \<in> B \<sigma> \<Longrightarrow> pp_b_action \<sigma> i x = x"
    and basis_countable: "\<And>\<sigma>. countable (B \<sigma>)"
    and basis_application: "\<And>\<sigma> \<tau> f x. f \<in> B (Arr \<sigma> \<tau>) \<Longrightarrow> x \<in> B \<sigma> \<Longrightarrow> f \<acute> x \<in> B \<tau>"
    and basis_logical: "\<And>\<sigma> M. [] \<turnstile> M : \<sigma> \<Longrightarrow> pp_logical_vocabulary M \<Longrightarrow> pp_e_closed_den M \<in> B \<sigma>"
begin

lemma gi_basis_pure_member:
  "gi_basis_pure B \<sigma> w x \<Longrightarrow> Elem x (pp_e_domain \<sigma>)"
  unfolding gi_basis_pure_def by blast

lemma gi_basis_pureI:
  assumes member: "x \<in> B \<sigma>"
  shows "gi_basis_pure B \<sigma> w x"
  unfolding gi_basis_pure_def
  using member basis_member[OF member] pp_e_eqv_reflexive[OF basis_member[OF member]] by blast

lemma gi_basis_pure_persistent:
  assumes pure: "gi_basis_pure B \<sigma> w x" and future: "prefix w v"
  shows "gi_basis_pure B \<sigma> v x"
proof -
  obtain a where xm: "Elem x (pp_e_domain \<sigma>)" and ab: "a \<in> B \<sigma>"
    and related: "pp_e_eqv \<sigma> w x a" using pure unfolding gi_basis_pure_def by blast
  have later: "pp_e_eqv \<sigma> v x a" by (rule pp_e_eqv_persistent[OF related future])
  show ?thesis unfolding gi_basis_pure_def using xm ab later by blast
qed

theorem gi_basis_pure_admissible:
  "pp_e_predicate_admissible \<sigma> (gi_basis_pure B \<sigma>)"
proof (unfold pp_e_predicate_admissible_def, intro allI impI)
  fix w x y v
  assume xm: "Elem x (pp_e_domain \<sigma>)" and ym: "Elem y (pp_e_domain \<sigma>)"
    and xy: "pp_e_eqv \<sigma> w x y" and future: "prefix w v"
  have later: "pp_e_eqv \<sigma> v x y" by (rule pp_e_eqv_persistent[OF xy future])
  have reverse: "pp_e_eqv \<sigma> v y x" by (rule pp_e_eqv_symmetric[OF xm ym later])
  show "gi_basis_pure B \<sigma> v x = gi_basis_pure B \<sigma> v y"
  proof
    assume left: "gi_basis_pure B \<sigma> v x"
    then obtain a where am: "a \<in> B \<sigma>" and xa: "pp_e_eqv \<sigma> v x a"
      unfolding gi_basis_pure_def by blast
    have ya: "pp_e_eqv \<sigma> v y a" by (rule pp_e_eqv_transitive[OF ym xm basis_member[OF am] reverse xa])
    show "gi_basis_pure B \<sigma> v y" unfolding gi_basis_pure_def using ym am ya by blast
  next
    assume right: "gi_basis_pure B \<sigma> v y"
    then obtain a where am: "a \<in> B \<sigma>" and ya: "pp_e_eqv \<sigma> v y a"
      unfolding gi_basis_pure_def by blast
    have xa: "pp_e_eqv \<sigma> v x a" by (rule pp_e_eqv_transitive[OF xm ym basis_member[OF am] later ya])
    show "gi_basis_pure B \<sigma> v x" unfolding gi_basis_pure_def using xm am xa by blast
  qed
qed

theorem gi_basis_pure_application_closed:
  assumes fs: "gi_basis_pure B (Arr \<sigma> \<tau>) w f" and xs: "gi_basis_pure B \<sigma> w x"
  shows "gi_basis_pure B \<tau> w (f \<acute> x)"
proof -
  obtain a where fm: "Elem f (pp_e_domain (Arr \<sigma> \<tau>))" and ab: "a \<in> B (Arr \<sigma> \<tau>)"
    and fa: "pp_e_eqv (Arr \<sigma> \<tau>) w f a" using fs unfolding gi_basis_pure_def by blast
  obtain b where xm: "Elem x (pp_e_domain \<sigma>)" and bb: "b \<in> B \<sigma>"
    and xb: "pp_e_eqv \<sigma> w x b" using xs unfolding gi_basis_pure_def by blast
  have value_member: "Elem (f \<acute> x) (pp_e_domain \<tau>)" by (rule pp_e_app_closed[OF fm xm])
  have basis_value: "a \<acute> b \<in> B \<tau>" by (rule basis_application[OF ab bb])
  have related: "pp_e_eqv \<tau> w (f \<acute> x) (a \<acute> b)"
    by (rule pp_e_app_respects[OF fa xm basis_member[OF bb] xb])
  show ?thesis unfolding gi_basis_pure_def using value_member basis_value related by blast
qed

theorem gi_basis_pure_logical_denotation:
  "[] \<turnstile> M : \<sigma> \<Longrightarrow> pp_logical_vocabulary M \<Longrightarrow> gi_basis_pure B \<sigma> w (pp_e_closed_den M)"
  by (rule gi_basis_pureI, rule basis_logical; assumption)

theorem gi_basis_contains_logical_eval:
  assumes typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
  shows "gi_basis_pure B \<sigma> w (pp_e_eval C \<rho> M)"
  by (simp only: gi_exact_old_closed_evaluation[OF typed logical];
    rule gi_basis_pure_logical_denotation[OF typed logical])

theorem gi_basis_contains_native_closed_logical:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_basis_pure B \<sigma> w (gi_exact_goodman_denote C G g A)"
  by (simp only: gi_goodman_closed_logical_decode_denotation(3)[OF logical];
    rule gi_basis_pure_logical_denotation[OF gi_goodman_closed_logical_decode_denotation(1)[OF logical]
      gi_goodman_closed_logical_decode_denotation(2)[OF logical]])

theorem gi_basis_pure_classifier_member:
  "Elem (pp_e_classifier \<sigma> (gi_basis_pure B \<sigma>)) (pp_e_domain (Arr \<sigma> Prop))"
  by (rule pp_e_classifier_in_domain[OF gi_basis_pure_admissible])

theorem gi_basis_pure_iff_action_member:
  assumes xm: "Elem x (pp_e_domain \<sigma>)"
  shows "gi_basis_pure B \<sigma> w x \<longleftrightarrow> pp_b_action \<sigma> (rev w) x \<in> B \<sigma>"
proof
  assume pure: "gi_basis_pure B \<sigma> w x"
  then obtain a where ab: "a \<in> B \<sigma>" and xa: "pp_e_eqv \<sigma> w x a"
    unfolding gi_basis_pure_def by blast
  have equal: "pp_b_action \<sigma> (rev w) x = a"
    using xa by (simp only: pp_e_eqv_iff_action_eq[OF xm basis_member[OF ab]] basis_invariant[OF ab])
  show "pp_b_action \<sigma> (rev w) x \<in> B \<sigma>" using ab by (simp only: equal)
next
  assume ab: "pp_b_action \<sigma> (rev w) x \<in> B \<sigma>"
  have related: "pp_e_eqv \<sigma> w x (pp_b_action \<sigma> (rev w) x)"
    by (simp only: pp_e_eqv_iff_action_eq[OF xm basis_member[OF ab]] basis_invariant[OF ab])
  show "gi_basis_pure B \<sigma> w x" unfolding gi_basis_pure_def using xm ab related by blast
qed

corollary gi_basis_pure_root_iff:
  "gi_basis_pure B \<sigma> [] x \<longleftrightarrow> x \<in> B \<sigma>"
proof
  assume pure: "gi_basis_pure B \<sigma> [] x"
  have xm: "Elem x (pp_e_domain \<sigma>)" by (rule gi_basis_pure_member[OF pure])
  show "x \<in> B \<sigma>"
    using pure by (simp only: gi_basis_pure_iff_action_member[OF xm] rev.simps pp_b_action_one_all[OF xm])
next
  assume "x \<in> B \<sigma>"
  then show "gi_basis_pure B \<sigma> [] x" by (rule gi_basis_pureI)
qed

corollary gi_basis_pure_all_worlds_iff_root:
  "(\<forall>w. gi_basis_pure B \<sigma> w x) \<longleftrightarrow> gi_basis_pure B \<sigma> [] x"
proof
  assume "\<forall>w. gi_basis_pure B \<sigma> w x"
  then show "gi_basis_pure B \<sigma> [] x" by blast
next
  assume root: "gi_basis_pure B \<sigma> [] x"
  show "\<forall>w. gi_basis_pure B \<sigma> w x"
  proof
    fix w show "gi_basis_pure B \<sigma> w x"
      by (rule gi_basis_pure_persistent[OF root]; simp)
  qed
qed

end

text \<open>
  These assumptions concern a basis of actual values in the unchanged
  exact carriers, not a replacement of the carriers. Countability and
  invariance will support the generic witness construction. PP remains
  a separate higher-type membership obligation: admissibility supplies
  the classifier as a carrier value, not membership in the basis.
\<close>

end
