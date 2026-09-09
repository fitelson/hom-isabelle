theory Bacon_Source_BBK_Global_Assignments
  imports Bacon_Source_BBK_Roundtrip Bacon_Source_Global_Proof_Preservation
begin

section \<open>Total assignments to the represented global variable stock\<close>

text \<open>
  An assignment g is typed for the total stock G when g(n) ∈ D(G(n))
  for every slot n.  It is then typed for each finite prefix of G.
  Source role: interpreting the finite-prefix proof translation without
  restricting the global stock to the conclusion's free variables.

  Isabelle representation.  paper_global_env_typed is a total assignment
  predicate; source_prefix G m is the existing first-m-slots frame.
  Status.  This does not identify total assignments with the paper's
  adequate partial named assignments.  No such representation bridge or
  source-model soundness theorem is assumed or proved in this leaf.
\<close>

definition paper_global_env_typed ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> bool" where
  "paper_global_env_typed D G g \<longleftrightarrow> (\<forall>n. g n \<in> D (G n))"

lemma paper_global_env_at:
  assumes env: "paper_global_env_typed D G g"
  shows "g n \<in> D (G n)"
  by (rule spec[where x=n, OF env[unfolded paper_global_env_typed_def]])

lemma paper_global_env_prefix:
  assumes env: "paper_global_env_typed D G g"
  shows "pbbk_env_typed D (source_prefix G m) g"
proof (unfold pbbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume index: "lookup (source_prefix G m) n = Some \<sigma>"
  have bound: "n < m" using index by (auto simp: source_prefix_def lookup_def split: if_splits)
  have source_index: "lookup (source_prefix G m) n = Some (G n)" by (rule source_prefix_lookup[OF bound])
  have type_eq: "G n = \<sigma>" using index source_index by simp
  show "g n \<in> D \<sigma>" using paper_global_env_at[OF env, where n=n] by (simp only: type_eq)
qed

lemma paper_global_env_prefix_iff:
  "paper_global_env_typed D G g \<longleftrightarrow> (\<forall>m. pbbk_env_typed D (source_prefix G m) g)"
proof
  assume env: "paper_global_env_typed D G g"
  show "\<forall>m. pbbk_env_typed D (source_prefix G m) g"
    by (rule allI, rule paper_global_env_prefix[OF env])
next
  assume prefixes: "\<forall>m. pbbk_env_typed D (source_prefix G m) g"
  show "paper_global_env_typed D G g"
  proof (unfold paper_global_env_typed_def, rule allI)
    fix n
    have env: "pbbk_env_typed D (source_prefix G (Suc n)) g"
      by (rule spec[where x="Suc n", OF prefixes])
    have index: "lookup (source_prefix G (Suc n)) n = Some (G n)"
      by (rule source_prefix_lookup) simp
    show "g n \<in> D (G n)" by (rule pbbk_env_lookup[OF env index])
  qed
qed

lemma paper_global_env_exists:
  assumes nonempty: "\<And>\<sigma>. D \<sigma> \<noteq> {}"
  shows "\<exists>g. paper_global_env_typed D G g"
proof -
  let ?g = "\<lambda>n. SOME a. a \<in> D (G n)"
  have env: "paper_global_env_typed D G ?g"
  proof (unfold paper_global_env_typed_def, rule allI)
    fix n
    have witness: "\<exists>a. a \<in> D (G n)" using nonempty[of "G n"] by blast
    show "(SOME a. a \<in> D (G n)) \<in> D (G n)" by (rule someI_ex[OF witness])
  qed
  show ?thesis by (rule exI[where x="?g"], rule env)
qed

text \<open>
  The existence lemma selects semantic domain elements.  It assumes no
  closed term of any type in Σ and proves no named-assignment completion
  or model existence claim.
\<close>

context paper_db_bbk_structure
begin

lemma paper_db_global_denote_type:
  assumes language: "sgterm_in_language paper_logical_type signature G A \<tau>"
    and env: "paper_global_env_typed domain G g"
  shows "denote g A \<in> domain \<tau>"
proof -
  have finite_language: "sterm_in_language paper_logical_type signature
    (source_prefix G (source_free_bound A)) A \<tau>"
    by (rule source_language_in_prefix[OF language]) (rule order_refl)
  show ?thesis by (rule denote_type[OF finite_language paper_global_env_prefix[OF env]])
qed

theorem paper_db_global_roundtrip_denotation:
  assumes language: "sgterm_in_language paper_logical_type signature G A \<tau>"
    and env: "paper_global_env_typed domain G g"
  shows "denote g (pterm_to_paper (paper_to_pterm A)) = denote g A"
proof -
  have finite_language: "sterm_in_language paper_logical_type signature
    (source_prefix G (source_free_bound A)) A \<tau>"
    by (rule source_language_in_prefix[OF language]) (rule order_refl)
  have finite_env: "pbbk_env_typed domain (source_prefix G (source_free_bound A)) g"
    by (rule paper_global_env_prefix[OF env])
  show ?thesis by (rule paper_db_roundtrip_denotation[OF finite_language finite_env])
qed

end

section \<open>Translated proofs and their typed environments share a prefix\<close>

text \<open>
  Every global source H proof has a bound N such that its target proof
  exists in every prefix m ≥ N.  A globally typed g is a typed environment
  for each of those proof frames.  Status.  This combines proof transport
  with assignment typing; semantic truth of the proof conclusion is not
  asserted until a separately constructed target model and soundness
  theorem are supplied.
\<close>

theorem paper_global_H_target_prefix_with_env:
  assumes derivation: "paper_global_H \<Sigma> G A"
    and env: "paper_global_env_typed D G g"
  shows "\<exists>N. \<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A) \<and>
    pbbk_env_typed D (source_prefix G m) g"
proof -
  obtain N where proofs: "\<forall>m\<ge>N. pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
    using paper_global_H_target_eventual[OF derivation] unfolding paper_target_eventual_def by (elim exE)
  show ?thesis
  proof (rule exI[where x=N], intro allI impI)
    fix m
    assume bound: "N \<le> m"
    have proof_m: "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A)"
      using proofs bound by blast
    show "pH_proves \<Sigma> (source_prefix G m) (paper_to_pterm A) \<and> pbbk_env_typed D (source_prefix G m) g"
      by (rule conjI[OF proof_m paper_global_env_prefix[OF env]])
  qed
qed

end
