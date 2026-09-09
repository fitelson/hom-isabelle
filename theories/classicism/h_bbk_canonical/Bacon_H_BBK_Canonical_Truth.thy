theory Bacon_H_BBK_Canonical_Truth
  imports Bacon_H_BBK_Canonical_Domain
begin

section \<open>Truth in the canonical identity classes\<close>

text \<open>
  v([A]ₜ) = 1 ⇔ A ∈ T. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp.
  320–321.

  Isabelle representation: H_BBK_holds uses membership of a chosen representative. H
  identity and Leibniz substitution ensure that truth is independent of that choice.

  Status: Boolean truth and actual-equality clauses are proved without collapsing
  same-truth propositions.
\<close>

context H_closed_Henkin
begin

definition H_BBK_holds :: "h_bbk_value \<Rightarrow> bool" where
  "H_BBK_holds v \<longleftrightarrow> fst v = Prop \<and> H_BBK_rep v \<in> T"

lemma H_BBK_holds_class:
  assumes typed: "[] \<turnstile> P : Prop"
  shows "H_BBK_holds (H_BBK_class Prop P) \<longleftrightarrow> P \<in> T"
proof -
  have eq: "H_term_eq Prop (H_BBK_rep (H_BBK_class Prop P)) P"
    by (rule H_BBK_rep_class_eq[OF typed])
  have same_truth: "H_BBK_rep (H_BBK_class Prop P) \<in> T \<longleftrightarrow> P \<in> T"
    by (rule H_term_eq_prop_truth_iff[OF eq])
  have tag: "fst (H_BBK_class Prop P) = Prop" by (simp only: H_BBK_class_def fst_conv)
  show ?thesis by (simp only: H_BBK_holds_def tag same_truth simp_thms)
qed

lemma H_BBK_holds_member:
  assumes domain: "v \<in> H_BBK_domain Prop" and member: "P \<in> snd v"
  shows "H_BBK_holds v \<longleftrightarrow> P \<in> T"
proof -
  have tag: "fst v = Prop" by (rule H_BBK_domain_tag[OF domain])
  have reconstruction: "H_BBK_class Prop (H_BBK_rep v) = v"
    by (rule H_BBK_rep_reconstruct[OF domain])
  have class_eq: "snd v = H_term_class Prop (H_BBK_rep v)"
    using arg_cong[where f=snd, OF reconstruction] by (simp only: H_BBK_class_def snd_conv)
  have eq: "H_term_eq Prop (H_BBK_rep v) P"
    using member by (simp only: class_eq H_term_class_def mem_Collect_eq)
  have same_truth: "H_BBK_rep v \<in> T \<longleftrightarrow> P \<in> T"
    by (rule H_term_eq_prop_truth_iff[OF eq])
  show ?thesis by (simp only: H_BBK_holds_def tag same_truth simp_thms)
qed

subsection \<open>The membership truth lemma for represented assignments\<close>

text \<open>
  v(⟦A⟧g) = 1 ⇔ A[s] ∈ T, where s chooses closed representatives of g. Bacon–Dorr,
  Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: The first result uses H_BBK_rep; the second allows every
  type-respecting selector of the same classes.

  Status: Assignment-level membership truth, not merely a valuation on closed sentence
  names.
\<close>

lemma H_BBK_closed_instance_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) M : \<tau>"
  by (rule term_subst_preserves_typing[OF typed H_BBK_rep_substitution_typed[OF env]])

lemma H_BBK_truth_lemma:
  assumes typed: "\<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> A) \<longleftrightarrow>
    subst (\<lambda>n. H_BBK_rep (\<rho> n)) A \<in> T"
proof -
  have closed_type: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) A : Prop"
    by (rule H_BBK_closed_instance_type[OF typed env])
  show ?thesis
    by (simp only: H_BBK_den_typed_form[OF typed] H_BBK_holds_class[OF closed_type])
qed

lemma H_BBK_truth_representatives:
  assumes typed: "\<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
    and s_typed: "term_subst_typed \<Gamma> [] s"
    and represents: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_BBK_class \<sigma> (s n) = \<rho> n"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> A) \<longleftrightarrow> subst s A \<in> T"
proof -
  have denotation: "H_BBK_den \<Gamma> \<rho> A = H_BBK_class Prop (subst s A)"
    by (rule H_BBK_den_representatives[where \<Gamma>=\<Gamma> and M=A and \<tau>=Prop
          and \<rho>=\<rho> and s=s, OF typed env s_typed represents])
  have closed_type: "[] \<turnstile> subst s A : Prop"
    by (rule term_subst_preserves_typing[OF typed s_typed])
  show ?thesis by (simp only: denotation H_BBK_holds_class[OF closed_type])
qed

subsection \<open>Truth-functional connectives\<close>

text \<open>
  𝔐,g ⊨ ¬A ⇔ 𝔐,g ⊭ A; v(⟦A ∧ B⟧g) = v(⟦A⟧g) ∧ v(⟦B⟧g), with the analogous ∨ and ⇒
  clauses. Bacon–Dorr, Definition 3.1, pp. 43–44.

  Isabelle representation: The implemented Imp constructor remains primitive; it is
  not replaced inside identities by a truth-equivalent source abbreviation.

  Status: These are truth-value clauses, not identities between arbitrary proposition
  denotations.
\<close>

lemma H_BBK_truth_Neg:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Neg A)) \<longleftrightarrow>
    \<not> H_BBK_holds (H_BBK_den \<Gamma> \<rho> A)"
proof -
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have closed_A: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) A : Prop"
    by (rule H_BBK_closed_instance_type[OF A env])
  show ?thesis
    using H_Henkin_neg_mem_iff[OF henkin closed_A]
    by (simp only: H_BBK_truth_lemma[OF neg_type env] H_BBK_truth_lemma[OF A env] subst.simps)
qed

lemma H_BBK_truth_Conj:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Conj A B)) \<longleftrightarrow>
    H_BBK_holds (H_BBK_den \<Gamma> \<rho> A) \<and> H_BBK_holds (H_BBK_den \<Gamma> \<rho> B)"
proof -
  have conjunction_type: "\<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have closed_A: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) A : Prop"
    by (rule H_BBK_closed_instance_type[OF A env])
  have closed_B: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) B : Prop"
    by (rule H_BBK_closed_instance_type[OF B env])
  show ?thesis
    using H_Henkin_conj_mem_iff[OF henkin closed_A closed_B]
    by (simp only: H_BBK_truth_lemma[OF conjunction_type env] H_BBK_truth_lemma[OF A env]
          H_BBK_truth_lemma[OF B env] subst.simps)
qed

lemma H_BBK_truth_Disj:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Disj A B)) \<longleftrightarrow>
    H_BBK_holds (H_BBK_den \<Gamma> \<rho> A) \<or> H_BBK_holds (H_BBK_den \<Gamma> \<rho> B)"
proof -
  have disjunction_type: "\<Gamma> \<turnstile> Disj A B : Prop" by (rule has_type.Disj[OF A B])
  have closed_A: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) A : Prop"
    by (rule H_BBK_closed_instance_type[OF A env])
  have closed_B: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) B : Prop"
    by (rule H_BBK_closed_instance_type[OF B env])
  show ?thesis
    using H_Henkin_disj_mem_iff[OF henkin closed_A closed_B]
    by (simp only: H_BBK_truth_lemma[OF disjunction_type env] H_BBK_truth_lemma[OF A env]
          H_BBK_truth_lemma[OF B env] subst.simps)
qed

lemma H_BBK_truth_Imp:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Imp A B)) \<longleftrightarrow>
    (H_BBK_holds (H_BBK_den \<Gamma> \<rho> A) \<longrightarrow> H_BBK_holds (H_BBK_den \<Gamma> \<rho> B))"
proof -
  have implication_type: "\<Gamma> \<turnstile> Imp A B : Prop" by (rule has_type.Imp[OF A B])
  have closed_A: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) A : Prop"
    by (rule H_BBK_closed_instance_type[OF A env])
  have closed_B: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) B : Prop"
    by (rule H_BBK_closed_instance_type[OF B env])
  show ?thesis
    using H_Henkin_imp_mem_iff[OF henkin closed_A closed_B]
    by (simp only: H_BBK_truth_lemma[OF implication_type env] H_BBK_truth_lemma[OF A env]
          H_BBK_truth_lemma[OF B env] subst.simps)
qed

subsection \<open>Object identity is actual equality of denotations\<close>

text \<open>
  𝔐,g ⊨ M =σ N ⇔ ⟦M⟧g = ⟦N⟧g. Bacon–Dorr, Definition 3.1, pp. 43–44.

  Isabelle representation: The proof identifies equality of tagged classes with
  membership of the corresponding object identity in T.

  Status: Both directions of BBK's identity clause are established; this is the
  Leibnizian specialization of the book's general identity semantics.
\<close>

lemma H_BBK_identity_membership:
  assumes M: "[] \<turnstile> M : \<sigma>" and N: "[] \<turnstile> N : \<sigma>"
  shows "Eq \<sigma> M N \<in> T \<longleftrightarrow> H_BBK_class \<sigma> M = H_BBK_class \<sigma> N"
  using H_BBK_class_eq_iff[OF M N] M N unfolding H_term_eq_def by blast

text \<open>
  The following is the full biconditional
  \<open>val(\<lbrakk>M = N\<rbrakk>g) = 1 \<longleftrightarrow> \<lbrakk>M\<rbrakk>g = \<lbrakk>N\<rbrakk>g\<close>.
  Merely validating reflexivity and Leibniz substitution would not establish
  the right-to-left and left-to-right correspondence with actual equality.
\<close>

lemma H_BBK_truth_Eq:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
    and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_holds (H_BBK_den \<Gamma> \<rho> (Eq \<sigma> M N)) \<longleftrightarrow>
    H_BBK_den \<Gamma> \<rho> M = H_BBK_den \<Gamma> \<rho> N"
proof -
  have identity_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop" by (rule has_type.Eq[OF M N])
  have closed_M: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) M : \<sigma>"
    by (rule H_BBK_closed_instance_type[OF M env])
  have closed_N: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) N : \<sigma>"
    by (rule H_BBK_closed_instance_type[OF N env])
  show ?thesis
    by (simp only: H_BBK_truth_lemma[OF identity_type env] subst.simps
          H_BBK_den_typed_form[OF M] H_BBK_den_typed_form[OF N]
          H_BBK_identity_membership[OF closed_M closed_N])
qed

end
end
