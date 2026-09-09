theory Bacon_H_BBK_Canonical_Model
  imports Bacon_H_BBK_Canonical_Quantifiers
    Bacon_BBK_Semantics_Development.Bacon_BBK_H_Soundness_Quantifiers
begin

section \<open>The canonical identity classes form a BBK model\<close>

text \<open>
  𝔐ₜ = (Dₜ, ⟦·⟧ₜ, vₜ), with ⟦M⟧g = [M[rep ∘ g]]ₜ. Bacon–Dorr, Definition 3.1, pp.
  43–44. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Free-variable locality and de Bruijn renaming coherence
  follow from syntactic substitution. The Canonical sublocale assembles all domain and
  truth lemmas into bbk_model.

  Status: An actual represented BBK model over F and universal typed-string names;
  source-syntax and arbitrary-cardinality extensions are not proved here.
\<close>

lemma H_BBK_lift_free_agreement:
  assumes agree: "\<And>n. Suc n \<in> bbk_fv M \<Longrightarrow> s n = r n"
    and member: "n \<in> bbk_fv M"
  shows "lift_subst s n = lift_subst r n"
proof (cases n)
  case 0
  show ?thesis by (simp add: 0)
next
  case (Suc m)
  have in_body: "Suc m \<in> bbk_fv M" using member by (simp only: Suc)
  have eq: "s m = r m" by (rule agree[OF in_body])
  show ?thesis by (simp only: Suc lift_subst.simps eq)
qed

lemma H_BBK_subst_free_agreement:
  assumes agree: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> s n = r n"
  shows "subst s M = subst r M"
  using agree
proof (induction M arbitrary: s r)
  case (Var n)
  have eq: "s n = r n" by (rule Var.prems) simp
  show ?case by (simp only: subst.simps eq)
next
  case (Const c \<sigma>)
  show ?case by (simp only: subst.simps)
next
  case (App M N)
  have left: "subst s M = subst r M"
    by (rule App.IH(1)[where s=s and r=r]) (rule App.prems, simp)
  have right: "subst s N = subst r N"
    by (rule App.IH(2)[where s=s and r=r]) (rule App.prems, simp)
  show ?case by (simp only: subst.simps left right)
next
  case (Lam \<sigma> M)
  have tail: "\<And>n. Suc n \<in> bbk_fv M \<Longrightarrow> s n = r n"
    using Lam.prems by (simp only: bbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> lift_subst s n = lift_subst r n"
    by (rule H_BBK_lift_free_agreement[OF tail])
  have body: "subst (lift_subst s) M = subst (lift_subst r) M"
    by (rule Lam.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  show ?case by (simp only: subst.simps body)
next
  case (Eq \<sigma> M N)
  have left: "subst s M = subst r M"
    by (rule Eq.IH(1)[where s=s and r=r]) (rule Eq.prems, simp)
  have right: "subst s N = subst r N"
    by (rule Eq.IH(2)[where s=s and r=r]) (rule Eq.prems, simp)
  show ?case by (simp only: subst.simps left right)
next
  case (Neg M)
  have body: "subst s M = subst r M"
    by (rule Neg.IH[where s=s and r=r]) (rule Neg.prems, simp)
  show ?case by (simp only: subst.simps body)
next
  case (Conj M N)
  have left: "subst s M = subst r M"
    by (rule Conj.IH(1)[where s=s and r=r]) (rule Conj.prems, simp)
  have right: "subst s N = subst r N"
    by (rule Conj.IH(2)[where s=s and r=r]) (rule Conj.prems, simp)
  show ?case by (simp only: subst.simps left right)
next
  case (Disj M N)
  have left: "subst s M = subst r M"
    by (rule Disj.IH(1)[where s=s and r=r]) (rule Disj.prems, simp)
  have right: "subst s N = subst r N"
    by (rule Disj.IH(2)[where s=s and r=r]) (rule Disj.prems, simp)
  show ?case by (simp only: subst.simps left right)
next
  case (Imp M N)
  have left: "subst s M = subst r M"
    by (rule Imp.IH(1)[where s=s and r=r]) (rule Imp.prems, simp)
  have right: "subst s N = subst r N"
    by (rule Imp.IH(2)[where s=s and r=r]) (rule Imp.prems, simp)
  show ?case by (simp only: subst.simps left right)
next
  case (Forall \<sigma> M)
  have tail: "\<And>n. Suc n \<in> bbk_fv M \<Longrightarrow> s n = r n"
    using Forall.prems by (simp only: bbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> lift_subst s n = lift_subst r n"
    by (rule H_BBK_lift_free_agreement[OF tail])
  have body: "subst (lift_subst s) M = subst (lift_subst r) M"
    by (rule Forall.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  show ?case by (simp only: subst.simps body)
next
  case (Exists \<sigma> M)
  have tail: "\<And>n. Suc n \<in> bbk_fv M \<Longrightarrow> s n = r n"
    using Exists.prems by (simp only: bbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> lift_subst s n = lift_subst r n"
    by (rule H_BBK_lift_free_agreement[OF tail])
  have body: "subst (lift_subst s) M = subst (lift_subst r) M"
    by (rule Exists.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  show ?case by (simp only: subst.simps body)
qed

context H_closed_Henkin
begin

lemma H_BBK_env_interface:
  "bbk_env_typed H_BBK_domain \<Gamma> g \<longleftrightarrow> H_BBK_env_typed \<Gamma> g"
  by (simp only: bbk_env_typed_def H_BBK_env_typed_def)

lemma H_BBK_denote_locality:
  assumes same: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n"
  shows "H_BBK_denote g M = H_BBK_denote h M"
proof -
  have representatives: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> H_BBK_rep (g n) = H_BBK_rep (h n)"
    by (simp only: same)
  have closed_terms: "subst (\<lambda>n. H_BBK_rep (g n)) M = subst (\<lambda>n. H_BBK_rep (h n)) M"
    by (rule H_BBK_subst_free_agreement[where M=M and s="\<lambda>n. H_BBK_rep (g n)"
          and r="\<lambda>n. H_BBK_rep (h n)", OF representatives])
  show ?thesis by (simp only: H_BBK_denote_def closed_terms)
qed

lemma H_BBK_denote_rename:
  "H_BBK_denote g (rename r M) = H_BBK_denote (\<lambda>n. g (r n)) M"
  by (simp add: H_BBK_denote_def subst_rename comp_def)

lemma H_BBK_denote_application:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and A: "\<Gamma> \<turnstile> A : \<sigma>"
    and env: "H_BBK_env_typed \<Gamma> g"
  shows "H_BBK_denote g (App F A) = H_BBK_app \<sigma> \<tau> (H_BBK_denote g F) (H_BBK_denote g A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App F A : \<tau>" by (rule has_type.App[OF F A])
  show ?thesis
    by (simp only: H_BBK_denote_eq_den[OF app_type env] H_BBK_denote_eq_den[OF F env]
          H_BBK_denote_eq_den[OF A env] H_BBK_den_App[OF F A env])
qed

lemma H_BBK_denote_truth_Forall:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> g"
  shows "H_BBK_holds (H_BBK_denote g (Forall \<sigma> A)) =
    (\<forall>a \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend a g) A))"
proof -
  have quantified: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop" by (rule has_type.Forall[OF body])
  have at_value: "H_BBK_denote (case_nat a g) A = H_BBK_den (\<sigma> # \<Gamma>) (case_nat a g) A"
    if domain: "a \<in> H_BBK_domain \<sigma>" for a
    by (rule H_BBK_denote_eq_den[OF body H_BBK_env_extend[OF env domain]])
  show ?thesis
    by (simp add: H_BBK_denote_eq_den[OF quantified env] bbk_extend_def at_value
          H_BBK_truth_Forall[OF body env])
qed

lemma H_BBK_denote_truth_Exists:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and env: "H_BBK_env_typed \<Gamma> g"
  shows "H_BBK_holds (H_BBK_denote g (Exists \<sigma> A)) =
    (\<exists>a \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend a g) A))"
proof -
  have quantified: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop" by (rule has_type.Exists[OF body])
  have at_value: "H_BBK_denote (case_nat a g) A = H_BBK_den (\<sigma> # \<Gamma>) (case_nat a g) A"
    if domain: "a \<in> H_BBK_domain \<sigma>" for a
    by (rule H_BBK_denote_eq_den[OF body H_BBK_env_extend[OF env domain]])
  show ?thesis
    by (simp add: H_BBK_denote_eq_den[OF quantified env] bbk_extend_def at_value
          H_BBK_truth_Exists[OF body env])
qed

subsection \<open>Discharging every field of the model interface\<close>

text \<open>
  𝔐ₜ satisfies BBK(i), BBK(ii.a–d), and BBK(iii.a–f). Bacon–Dorr, Definition 3.1, pp.
  43–44.

  Isabelle representation: The sublocale proof supplies nonemptiness, typed
  evaluation, locality, representation coherence, conversion, and all logical truth
  conditions individually.

  Status: Every displayed field is discharged; no countermodel-existence assumption
  substitutes for this construction.
\<close>

sublocale Canonical: bbk_model "\<lambda>_. UNIV" H_BBK_domain H_BBK_denote H_BBK_holds
proof (unfold_locales)
  show "H_BBK_domain \<sigma> \<noteq> {}" for \<sigma> by (rule H_BBK_domain_nonempty)
next
  fix \<Gamma> M \<sigma> g
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  show "H_BBK_denote g M \<in> H_BBK_domain \<sigma>"
    using H_BBK_den_type[OF typed ce] by (simp only: H_BBK_denote_eq_den[OF typed ce])
next
  fix \<Gamma> n \<sigma> g
  assume lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have typed: "\<Gamma> \<turnstile> Var n : \<sigma>" by (rule has_type.Var[OF lookup])
  show "H_BBK_denote g (Var n) = g n"
    by (simp only: H_BBK_denote_eq_den[OF typed ce] H_BBK_den_Var[OF lookup ce])
next
  fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
  assume F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and A: "\<Gamma> \<turnstile> A : \<sigma>"
    and G: "\<Delta> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>" and B: "\<Delta> \<turnstile> B : \<sigma>"
    and sigF: "bbk_in_signature (\<lambda>_. UNIV) (App F A)"
    and sigG: "bbk_in_signature (\<lambda>_. UNIV) (App G B)"
    and envg: "bbk_env_typed H_BBK_domain \<Gamma> g" and envh: "bbk_env_typed H_BBK_domain \<Delta> h"
    and eqF: "H_BBK_denote g F = H_BBK_denote h G" and eqA: "H_BBK_denote g A = H_BBK_denote h B"
  have cg: "H_BBK_env_typed \<Gamma> g" and ch: "H_BBK_env_typed \<Delta> h"
    using envg envh by (simp_all only: H_BBK_env_interface)
  show "H_BBK_denote g (App F A) = H_BBK_denote h (App G B)"
    by (simp only: H_BBK_denote_application[OF F A cg] H_BBK_denote_application[OF G B ch] eqF eqA)
next
  fix \<Gamma> M \<sigma> \<Delta> g h
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and typed': "\<Delta> \<turnstile> M : \<sigma>"
    and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and envg: "bbk_env_typed H_BBK_domain \<Gamma> g" and envh: "bbk_env_typed H_BBK_domain \<Delta> h"
    and same: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n"
  show "H_BBK_denote g M = H_BBK_denote h M" by (rule H_BBK_denote_locality[OF same])
next
  fix \<Gamma> M \<sigma> r \<Delta> g
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and injective: "inj r" and env: "bbk_env_typed H_BBK_domain \<Delta> g"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  show "H_BBK_denote g (rename r M) = H_BBK_denote (\<lambda>n. g (r n)) M"
    by (rule H_BBK_denote_rename)
next
  fix \<Gamma> \<sigma> M N g
  assume conv: "beta_eta_equiv \<Gamma> \<sigma> M N"
    and sigM: "bbk_in_signature (\<lambda>_. UNIV) M" and sigN: "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  show "H_BBK_denote g M = H_BBK_denote g N" by (rule H_BBK_denote_beta_eta[OF conv ce])
next
  fix \<Gamma> A g
  assume A: "\<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have neg: "\<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  show "H_BBK_holds (H_BBK_denote g (Neg A)) = (\<not> H_BBK_holds (H_BBK_denote g A))"
    by (simp only: H_BBK_denote_eq_den[OF neg ce] H_BBK_denote_eq_den[OF A ce] H_BBK_truth_Neg[OF A ce])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have conj: "\<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  show "H_BBK_holds (H_BBK_denote g (Conj A B)) =
      (H_BBK_holds (H_BBK_denote g A) \<and> H_BBK_holds (H_BBK_denote g B))"
    by (simp only: H_BBK_denote_eq_den[OF conj ce] H_BBK_denote_eq_den[OF A ce]
          H_BBK_denote_eq_den[OF B ce] H_BBK_truth_Conj[OF A B ce])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have disj: "\<Gamma> \<turnstile> Disj A B : Prop" by (rule has_type.Disj[OF A B])
  show "H_BBK_holds (H_BBK_denote g (Disj A B)) =
      (H_BBK_holds (H_BBK_denote g A) \<or> H_BBK_holds (H_BBK_denote g B))"
    by (simp only: H_BBK_denote_eq_den[OF disj ce] H_BBK_denote_eq_den[OF A ce]
          H_BBK_denote_eq_den[OF B ce] H_BBK_truth_Disj[OF A B ce])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have imp: "\<Gamma> \<turnstile> Imp A B : Prop" by (rule has_type.Imp[OF A B])
  show "H_BBK_holds (H_BBK_denote g (Imp A B)) =
      (H_BBK_holds (H_BBK_denote g A) \<longrightarrow> H_BBK_holds (H_BBK_denote g B))"
    by (simp only: H_BBK_denote_eq_den[OF imp ce] H_BBK_denote_eq_den[OF A ce]
          H_BBK_denote_eq_den[OF B ce] H_BBK_truth_Imp[OF A B ce])
next
  fix \<sigma> \<Gamma> A g
  assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  show "H_BBK_holds (H_BBK_denote g (Forall \<sigma> A)) =
      (\<forall>a \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend a g) A))"
    by (rule H_BBK_denote_truth_Forall[OF body ce])
next
  fix \<sigma> \<Gamma> A g
  assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  show "H_BBK_holds (H_BBK_denote g (Exists \<sigma> A)) =
      (\<exists>a \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend a g) A))"
    by (rule H_BBK_denote_truth_Exists[OF body ce])
next
  fix \<Gamma> M \<sigma> N g
  assume M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
    and sigM: "bbk_in_signature (\<lambda>_. UNIV) M" and sigN: "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed H_BBK_domain \<Gamma> g"
  have ce: "H_BBK_env_typed \<Gamma> g" using env by (simp only: H_BBK_env_interface)
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop" by (rule has_type.Eq[OF M N])
  show "H_BBK_holds (H_BBK_denote g (Eq \<sigma> M N)) = (H_BBK_denote g M = H_BBK_denote g N)"
    by (simp only: H_BBK_denote_eq_den[OF eq_type ce] H_BBK_denote_eq_den[OF M ce]
          H_BBK_denote_eq_den[OF N ce] H_BBK_truth_Eq[OF M N ce])
qed

end
end
