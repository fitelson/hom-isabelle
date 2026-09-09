theory Bacon_Applicative_BBK_Bridge
  imports Bacon_BBK_Semantics_Development.Bacon_H_Signature_Proof
    Bacon_Classicism.Bacon_Semantics
begin

section \<open>When an auxiliary applicative interpretation is a BBK model\<close>

text \<open>
  J(M,g) = eval(g,M), V = holds, and Dσ is unchanged.
  The required identity clause is V(J(M =σ N,g)) ⇔ J(M,g) = J(N,g).
  Source: Bacon–Dorr, Definition 3.1, pp. 43–44.

  Isabelle representation: the old applicative_structure supplies evaluation,
  typed application, abstraction and truth representatives.  The bridge
  additionally requires actual identity on typed evaluations.  A sufficient
  condition is eq_den(σ,x,y) ⇔ x = y for x,y ∈ Dσ.

  Status: a conditional preservation bridge for the universal string
  signature, not an equivalence of semantic interfaces.  It does not assert
  that every auxiliary applicative structure meets the identity condition,
  nor that arbitrary BBK models admit this full-function interpretation.
\<close>

lemma applicative_extend_is_bbk:
  "extend_env a g = bbk_extend a g"
proof (rule ext)
  fix n :: nat
  show "extend_env a g n = bbk_extend a g n"
    by (cases n) (simp_all add: bbk_extend_def)
qed

lemma applicative_extended_agreement:
  assumes agree: "\<And>n. Suc n \<in> bbk_fv M \<Longrightarrow> g n = h n"
    and member: "n \<in> bbk_fv M"
  shows "extend_env a g n = extend_env a h n"
proof (cases n)
  case 0
  show ?thesis by (simp only: 0 extend_env.simps)
next
  case (Suc m)
  have eq: "g m = h m" by (rule agree) (simp only: Suc[symmetric] member)
  show ?thesis by (simp only: Suc extend_env.simps eq)
qed

context applicative_structure
begin

lemma applicative_bbk_environment:
  "bbk_env_typed D \<Gamma> g \<longleftrightarrow> env_typed \<Gamma> g"
  by (simp only: bbk_env_typed_def env_typed_def)

lemma applicative_eval_locality:
  assumes agree: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n"
  shows "eval g M = eval h M"
  using agree
proof (induction M arbitrary: g h)
  case (Var n)
  have "g n = h n" by (rule Var.prems) simp
  then show ?case by (simp only: eval.simps)
next
  case (Const c \<sigma>)
  show ?case by (simp only: eval.simps)
next
  case (App M N)
  have left: "eval g M = eval h M" by (rule App.IH(1); rule App.prems) (simp add: bbk_fv.simps)
  have right: "eval g N = eval h N" by (rule App.IH(2); rule App.prems) (simp add: bbk_fv.simps)
  show ?case by (simp only: eval.simps left right)
next
  case (Lam \<sigma> M)
  have eq: "eval (extend_env a g) M = eval (extend_env a h) M" for a
  proof (rule Lam.IH)
    fix n
    assume member: "n \<in> bbk_fv M"
    show "extend_env a g n = extend_env a h n"
      by (rule applicative_extended_agreement[OF _ member]; rule Lam.prems) simp
  qed
  show ?case by (simp only: eval.simps eq)
next
  case (Eq \<sigma> M N)
  have left: "eval g M = eval h M" by (rule Eq.IH(1); rule Eq.prems) (simp add: bbk_fv.simps)
  have right: "eval g N = eval h N" by (rule Eq.IH(2); rule Eq.prems) (simp add: bbk_fv.simps)
  show ?case by (simp only: eval.simps left right)
next
  case (Neg M)
  have eq: "eval g M = eval h M" by (rule Neg.IH; rule Neg.prems) simp
  show ?case by (simp only: eval.simps eq)
next
  case (Conj M N)
  have left: "eval g M = eval h M" by (rule Conj.IH(1); rule Conj.prems) (simp add: bbk_fv.simps)
  have right: "eval g N = eval h N" by (rule Conj.IH(2); rule Conj.prems) (simp add: bbk_fv.simps)
  show ?case by (simp only: eval.simps left right)
next
  case (Disj M N)
  have left: "eval g M = eval h M" by (rule Disj.IH(1); rule Disj.prems) (simp add: bbk_fv.simps)
  have right: "eval g N = eval h N" by (rule Disj.IH(2); rule Disj.prems) (simp add: bbk_fv.simps)
  show ?case by (simp only: eval.simps left right)
next
  case (Imp M N)
  have left: "eval g M = eval h M" by (rule Imp.IH(1); rule Imp.prems) (simp add: bbk_fv.simps)
  have right: "eval g N = eval h N" by (rule Imp.IH(2); rule Imp.prems) (simp add: bbk_fv.simps)
  show ?case by (simp only: eval.simps left right)
next
  case (Forall \<sigma> M)
  have eq: "eval (extend_env a g) M = eval (extend_env a h) M" for a
  proof (rule Forall.IH)
    fix n
    assume member: "n \<in> bbk_fv M"
    show "extend_env a g n = extend_env a h n"
      by (rule applicative_extended_agreement[OF _ member]; rule Forall.prems) simp
  qed
  show ?case by (simp only: eval.simps eq)
next
  case (Exists \<sigma> M)
  have eq: "eval (extend_env a g) M = eval (extend_env a h) M" for a
  proof (rule Exists.IH)
    fix n
    assume member: "n \<in> bbk_fv M"
    show "extend_env a g n = extend_env a h n"
      by (rule applicative_extended_agreement[OF _ member]; rule Exists.prems) simp
  qed
  show ?case by (simp only: eval.simps eq)
qed

lemma applicative_eval_beta_eta:
  assumes conversion: "beta_eta_equiv \<Gamma> \<tau> M N" and env: "env_typed \<Gamma> g"
  shows "eval g M = eval g N"
  using conversion env
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule refl)
next
  case (Beta \<Gamma> M \<tau> N)
  show ?case by (rule beta_compatible_eval[OF Beta.hyps(3,1,2) Beta.prems])
next
  case (Eta \<Gamma> M \<tau> N)
  show ?case by (rule eta_compatible_eval[OF Eta.hyps(3,1,2) Eta.prems])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

theorem applicative_to_BBK:
  assumes actual_identity: "\<And>\<Gamma> M \<sigma> N g. \<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow>
    env_typed \<Gamma> g \<Longrightarrow> holds (eval g (Eq \<sigma> M N)) = (eval g M = eval g N)"
  shows "bbk_model (\<lambda>_. UNIV) D eval holds"
proof (unfold_locales)
  fix \<sigma>
  have member: "const_den [] \<sigma> \<in> D \<sigma>" by (rule const_den_type)
  show "D \<sigma> \<noteq> {}" using member by auto
next
  fix \<Gamma> M \<sigma> g
  assume mt: "\<Gamma> \<turnstile> M : \<sigma>" and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and env: "bbk_env_typed D \<Gamma> g"
  have old_env: "env_typed \<Gamma> g" using env by (simp only: applicative_bbk_environment)
  show "eval g M \<in> D \<sigma>" by (rule eval_type[OF mt old_env])
next
  fix \<Gamma> n \<sigma> g
  assume "lookup \<Gamma> n = Some \<sigma>" and "bbk_env_typed D \<Gamma> g"
  show "eval g (Var n) = g n" by (simp only: eval.simps)
next
  fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
  assume "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and "\<Gamma> \<turnstile> A : \<sigma>"
    and "\<Delta> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>" and "\<Delta> \<turnstile> B : \<sigma>"
    and "bbk_in_signature (\<lambda>_. UNIV) (App F A)" and "bbk_in_signature (\<lambda>_. UNIV) (App G B)"
    and "bbk_env_typed D \<Gamma> g" and "bbk_env_typed D \<Delta> h"
    and fg: "eval g F = eval h G" and ab: "eval g A = eval h B"
  show "eval g (App F A) = eval h (App G B)" by (simp only: eval.simps fg ab)
next
  fix \<Gamma> M \<sigma> \<Delta> g h
  assume "\<Gamma> \<turnstile> M : \<sigma>" and "\<Delta> \<turnstile> M : \<sigma>" and "bbk_in_signature (\<lambda>_. UNIV) M"
    and "bbk_env_typed D \<Gamma> g" and "bbk_env_typed D \<Delta> h"
    and agree: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n"
  show "eval g M = eval h M" by (rule applicative_eval_locality[OF agree])
next
  fix \<Gamma> M \<sigma> r \<Delta> g
  assume "\<Gamma> \<turnstile> M : \<sigma>" and "bbk_in_signature (\<lambda>_. UNIV) M" and "inj r"
    and "bbk_env_typed D \<Delta> g"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  show "eval g (rename r M) = eval (\<lambda>n. g (r n)) M" by (rule eval_rename)
next
  fix \<Gamma> \<sigma> M N g
  assume conv: "beta_eta_equiv \<Gamma> \<sigma> M N"
    and "bbk_in_signature (\<lambda>_. UNIV) M" and "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed D \<Gamma> g"
  have old_env: "env_typed \<Gamma> g" using env by (simp only: applicative_bbk_environment)
  show "eval g M = eval g N" by (rule applicative_eval_beta_eta[OF conv old_env])
next
  fix \<Gamma> A g
  assume "\<Gamma> \<turnstile> A : Prop" and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Neg A)) = (\<not> holds (eval g A))"
    by (simp only: eval.simps truth_den_holds)
next
  fix \<Gamma> A B g
  assume "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_in_signature (\<lambda>_. UNIV) B" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Conj A B)) = (holds (eval g A) \<and> holds (eval g B))"
    by (simp only: eval.simps truth_den_holds)
next
  fix \<Gamma> A B g
  assume "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_in_signature (\<lambda>_. UNIV) B" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Disj A B)) = (holds (eval g A) \<or> holds (eval g B))"
    by (simp only: eval.simps truth_den_holds)
next
  fix \<Gamma> A B g
  assume "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_in_signature (\<lambda>_. UNIV) B" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Imp A B)) = (holds (eval g A) \<longrightarrow> holds (eval g B))"
    by (simp only: eval.simps truth_den_holds)
next
  fix \<sigma> \<Gamma> A g
  assume "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Forall \<sigma> A)) = (\<forall>a \<in> D \<sigma>. holds (eval (bbk_extend a g) A))"
    by (simp only: eval.simps truth_den_holds applicative_extend_is_bbk)
next
  fix \<sigma> \<Gamma> A g
  assume "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "bbk_in_signature (\<lambda>_. UNIV) A" and "bbk_env_typed D \<Gamma> g"
  show "holds (eval g (Exists \<sigma> A)) = (\<exists>a \<in> D \<sigma>. holds (eval (bbk_extend a g) A))"
    by (simp only: eval.simps truth_den_holds applicative_extend_is_bbk)
next
  fix \<Gamma> M \<sigma> N g
  assume mt: "\<Gamma> \<turnstile> M : \<sigma>" and nt: "\<Gamma> \<turnstile> N : \<sigma>"
    and "bbk_in_signature (\<lambda>_. UNIV) M" and "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed D \<Gamma> g"
  have old_env: "env_typed \<Gamma> g" using env by (simp only: applicative_bbk_environment)
  show "holds (eval g (Eq \<sigma> M N)) = (eval g M = eval g N)"
    by (rule actual_identity[OF mt nt old_env])
qed

corollary applicative_to_BBK_from_eq_den:
  assumes faithful: "\<And>\<sigma> x y. x \<in> D \<sigma> \<Longrightarrow> y \<in> D \<sigma> \<Longrightarrow>
    eq_den \<sigma> x y \<longleftrightarrow> x = y"
  shows "bbk_model (\<lambda>_. UNIV) D eval holds"
proof (rule applicative_to_BBK)
  fix \<Gamma> M \<sigma> N g
  assume mt: "\<Gamma> \<turnstile> M : \<sigma>" and nt: "\<Gamma> \<turnstile> N : \<sigma>" and env: "env_typed \<Gamma> g"
  have m: "eval g M \<in> D \<sigma>" by (rule eval_type[OF mt env])
  have n: "eval g N \<in> D \<sigma>" by (rule eval_type[OF nt env])
  show "holds (eval g (Eq \<sigma> M N)) = (eval g M = eval g N)"
    by (simp only: eval.simps truth_den_holds faithful[OF m n])
qed

end

end
