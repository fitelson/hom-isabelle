theory Bacon_H_BBK_Countable_Model
  imports Bacon_H_BBK_Countable_Transport
begin

section \<open>The transported natural-number domains form an exact BBK model\<close>

text \<open>
  𝔐nat = (c[D], c ∘ ⟦·⟧ ∘ c⁻¹, v ∘ c⁻¹) is a BBK model. Bacon–Dorr, Theorem 3.2, pp.
  44–45, countable-domain refinement.

  Isabelle representation: The sublocale transports each field separately; identity
  uses injectivity and quantifiers use the typed image-domain bijections.

  Status: A BBK model with domains contained in ℕ, not a substitution of full-function
  or Fregean semantics.
\<close>

context H_closed_Henkin
begin

sublocale NatCanonical: bbk_model "\<lambda>_. UNIV"
    H_BBK_nat_domain H_BBK_nat_denote H_BBK_nat_holds
proof (unfold_locales)
  show "H_BBK_nat_domain \<sigma> \<noteq> {}" for \<sigma> by (rule H_BBK_nat_domain_nonempty)
next
  fix \<Gamma> M \<sigma> g
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  show "H_BBK_nat_denote g M \<in> H_BBK_nat_domain \<sigma>"
    by (rule H_BBK_nat_denote_type[OF typed env])
next
  fix \<Gamma> n \<sigma> g
  assume lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have original: "H_BBK_denote (H_BBK_nat_env g) (Var n) = H_BBK_nat_env g n"
    by (rule Canonical.denote_var[OF lookup H_BBK_nat_env_typed[OF env]])
  have image: "g n \<in> H_BBK_nat_domain \<sigma>"
    by (rule bbk_env_lookup[OF env lookup])
  have inverse_at_n: "H_BBK_nat_code (H_BBK_nat_decode (g n)) = g n"
    by (rule H_BBK_nat_code_decode[OF image])
  have original_decoded:
    "H_BBK_denote (H_BBK_nat_env g) (Var n) = H_BBK_nat_decode (g n)"
    using original by (simp only: H_BBK_nat_env_def)
  have "H_BBK_nat_denote g (Var n) =
    H_BBK_nat_code (H_BBK_denote (H_BBK_nat_env g) (Var n))"
    by (simp only: H_BBK_nat_denote_def)
  also have "... = H_BBK_nat_code (H_BBK_nat_decode (g n))"
    by (simp only: original_decoded)
  also have "... = g n" by (rule inverse_at_n)
  finally show "H_BBK_nat_denote g (Var n) = g n" .
next
  fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
  assume F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and A: "\<Gamma> \<turnstile> A : \<sigma>"
    and G: "\<Delta> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>" and B: "\<Delta> \<turnstile> B : \<sigma>"
    and sigF: "bbk_in_signature (\<lambda>_. UNIV) (App F A)"
    and sigG: "bbk_in_signature (\<lambda>_. UNIV) (App G B)"
    and envg: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
    and envh: "bbk_env_typed H_BBK_nat_domain \<Delta> h"
    and eqF: "H_BBK_nat_denote g F = H_BBK_nat_denote h G"
    and eqA: "H_BBK_nat_denote g A = H_BBK_nat_denote h B"
  have original_F: "H_BBK_denote (H_BBK_nat_env g) F = H_BBK_denote (H_BBK_nat_env h) G"
    by (rule iffD1[OF H_BBK_nat_denotation_eq_iff[OF F G envg envh] eqF])
  have original_A: "H_BBK_denote (H_BBK_nat_env g) A = H_BBK_denote (H_BBK_nat_env h) B"
    by (rule iffD1[OF H_BBK_nat_denotation_eq_iff[OF A B envg envh] eqA])
  have application: "H_BBK_denote (H_BBK_nat_env g) (App F A) =
    H_BBK_denote (H_BBK_nat_env h) (App G B)"
    by (rule Canonical.denote_application_cong[OF F A G B sigF sigG
      H_BBK_nat_env_typed[OF envg] H_BBK_nat_env_typed[OF envh] original_F original_A])
  show "H_BBK_nat_denote g (App F A) = H_BBK_nat_denote h (App G B)"
    by (simp only: H_BBK_nat_denote_def application)
next
  fix \<Gamma> M \<sigma> \<Delta> g h
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and typed': "\<Delta> \<turnstile> M : \<sigma>"
    and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and envg: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
    and envh: "bbk_env_typed H_BBK_nat_domain \<Delta> h"
    and same: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n"
  have decoded: "\<And>n. n \<in> bbk_fv M \<Longrightarrow> H_BBK_nat_env g n = H_BBK_nat_env h n"
    by (simp only: H_BBK_nat_env_def same)
  have original: "H_BBK_denote (H_BBK_nat_env g) M = H_BBK_denote (H_BBK_nat_env h) M"
    by (rule H_BBK_denote_locality[OF decoded])
  show "H_BBK_nat_denote g M = H_BBK_nat_denote h M"
    by (simp only: H_BBK_nat_denote_def original)
next
  fix \<Gamma> M \<sigma> r \<Delta> g
  assume typed: "\<Gamma> \<turnstile> M : \<sigma>" and sig: "bbk_in_signature (\<lambda>_. UNIV) M"
    and injective: "inj r" and env: "bbk_env_typed H_BBK_nat_domain \<Delta> g"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  show "H_BBK_nat_denote g (rename r M) = H_BBK_nat_denote (\<lambda>n. g (r n)) M"
    by (simp only: H_BBK_nat_denote_def H_BBK_denote_rename H_BBK_nat_env_rename)
next
  fix \<Gamma> \<sigma> M N g
  assume conv: "beta_eta_equiv \<Gamma> \<sigma> M N"
    and sigM: "bbk_in_signature (\<lambda>_. UNIV) M" and sigN: "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have original: "H_BBK_denote (H_BBK_nat_env g) M = H_BBK_denote (H_BBK_nat_env g) N"
    by (rule Canonical.denote_beta_eta[OF conv sigM sigN H_BBK_nat_env_typed[OF env]])
  show "H_BBK_nat_denote g M = H_BBK_nat_denote g N"
    by (simp only: H_BBK_nat_denote_def original)
next
  fix \<Gamma> A g
  assume A: "\<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_neg: "\<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Neg A)) =
    (\<not> H_BBK_nat_holds (H_BBK_nat_denote g A))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_neg env]
      H_BBK_nat_truth_preservation[OF A env]
      Canonical.valuation_neg[OF A sig H_BBK_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_conj: "\<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Conj A B)) =
    (H_BBK_nat_holds (H_BBK_nat_denote g A) \<and> H_BBK_nat_holds (H_BBK_nat_denote g B))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_conj env]
      H_BBK_nat_truth_preservation[OF A env] H_BBK_nat_truth_preservation[OF B env]
      Canonical.valuation_conj[OF A B sigA sigB H_BBK_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_disj: "\<Gamma> \<turnstile> Disj A B : Prop" by (rule has_type.Disj[OF A B])
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Disj A B)) =
    (H_BBK_nat_holds (H_BBK_nat_denote g A) \<or> H_BBK_nat_holds (H_BBK_nat_denote g B))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_disj env]
      H_BBK_nat_truth_preservation[OF A env] H_BBK_nat_truth_preservation[OF B env]
      Canonical.valuation_disj[OF A B sigA sigB H_BBK_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_imp: "\<Gamma> \<turnstile> Imp A B : Prop" by (rule has_type.Imp[OF A B])
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Imp A B)) =
    (H_BBK_nat_holds (H_BBK_nat_denote g A) \<longrightarrow> H_BBK_nat_holds (H_BBK_nat_denote g B))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_imp env]
      H_BBK_nat_truth_preservation[OF A env] H_BBK_nat_truth_preservation[OF B env]
      Canonical.valuation_imp[OF A B sigA sigB H_BBK_nat_env_typed[OF env]])
next
  fix \<sigma> \<Gamma> A g
  assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_all: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop" by (rule has_type.Forall[OF body])
  have transfer:
    "(\<forall>n \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)) =
     (\<forall>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A))"
  proof
    assume coded_all:
      "\<forall>n \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
    show "\<forall>v \<in> H_BBK_domain \<sigma>.
      H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
    proof (intro ballI)
      fix v
      assume domain: "v \<in> H_BBK_domain \<sigma>"
      have code_domain: "H_BBK_nat_code v \<in> H_BBK_nat_domain \<sigma>"
        by (rule H_BBK_nat_domainI[OF domain])
      have coded_truth:
        "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend (H_BBK_nat_code v) g) A)"
        by (rule bspec[OF coded_all code_domain])
      have decoded_truth: "H_BBK_holds (H_BBK_denote
        (bbk_extend (H_BBK_nat_decode (H_BBK_nat_code v)) (H_BBK_nat_env g)) A)"
        by (rule iffD1[OF H_BBK_nat_truth_extended[OF body env code_domain] coded_truth])
      show "H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
        using decoded_truth by (simp only: H_BBK_nat_decode_code_domain[OF domain])
    qed
  next
    assume original_all:
      "\<forall>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
    show "\<forall>n \<in> H_BBK_nat_domain \<sigma>.
      H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
    proof (intro ballI)
      fix n
      assume domain: "n \<in> H_BBK_nat_domain \<sigma>"
      have decoded_domain: "H_BBK_nat_decode n \<in> H_BBK_domain \<sigma>"
        by (rule H_BBK_nat_decode_typed[OF domain])
      have decoded_truth: "H_BBK_holds (H_BBK_denote
        (bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g)) A)"
        by (rule bspec[OF original_all decoded_domain])
      show "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
        by (rule iffD2[OF H_BBK_nat_truth_extended[OF body env domain] decoded_truth])
    qed
  qed
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Forall \<sigma> A)) =
    (\<forall>a \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend a g) A))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_all env] transfer
      Canonical.valuation_forall[OF body sig H_BBK_nat_env_typed[OF env]])
next
  fix \<sigma> \<Gamma> A g
  assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and sig: "bbk_in_signature (\<lambda>_. UNIV) A"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_ex: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop" by (rule has_type.Exists[OF body])
  have transfer:
    "(\<exists>n \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)) =
     (\<exists>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A))"
  proof
    assume coded_exists:
      "\<exists>n \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
    from coded_exists obtain n where domain: "n \<in> H_BBK_nat_domain \<sigma>"
      and coded_truth: "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
      by (elim bexE)
    have decoded_domain: "H_BBK_nat_decode n \<in> H_BBK_domain \<sigma>"
      by (rule H_BBK_nat_decode_typed[OF domain])
    have decoded_truth: "H_BBK_holds (H_BBK_denote
      (bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g)) A)"
      by (rule iffD1[OF H_BBK_nat_truth_extended[OF body env domain] coded_truth])
    show "\<exists>v \<in> H_BBK_domain \<sigma>.
      H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
    proof (rule bexI[where x="H_BBK_nat_decode n" and A="H_BBK_domain \<sigma>"
        and P="\<lambda>v. H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"])
      show "H_BBK_holds (H_BBK_denote
        (bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g)) A)" by (rule decoded_truth)
      show "H_BBK_nat_decode n \<in> H_BBK_domain \<sigma>" by (rule decoded_domain)
    qed
  next
    assume original_exists:
      "\<exists>v \<in> H_BBK_domain \<sigma>. H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
    from original_exists obtain v where domain: "v \<in> H_BBK_domain \<sigma>"
      and original_truth: "H_BBK_holds (H_BBK_denote (bbk_extend v (H_BBK_nat_env g)) A)"
      by (elim bexE)
    have code_domain: "H_BBK_nat_code v \<in> H_BBK_nat_domain \<sigma>"
      by (rule H_BBK_nat_domainI[OF domain])
    have decoded_truth: "H_BBK_holds (H_BBK_denote
      (bbk_extend (H_BBK_nat_decode (H_BBK_nat_code v)) (H_BBK_nat_env g)) A)"
      using original_truth by (simp only: H_BBK_nat_decode_code_domain[OF domain])
    have coded_truth:
      "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend (H_BBK_nat_code v) g) A)"
      by (rule iffD2[OF H_BBK_nat_truth_extended[OF body env code_domain] decoded_truth])
    show "\<exists>n \<in> H_BBK_nat_domain \<sigma>.
      H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"
    proof (rule bexI[where x="H_BBK_nat_code v" and A="H_BBK_nat_domain \<sigma>"
        and P="\<lambda>n. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A)"])
      show "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend (H_BBK_nat_code v) g) A)"
        by (rule coded_truth)
      show "H_BBK_nat_code v \<in> H_BBK_nat_domain \<sigma>" by (rule code_domain)
    qed
  qed
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Exists \<sigma> A)) =
    (\<exists>a \<in> H_BBK_nat_domain \<sigma>. H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend a g) A))"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_ex env] transfer
      Canonical.valuation_exists[OF body sig H_BBK_nat_env_typed[OF env]])
next
  fix \<Gamma> M \<sigma> N g
  assume M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
    and sigM: "bbk_in_signature (\<lambda>_. UNIV) M" and sigN: "bbk_in_signature (\<lambda>_. UNIV) N"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  have typed_eq: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop" by (rule has_type.Eq[OF M N])
  show "H_BBK_nat_holds (H_BBK_nat_denote g (Eq \<sigma> M N)) =
    (H_BBK_nat_denote g M = H_BBK_nat_denote g N)"
    by (simp only: H_BBK_nat_truth_preservation[OF typed_eq env]
      Canonical.valuation_identity[OF M N sigM sigN H_BBK_nat_env_typed[OF env]]
      H_BBK_nat_denotation_eq_iff[OF M N env env])
qed

theorem H_BBK_nat_model:
  "bbk_model (\<lambda>_. UNIV) H_BBK_nat_domain H_BBK_nat_denote H_BBK_nat_holds"
  by (rule NatCanonical.bbk_model_axioms)

lemma H_BBK_nat_closed_truth_lemma:
  assumes typed: "[] \<turnstile> A : Prop"
  shows "H_BBK_nat_holds (H_BBK_nat_denote g A) \<longleftrightarrow> A \<in> T"
  by (simp only: H_BBK_nat_truth_preservation[OF typed bbk_env_empty]
      H_BBK_closed_truth_lemma[OF typed])

end
end
