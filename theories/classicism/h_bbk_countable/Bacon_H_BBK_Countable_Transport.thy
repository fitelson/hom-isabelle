theory Bacon_H_BBK_Countable_Transport
  imports Bacon_H_BBK_Countable_Coding
begin

section \<open>Transporting the canonical interpretation to natural-number codes\<close>

text \<open>
  ⟦M⟧nat,g = c(⟦M⟧c⁻¹∘g), and vnat(n) = v(c⁻¹(n)). Bacon–Dorr, Theorem 3.2, pp. 44–45,
  countable-domain refinement.

  Isabelle representation: Environment transport keeps every assignment in the
  corresponding image domain. Every use of a coding inverse retains its domain
  premise.

  Status: Interpretation and truth transport; the next file verifies the complete BBK
  interface.
\<close>

context H_closed_Henkin
begin

definition H_BBK_nat_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> h_bbk_value" where
  "H_BBK_nat_env g = (\<lambda>n. H_BBK_nat_decode (g n))"

definition H_BBK_nat_denote :: "(nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> nat" where
  "H_BBK_nat_denote g M = H_BBK_nat_code (H_BBK_denote (H_BBK_nat_env g) M)"

definition H_BBK_nat_holds :: "nat \<Rightarrow> bool" where
  "H_BBK_nat_holds n = H_BBK_holds (H_BBK_nat_decode n)"

lemma H_BBK_nat_env_typed:
  assumes env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  shows "bbk_env_typed H_BBK_domain \<Gamma> (H_BBK_nat_env g)"
proof (unfold bbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have image: "g n \<in> H_BBK_nat_domain \<sigma>" by (rule bbk_env_lookup[OF env lookup])
  have decoded: "H_BBK_nat_decode (g n) \<in> H_BBK_domain \<sigma>"
    by (rule H_BBK_nat_decode_typed[OF image])
  show "H_BBK_nat_env g n \<in> H_BBK_domain \<sigma>"
    by (simp only: H_BBK_nat_env_def decoded)
qed

lemma H_BBK_nat_env_extend:
  "H_BBK_nat_env (bbk_extend n g) =
    bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g)"
proof (rule ext)
  fix k
  show "H_BBK_nat_env (bbk_extend n g) k =
    bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g) k"
    by (cases k) (simp_all only: H_BBK_nat_env_def bbk_extend_zero bbk_extend_Suc)
qed

lemma H_BBK_nat_env_rename:
  "H_BBK_nat_env (\<lambda>n. g (r n)) = (\<lambda>n. H_BBK_nat_env g (r n))"
  by (rule ext) (simp only: H_BBK_nat_env_def)

lemma H_BBK_nat_canonical_denote_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  shows "H_BBK_denote (H_BBK_nat_env g) M \<in> H_BBK_domain \<sigma>"
  by (rule Canonical.denote_type
    [OF typed bbk_in_universal_signature H_BBK_nat_env_typed[OF env]])

lemma H_BBK_nat_denote_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  shows "H_BBK_nat_denote g M \<in> H_BBK_nat_domain \<sigma>"
  unfolding H_BBK_nat_denote_def
  by (rule H_BBK_nat_domainI[OF H_BBK_nat_canonical_denote_type[OF typed env]])

lemma H_BBK_nat_truth_preservation:
  assumes typed: "\<Gamma> \<turnstile> A : Prop"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
  shows "H_BBK_nat_holds (H_BBK_nat_denote g A) =
    H_BBK_holds (H_BBK_denote (H_BBK_nat_env g) A)"
proof -
  have domain: "H_BBK_denote (H_BBK_nat_env g) A \<in> H_BBK_domain Prop"
    by (rule H_BBK_nat_canonical_denote_type[OF typed env])
  show ?thesis
    by (simp only: H_BBK_nat_holds_def H_BBK_nat_denote_def
        H_BBK_nat_decode_code_domain[OF domain])
qed

lemma H_BBK_nat_denotation_eq_iff:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
    and N: "\<Delta> \<turnstile> N : \<sigma>"
    and g: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
    and h: "bbk_env_typed H_BBK_nat_domain \<Delta> h"
  shows "H_BBK_nat_denote g M = H_BBK_nat_denote h N \<longleftrightarrow>
    H_BBK_denote (H_BBK_nat_env g) M = H_BBK_denote (H_BBK_nat_env h) N"
proof
  assume codes: "H_BBK_nat_denote g M = H_BBK_nat_denote h N"
  have code_eq: "H_BBK_nat_code (H_BBK_denote (H_BBK_nat_env g) M) =
    H_BBK_nat_code (H_BBK_denote (H_BBK_nat_env h) N)"
    using codes by (simp only: H_BBK_nat_denote_def)
  show "H_BBK_denote (H_BBK_nat_env g) M = H_BBK_denote (H_BBK_nat_env h) N"
    by (rule H_BBK_nat_code_cross_type_injective[OF
      H_BBK_nat_canonical_denote_type[OF M g]
      H_BBK_nat_canonical_denote_type[OF N h] code_eq])
next
  assume same: "H_BBK_denote (H_BBK_nat_env g) M = H_BBK_denote (H_BBK_nat_env h) N"
  show "H_BBK_nat_denote g M = H_BBK_nat_denote h N"
    by (simp only: H_BBK_nat_denote_def same)
qed

lemma H_BBK_nat_truth_extended:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and env: "bbk_env_typed H_BBK_nat_domain \<Gamma> g"
    and domain: "n \<in> H_BBK_nat_domain \<sigma>"
  shows "H_BBK_nat_holds (H_BBK_nat_denote (bbk_extend n g) A) =
    H_BBK_holds (H_BBK_denote
      (bbk_extend (H_BBK_nat_decode n) (H_BBK_nat_env g)) A)"
  using H_BBK_nat_truth_preservation[OF body bbk_env_extend[OF env domain]]
  by (simp only: H_BBK_nat_env_extend)

lemma H_BBK_nat_forall_transfer:
  "(\<forall>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)) \<longleftrightarrow>
    (\<forall>v \<in> H_BBK_domain \<sigma>. P v)"
proof
  assume codes: "\<forall>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)"
  show "\<forall>v \<in> H_BBK_domain \<sigma>. P v"
  proof (intro ballI)
    fix v
    assume domain: "v \<in> H_BBK_domain \<sigma>"
    have P: "P (H_BBK_nat_decode (H_BBK_nat_code v))"
      by (rule bspec[OF codes H_BBK_nat_domainI[OF domain]])
    show "P v" using P by (simp only: H_BBK_nat_decode_code_domain[OF domain])
  qed
next
  assume original: "\<forall>v \<in> H_BBK_domain \<sigma>. P v"
  show "\<forall>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)"
  proof (intro ballI)
    fix n
    assume domain: "n \<in> H_BBK_nat_domain \<sigma>"
    show "P (H_BBK_nat_decode n)"
      by (rule bspec[OF original H_BBK_nat_decode_typed[OF domain]])
  qed
qed

lemma H_BBK_nat_exists_transfer:
  "(\<exists>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)) \<longleftrightarrow>
    (\<exists>v \<in> H_BBK_domain \<sigma>. P v)"
proof
  assume codes: "\<exists>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)"
  from codes obtain n where domain: "n \<in> H_BBK_nat_domain \<sigma>"
    and P: "P (H_BBK_nat_decode n)" by (elim bexE)
  show "\<exists>v \<in> H_BBK_domain \<sigma>. P v"
  proof (rule bexI[where x="H_BBK_nat_decode n" and P=P and A="H_BBK_domain \<sigma>"])
    show "P (H_BBK_nat_decode n)" by (rule P)
    show "H_BBK_nat_decode n \<in> H_BBK_domain \<sigma>"
      by (rule H_BBK_nat_decode_typed[OF domain])
  qed
next
  assume original: "\<exists>v \<in> H_BBK_domain \<sigma>. P v"
  from original obtain v where domain: "v \<in> H_BBK_domain \<sigma>" and P: "P v"
    by (elim bexE)
  have coded: "P (H_BBK_nat_decode (H_BBK_nat_code v))"
    by (simp only: H_BBK_nat_decode_code_domain[OF domain] P)
  show "\<exists>n \<in> H_BBK_nat_domain \<sigma>. P (H_BBK_nat_decode n)"
  proof (rule bexI[where x="H_BBK_nat_code v"
      and P="\<lambda>n. P (H_BBK_nat_decode n)" and A="H_BBK_nat_domain \<sigma>"])
    show "P (H_BBK_nat_decode (H_BBK_nat_code v))" by (rule coded)
    show "H_BBK_nat_code v \<in> H_BBK_nat_domain \<sigma>"
      by (rule H_BBK_nat_domainI[OF domain])
  qed
qed

end
end
