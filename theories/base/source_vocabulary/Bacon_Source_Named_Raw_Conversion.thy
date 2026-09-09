theory Bacon_Source_Named_Raw_Conversion
  imports Bacon_Source_Named_Conversion
begin

section \<open>Typed βη conversion without a nonlogical-signature restriction\<close>

text \<open>
  Raw conversion here means that intermediate terms may use constants
  outside the endpoint signature. Every term still has its fixed G-type:
  this is not conversion through ill-typed expressions. Taking the universal
  signature supplies exactly that existing typed conversion relation.

  Source role: an explicit reading of βη-equivalence in Bacon–Dorr
  Definition 3.1(ii.d). Endpoint membership in ℒ(Σ) is imposed by the
  named-model clause separately. Its reduction to a chain staying inside
  Σ must be proved using the rich variable stock, not assumed from the
  definition of raw conversion.
\<close>

abbreviation named_raw_beta_eta ::
  "('l \<Rightarrow> otype) \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow>
    ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "named_raw_beta_eta L G \<tau> A B \<equiv>
    named_beta_eta_in_language L (\<lambda>_. UNIV) G \<tau> A B"

lemma named_universal_signature:
  "named_in_signature (\<lambda>_. UNIV) A"
  by (induction A) simp_all

lemma named_universal_language:
  "named_in_language L (\<lambda>_. UNIV) G A \<tau> \<longleftrightarrow> has_ntype L G A \<tau>"
  by (simp add: named_in_language_def named_universal_signature)

lemma named_language_into_universal:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_in_language L (\<lambda>_. UNIV) G A \<tau>"
  using language unfolding named_in_language_def by (simp add: named_universal_signature)

theorem named_conversion_to_raw:
  assumes conversion: "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
  shows "named_raw_beta_eta L G \<tau> A B"
  using conversion
proof (induction rule: named_beta_eta_in_language.induct)
  case Refl
  show ?case by (rule named_beta_eta_in_language.Refl[OF named_language_into_universal[OF Refl.hyps]])
next
  case Beta
  show ?case by (rule named_beta_eta_in_language.Beta[OF named_language_into_universal[OF Beta.hyps(1)]
    named_language_into_universal[OF Beta.hyps(2)] Beta.hyps(3)])
next
  case Eta
  show ?case by (rule named_beta_eta_in_language.Eta[OF named_language_into_universal[OF Eta.hyps(1)]
    named_language_into_universal[OF Eta.hyps(2)] Eta.hyps(3)])
next
  case Sym
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule named_beta_eta_in_language.Trans[OF Trans.IH])
qed

end
