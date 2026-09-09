theory Bacon_Parametric_Canonical_Model
  imports Bacon_Parametric_Canonical_Quantifiers Bacon_Parametric_Canonical_Model_Support
begin

section \<open>A Henkin theory determines a BBK model\<close>

text \<open>
  Given a closed maximal consistent Henkin theory T in ℒ(Σ), let Dσ
  contain the tagged classes [M]ₜ, let ⟦A⟧g be the class obtained by
  substituting representatives, and let val([P]ₜ) = 1 iff P ∈ T.
  These data satisfy all clauses of the language-relative BBK definition.
  Source: Bacon–Dorr Definition 3.1, pp.43–44, and p.45 n.64;
  Bacon, Theorem 15.3, pp.320–321.

  The declaration below is conditional on pH_closed_Henkin.  It does not
  assert the existence of T, restrict the cardinality of Σ, or identify
  operations by their pointwise behavior.  The βη field uses conversions
  whose intermediate terms remain in ℒ(Σ), as stipulated by the interface.
\<close>

context pH_closed_Henkin
begin

sublocale Canonical: pbbk_model signature pHc_domain pHc_denote pHc_holds
proof (unfold_locales)
  show "pHc_domain \<sigma> \<noteq> {}" for \<sigma> by (rule pHc_domain_nonempty)
next
  fix \<Gamma> M \<sigma> g
  assume typed: "has_ptype \<Gamma> M \<sigma>" and sig: "pterm_in_signature signature M"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_denote g M \<in> pHc_domain \<sigma>" by (rule pHc_denote_type[OF typed sig env])
next
  fix \<Gamma> n \<sigma> g
  assume lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_denote g (PVar n) = g n" by (rule pHc_denote_Var[OF lookup env])
next
  fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
  assume F: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and A: "has_ptype \<Gamma> A \<sigma>"
    and G: "has_ptype \<Delta> G (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and B: "has_ptype \<Delta> B \<sigma>"
    and sigFA: "pterm_in_signature signature (PApp F A)"
    and sigGB: "pterm_in_signature signature (PApp G B)"
    and envg: "pbbk_env_typed pHc_domain \<Gamma> g" and envh: "pbbk_env_typed pHc_domain \<Delta> h"
    and eqF: "pHc_denote g F = pHc_denote h G" and eqA: "pHc_denote g A = pHc_denote h B"
  have sf: "pterm_in_signature signature F" and sa: "pterm_in_signature signature A"
    and sg: "pterm_in_signature signature G" and sb: "pterm_in_signature signature B"
    using sigFA sigGB by simp_all
  show "pHc_denote g (PApp F A) = pHc_denote h (PApp G B)"
    by (simp only: pHc_denote_App[OF F A sf sa envg] pHc_denote_App[OF G B sg sb envh] eqF eqA)
next
  fix \<Gamma> M \<sigma> \<Delta> g h
  assume typed: "has_ptype \<Gamma> M \<sigma>" and typed': "has_ptype \<Delta> M \<sigma>"
    and sig: "pterm_in_signature signature M"
    and envg: "pbbk_env_typed pHc_domain \<Gamma> g" and envh: "pbbk_env_typed pHc_domain \<Delta> h"
    and same: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> g n = h n"
  show "pHc_denote g M = pHc_denote h M" by (rule pHcm_denote_locality[OF same])
next
  fix \<Gamma> M \<sigma> r \<Delta> g
  assume typed: "has_ptype \<Gamma> M \<sigma>" and sig: "pterm_in_signature signature M"
    and injective: "inj r" and env: "pbbk_env_typed pHc_domain \<Delta> g"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  show "pHc_denote g (prename r M) = pHc_denote (\<lambda>n. g (r n)) M" by (rule pHcm_denote_rename)
next
  fix \<Gamma> \<sigma> M N g
  assume conversion: "pbeta_eta_equiv_in_signature signature \<Gamma> \<sigma> M N"
    and sigM: "pterm_in_signature signature M" and sigN: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_denote g M = pHc_denote g N" by (rule pHcm_denote_beta_eta[OF conversion env])
next
  fix \<Gamma> A g
  assume typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PNeg A)) = (\<not> pHc_holds (pHc_denote g A))"
    by (rule pHc_truth_Neg[OF typed sig env])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PConj A B)) = (pHc_holds (pHc_denote g A) \<and> pHc_holds (pHc_denote g B))"
    by (rule pHc_truth_Conj[OF A B sa sb env])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PDisj A B)) = (pHc_holds (pHc_denote g A) \<or> pHc_holds (pHc_denote g B))"
    by (rule pHc_truth_Disj[OF A B sa sb env])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PImp A B)) = (pHc_holds (pHc_denote g A) \<longrightarrow> pHc_holds (pHc_denote g B))"
    by (rule pHc_truth_Imp[OF A B sa sb env])
next
  fix \<sigma> \<Gamma> A g
  assume body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PForall \<sigma> A)) =
    (\<forall>a \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend a g) A))"
    by (rule pHc_truth_Forall[OF body sig env])
next
  fix \<sigma> \<Gamma> A g
  assume body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PExists \<sigma> A)) =
    (\<exists>a \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend a g) A))"
    by (rule pHc_truth_Exists[OF body sig env])
next
  fix \<Gamma> M \<sigma> N g
  assume M: "has_ptype \<Gamma> M \<sigma>" and N: "has_ptype \<Gamma> N \<sigma>"
    and sm: "pterm_in_signature signature M" and sn: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  show "pHc_holds (pHc_denote g (PEq \<sigma> M N)) = (pHc_denote g M = pHc_denote g N)"
    by (rule pHc_truth_Eq[OF M N sm sn env])
qed

theorem pHc_is_pbbk_model:
  "pbbk_model signature pHc_domain pHc_denote pHc_holds"
  by (rule Canonical.pbbk_model_axioms)

text \<open>
  The theorem retains the locale premise pH_Henkin_theory Σ [] T.
  It verifies the canonical data once such a T is given; it does not
  discharge the independent arbitrary-signature Henkin existence theorem.
\<close>

end
end
