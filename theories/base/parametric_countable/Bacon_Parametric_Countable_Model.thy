theory Bacon_Parametric_Countable_Model
  imports Bacon_Parametric_Countable_Coding
    Bacon_Parametric_Canonical_Development.Bacon_Parametric_Canonical_Model
begin

section \<open>The canonical BBK model on natural-number domains\<close>

text \<open>
  Put Dσⁿ = c[Dσ], ⟦A⟧ⁿg = c(⟦A⟧c⁻¹∘g), and valⁿ(n) = val(c⁻¹(n)).
  These data form a BBK model with every Dσⁿ ⊆ ℕ.  Source: Bacon–Dorr,
  Theorem 3.2, pp.44–45, countable-signature refinement and p.45 n.64.

  Isabelle representation: transport every model field along the proved
  domain-restricted code/decode bijections.  βη conversions remain inside
  ℒ(Σ); truth of identity remains equality of denotations, not equality of
  truth values.  Quantifiers range over image domains, not all naturals.
  Status: conditional on pH_countable_closed_Henkin.  No arbitrary-theory
  model-existence theorem or semantic strengthening is asserted here.
\<close>

context pH_countable_closed_Henkin
begin

definition pHct_nat_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'c pHc_value" where
  "pHct_nat_env g = (\<lambda>n. pHct_decode (g n))"

definition pHct_nat_denote :: "(nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> nat" where
  "pHct_nat_denote g A = pHct_code (pHc_denote (pHct_nat_env g) A)"

definition pHct_nat_holds :: "nat \<Rightarrow> bool" where
  "pHct_nat_holds n = pHc_holds (pHct_decode n)"

lemma pHct_nat_env_typed:
  assumes env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  shows "pbbk_env_typed pHc_domain \<Gamma> (pHct_nat_env g)"
proof (unfold pbbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume look: "lookup \<Gamma> n = Some \<sigma>"
  have code: "g n \<in> pHct_nat_domain \<sigma>" by (rule pbbk_env_lookup[OF env look])
  show "pHct_nat_env g n \<in> pHc_domain \<sigma>"
    unfolding pHct_nat_env_def by (rule pHct_decode_typed[OF code])
qed

lemma pHct_nat_env_extend:
  "pHct_nat_env (pbbk_extend n g) = pbbk_extend (pHct_decode n) (pHct_nat_env g)"
  by (rule ext, rename_tac k, case_tac k)
    (simp_all only: pHct_nat_env_def pbbk_extend_zero pbbk_extend_Suc)

lemma pHct_nat_env_rename:
  "pHct_nat_env (\<lambda>n. g (r n)) = (\<lambda>n. pHct_nat_env g (r n))"
  by (rule ext) (simp only: pHct_nat_env_def)

lemma pHct_nat_canonical_type:
  "has_ptype \<Gamma> A \<sigma> \<Longrightarrow> pterm_in_signature signature A \<Longrightarrow>
    pbbk_env_typed pHct_nat_domain \<Gamma> g \<Longrightarrow>
    pHc_denote (pHct_nat_env g) A \<in> pHc_domain \<sigma>"
  by (rule Canonical.denote_type, assumption, assumption, rule pHct_nat_env_typed, assumption)

lemma pHct_nat_denote_type:
  "has_ptype \<Gamma> A \<sigma> \<Longrightarrow> pterm_in_signature signature A \<Longrightarrow>
    pbbk_env_typed pHct_nat_domain \<Gamma> g \<Longrightarrow> pHct_nat_denote g A \<in> pHct_nat_domain \<sigma>"
  unfolding pHct_nat_denote_def
  by (rule pHct_nat_domainI, rule pHct_nat_canonical_type; assumption)

lemma pHct_nat_truth_preservation:
  assumes typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  shows "pHct_nat_holds (pHct_nat_denote g A) = pHc_holds (pHc_denote (pHct_nat_env g) A)"
  by (simp only: pHct_nat_holds_def pHct_nat_denote_def
    pHct_decode_code_domain[OF pHct_nat_canonical_type[OF typed sig env]])

lemma pHct_nat_denotation_eq_iff:
  assumes M: "has_ptype \<Gamma> M \<sigma>" and N: "has_ptype \<Delta> N \<sigma>"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and g: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
    and h: "pbbk_env_typed pHct_nat_domain \<Delta> h"
  shows "pHct_nat_denote g M = pHct_nat_denote h N \<longleftrightarrow>
    pHc_denote (pHct_nat_env g) M = pHc_denote (pHct_nat_env h) N"
proof
  assume eq: "pHct_nat_denote g M = pHct_nat_denote h N"
  have codes: "pHct_code (pHc_denote (pHct_nat_env g) M) = pHct_code (pHc_denote (pHct_nat_env h) N)"
    using eq unfolding pHct_nat_denote_def .
  show "pHc_denote (pHct_nat_env g) M = pHc_denote (pHct_nat_env h) N"
    by (rule inj_onD[OF pHct_code_inj_on_domain codes
      pHct_nat_canonical_type[OF M ms g] pHct_nat_canonical_type[OF N ns h]])
next
  assume eq: "pHc_denote (pHct_nat_env g) M = pHc_denote (pHct_nat_env h) N"
  show "pHct_nat_denote g M = pHct_nat_denote h N" by (simp only: pHct_nat_denote_def eq)
qed

lemma pHct_nat_truth_extended:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g" and code: "n \<in> pHct_nat_domain \<sigma>"
  shows "pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A) =
    pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
  using pHct_nat_truth_preservation[OF body sig pbbk_env_extend[OF env code]]
  by (simp only: pHct_nat_env_extend)

lemma pHct_nat_forall_transfer:
  "(\<forall>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)) \<longleftrightarrow> (\<forall>v \<in> pHc_domain \<sigma>. P v)"
proof
  assume coded: "\<forall>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)"
  show "\<forall>v \<in> pHc_domain \<sigma>. P v"
  proof (rule ballI)
    fix v
    assume domain: "v \<in> pHc_domain \<sigma>"
    have "P (pHct_decode (pHct_code v))" by (rule bspec[OF coded pHct_nat_domainI[OF domain]])
    then show "P v" by (simp only: pHct_decode_code_domain[OF domain])
  qed
next
  assume original: "\<forall>v \<in> pHc_domain \<sigma>. P v"
  show "\<forall>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)"
    by (rule ballI, rule bspec[OF original], rule pHct_decode_typed, assumption)
qed

lemma pHct_nat_exists_transfer:
  "(\<exists>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)) \<longleftrightarrow> (\<exists>v \<in> pHc_domain \<sigma>. P v)"
proof
  assume coded: "\<exists>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)"
  obtain n where domain: "n \<in> pHct_nat_domain \<sigma>" and property: "P (pHct_decode n)"
    using coded by (elim bexE)
  show "\<exists>v \<in> pHc_domain \<sigma>. P v"
  proof (rule bexI[where x="pHct_decode n"])
    show "P (pHct_decode n)" by (rule property)
    show "pHct_decode n \<in> pHc_domain \<sigma>" by (rule pHct_decode_typed[OF domain])
  qed
next
  assume original: "\<exists>v \<in> pHc_domain \<sigma>. P v"
  obtain v where domain: "v \<in> pHc_domain \<sigma>" and property: "P v"
    using original by (elim bexE)
  have coded_property: "P (pHct_decode (pHct_code v))"
    using property by (simp only: pHct_decode_code_domain[OF domain])
  show "\<exists>n \<in> pHct_nat_domain \<sigma>. P (pHct_decode n)"
  proof (rule bexI[where x="pHct_code v"])
    show "P (pHct_decode (pHct_code v))" by (rule coded_property)
    show "pHct_code v \<in> pHct_nat_domain \<sigma>" by (rule pHct_nat_domainI[OF domain])
  qed
qed

subsection \<open>Every BBK field is preserved\<close>

text \<open>
  The bijection preserves application and actual identity; decoded
  assignments commute with binder extension.  Hence ∀ and ∃ range over
  precisely the original canonical domain after decoding.  Source:
  Bacon–Dorr Definition 3.1, pp.43–44, and Theorem 3.2.
\<close>

sublocale NatCanonical: pbbk_model signature pHct_nat_domain pHct_nat_denote pHct_nat_holds
proof (unfold_locales)
  show "pHct_nat_domain \<sigma> \<noteq> {}" for \<sigma> by (rule pHct_nat_domain_nonempty)
next
  fix \<Gamma> M \<sigma> g
  assume typed: "has_ptype \<Gamma> M \<sigma>" and sig: "pterm_in_signature signature M"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  show "pHct_nat_denote g M \<in> pHct_nat_domain \<sigma>" by (rule pHct_nat_denote_type[OF typed sig env])
next
  fix \<Gamma> n \<sigma> g
  assume look: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have original: "pHc_denote (pHct_nat_env g) (PVar n) = pHct_nat_env g n"
    by (rule Canonical.denote_var[OF look pHct_nat_env_typed[OF env]])
  have code: "g n \<in> pHct_nat_domain \<sigma>" by (rule pbbk_env_lookup[OF env look])
  have decoded: "pHc_denote (pHct_nat_env g) (PVar n) = pHct_decode (g n)"
    using original by (simp only: pHct_nat_env_def)
  show "pHct_nat_denote g (PVar n) = g n"
    by (simp only: pHct_nat_denote_def decoded pHct_code_decode[OF code])
next
  fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
  assume F: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and A: "has_ptype \<Gamma> A \<sigma>"
    and G: "has_ptype \<Delta> G (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and B: "has_ptype \<Delta> B \<sigma>"
    and sigFA: "pterm_in_signature signature (PApp F A)" and sigGB: "pterm_in_signature signature (PApp G B)"
    and envg: "pbbk_env_typed pHct_nat_domain \<Gamma> g" and envh: "pbbk_env_typed pHct_nat_domain \<Delta> h"
    and eqF: "pHct_nat_denote g F = pHct_nat_denote h G" and eqA: "pHct_nat_denote g A = pHct_nat_denote h B"
  have sf: "pterm_in_signature signature F" and sa: "pterm_in_signature signature A"
    and sg: "pterm_in_signature signature G" and sb: "pterm_in_signature signature B"
    using sigFA sigGB by simp_all
  have f_eq: "pHc_denote (pHct_nat_env g) F = pHc_denote (pHct_nat_env h) G"
    by (rule iffD1[OF pHct_nat_denotation_eq_iff[OF F G sf sg envg envh] eqF])
  have a_eq: "pHc_denote (pHct_nat_env g) A = pHc_denote (pHct_nat_env h) B"
    by (rule iffD1[OF pHct_nat_denotation_eq_iff[OF A B sa sb envg envh] eqA])
  have app_eq: "pHc_denote (pHct_nat_env g) (PApp F A) = pHc_denote (pHct_nat_env h) (PApp G B)"
    by (rule Canonical.denote_application_cong[OF F A G B sigFA sigGB
      pHct_nat_env_typed[OF envg] pHct_nat_env_typed[OF envh] f_eq a_eq])
  show "pHct_nat_denote g (PApp F A) = pHct_nat_denote h (PApp G B)"
    by (simp only: pHct_nat_denote_def app_eq)
next
  fix \<Gamma> M \<sigma> \<Delta> g h
  assume typed: "has_ptype \<Gamma> M \<sigma>" and typed': "has_ptype \<Delta> M \<sigma>"
    and sig: "pterm_in_signature signature M"
    and envg: "pbbk_env_typed pHct_nat_domain \<Gamma> g" and envh: "pbbk_env_typed pHct_nat_domain \<Delta> h"
    and same: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> g n = h n"
  have decoded: "pHct_nat_env g n = pHct_nat_env h n" if "n \<in> pbbk_fv M" for n
    by (simp only: pHct_nat_env_def same[OF that])
  show "pHct_nat_denote g M = pHct_nat_denote h M"
    by (simp only: pHct_nat_denote_def pHcm_denote_locality[OF decoded])
next
  fix \<Gamma> M \<sigma> r \<Delta> g
  assume typed: "has_ptype \<Gamma> M \<sigma>" and sig: "pterm_in_signature signature M"
    and injective: "inj r" and env: "pbbk_env_typed pHct_nat_domain \<Delta> g"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  show "pHct_nat_denote g (prename r M) = pHct_nat_denote (\<lambda>n. g (r n)) M"
    by (simp only: pHct_nat_denote_def pHcm_denote_rename pHct_nat_env_rename)
next
  fix \<Gamma> \<sigma> M N g
  assume conv: "pbeta_eta_equiv_in_signature signature \<Gamma> \<sigma> M N"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have original: "pHc_denote (pHct_nat_env g) M = pHc_denote (pHct_nat_env g) N"
    by (rule Canonical.denote_beta_eta[OF conv ms ns pHct_nat_env_typed[OF env]])
  show "pHct_nat_denote g M = pHct_nat_denote g N" by (simp only: pHct_nat_denote_def original)
next
  fix \<Gamma> A g
  assume A: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have ns: "pterm_in_signature signature (PNeg A)" using sig by simp
  show "pHct_nat_holds (pHct_nat_denote g (PNeg A)) = (\<not> pHct_nat_holds (pHct_nat_denote g A))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PNeg[OF A] ns env]
      pHct_nat_truth_preservation[OF A sig env] Canonical.valuation_neg[OF A sig pHct_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have sig: "pterm_in_signature signature (PConj A B)" using sa sb by simp
  show "pHct_nat_holds (pHct_nat_denote g (PConj A B)) =
    (pHct_nat_holds (pHct_nat_denote g A) \<and> pHct_nat_holds (pHct_nat_denote g B))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PConj[OF A B] sig env]
      pHct_nat_truth_preservation[OF A sa env] pHct_nat_truth_preservation[OF B sb env]
      Canonical.valuation_conj[OF A B sa sb pHct_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have sig: "pterm_in_signature signature (PDisj A B)" using sa sb by simp
  show "pHct_nat_holds (pHct_nat_denote g (PDisj A B)) =
    (pHct_nat_holds (pHct_nat_denote g A) \<or> pHct_nat_holds (pHct_nat_denote g B))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PDisj[OF A B] sig env]
      pHct_nat_truth_preservation[OF A sa env] pHct_nat_truth_preservation[OF B sb env]
      Canonical.valuation_disj[OF A B sa sb pHct_nat_env_typed[OF env]])
next
  fix \<Gamma> A B g
  assume A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have sig: "pterm_in_signature signature (PImp A B)" using sa sb by simp
  show "pHct_nat_holds (pHct_nat_denote g (PImp A B)) =
    (pHct_nat_holds (pHct_nat_denote g A) \<longrightarrow> pHct_nat_holds (pHct_nat_denote g B))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PImp[OF A B] sig env]
      pHct_nat_truth_preservation[OF A sa env] pHct_nat_truth_preservation[OF B sb env]
      Canonical.valuation_imp[OF A B sa sb pHct_nat_env_typed[OF env]])
next
  fix \<sigma> \<Gamma> A g
  assume body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have asig: "pterm_in_signature signature (PForall \<sigma> A)" using sig by simp
  have transfer: "(\<forall>n \<in> pHct_nat_domain \<sigma>. pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)) =
    (\<forall>v \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A))"
  proof
    have pointwise: "pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A) =
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      if "n \<in> pHct_nat_domain \<sigma>" for n
      by (rule pHct_nat_truth_extended[OF body sig env that])
    assume coded: "\<forall>n \<in> pHct_nat_domain \<sigma>.
      pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)"
    have decoded: "\<forall>n \<in> pHct_nat_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      using coded pointwise by blast
    show "\<forall>v \<in> pHc_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A)"
      by (rule iffD1[OF pHct_nat_forall_transfer decoded])
  next
    have pointwise: "pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A) =
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      if "n \<in> pHct_nat_domain \<sigma>" for n
      by (rule pHct_nat_truth_extended[OF body sig env that])
    assume original: "\<forall>v \<in> pHc_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A)"
    have decoded: "\<forall>n \<in> pHct_nat_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      by (rule iffD2[OF pHct_nat_forall_transfer original])
    show "\<forall>n \<in> pHct_nat_domain \<sigma>.
      pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)"
      using decoded pointwise by blast
  qed
  show "pHct_nat_holds (pHct_nat_denote g (PForall \<sigma> A)) =
    (\<forall>n \<in> pHct_nat_domain \<sigma>. pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PForall[OF body] asig env] transfer
      Canonical.valuation_forall[OF body sig pHct_nat_env_typed[OF env]])
next
  fix \<sigma> \<Gamma> A g
  assume body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have esig: "pterm_in_signature signature (PExists \<sigma> A)" using sig by simp
  have transfer: "(\<exists>n \<in> pHct_nat_domain \<sigma>. pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)) =
    (\<exists>v \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A))"
  proof
    have pointwise: "pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A) =
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      if "n \<in> pHct_nat_domain \<sigma>" for n
      by (rule pHct_nat_truth_extended[OF body sig env that])
    assume coded: "\<exists>n \<in> pHct_nat_domain \<sigma>.
      pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)"
    have decoded: "\<exists>n \<in> pHct_nat_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      using coded pointwise by blast
    show "\<exists>v \<in> pHc_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A)"
      by (rule iffD1[OF pHct_nat_exists_transfer decoded])
  next
    have pointwise: "pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A) =
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      if "n \<in> pHct_nat_domain \<sigma>" for n
      by (rule pHct_nat_truth_extended[OF body sig env that])
    assume original: "\<exists>v \<in> pHc_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend v (pHct_nat_env g)) A)"
    have decoded: "\<exists>n \<in> pHct_nat_domain \<sigma>.
      pHc_holds (pHc_denote (pbbk_extend (pHct_decode n) (pHct_nat_env g)) A)"
      by (rule iffD2[OF pHct_nat_exists_transfer original])
    show "\<exists>n \<in> pHct_nat_domain \<sigma>.
      pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A)"
      using decoded pointwise by blast
  qed
  show "pHct_nat_holds (pHct_nat_denote g (PExists \<sigma> A)) =
    (\<exists>n \<in> pHct_nat_domain \<sigma>. pHct_nat_holds (pHct_nat_denote (pbbk_extend n g) A))"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PExists[OF body] esig env] transfer
      Canonical.valuation_exists[OF body sig pHct_nat_env_typed[OF env]])
next
  fix \<Gamma> M \<sigma> N g
  assume M: "has_ptype \<Gamma> M \<sigma>" and N: "has_ptype \<Gamma> N \<sigma>"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and env: "pbbk_env_typed pHct_nat_domain \<Gamma> g"
  have sig: "pterm_in_signature signature (PEq \<sigma> M N)" using ms ns by simp
  show "pHct_nat_holds (pHct_nat_denote g (PEq \<sigma> M N)) = (pHct_nat_denote g M = pHct_nat_denote g N)"
    by (simp only: pHct_nat_truth_preservation[OF has_ptype.PEq[OF M N] sig env]
      Canonical.valuation_identity[OF M N ms ns pHct_nat_env_typed[OF env]]
      pHct_nat_denotation_eq_iff[OF M N ms ns env env])
qed

theorem pHct_nat_model: "pbbk_model signature pHct_nat_domain pHct_nat_denote pHct_nat_holds"
  by (rule NatCanonical.pbbk_model_axioms)

lemma pHct_nat_closed_truth_lemma:
  assumes lang: "pterm_in_language signature [] A Prop"
  shows "pHct_nat_holds (pHct_nat_denote g A) \<longleftrightarrow> A \<in> T"
proof -
  have typed: "has_ptype [] A Prop" using lang unfolding pterm_in_language_def by (rule conjunct1)
  have sig: "pterm_in_signature signature A" using lang unfolding pterm_in_language_def by (rule conjunct2)
  show ?thesis by (simp only: pHct_nat_truth_preservation[OF typed sig pbbk_env_empty]
    pHc_denote_closed[OF typed] pHc_holds_class[OF lang])
qed

end
end
