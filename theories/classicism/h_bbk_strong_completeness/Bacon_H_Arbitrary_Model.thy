theory Bacon_H_Arbitrary_Model
  imports Bacon_H_Arbitrary_Henkin
begin

section \<open>Returning from the expanded signature to the original theory\<close>

text \<open>
  ⟦A⟧original,g = ⟦ι(A)⟧expanded,g. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: The pullback changes constant interpretation only; domains,
  assignments, and valuation remain fixed, including unnamed witness values.

  Status: Model existence for arbitrary consistent closed theories in the represented
  universal string language; no first-class-constant or arbitrary-cardinality
  translation is claimed.
\<close>

lemma H_rename_constants_free_variables:
  "bbk_fv (H_rename_constants k M) = bbk_fv M"
  by (induction M) simp_all

lemma H_rename_constants_beta_eta:
  assumes conversion: "beta_eta_equiv \<Gamma> \<sigma> M N"
  shows "beta_eta_equiv \<Gamma> \<sigma> (H_rename_constants k M) (H_rename_constants k N)"
  using conversion
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule beta_eta_equiv.Refl[OF H_rename_constants_type[OF Refl.hyps]])
next
  case (Beta \<Gamma> M \<tau> N)
  show ?case by (rule beta_eta_equiv.Beta[OF H_rename_constants_type[OF Beta.hyps(1)]
    H_rename_constants_type[OF Beta.hyps(2)] H_rename_constants_beta_step[OF Beta.hyps(3)]])
next
  case (Eta \<Gamma> M \<tau> N)
  show ?case by (rule beta_eta_equiv.Eta[OF H_rename_constants_type[OF Eta.hyps(1)]
    H_rename_constants_type[OF Eta.hyps(2)] H_rename_constants_eta_step[OF Eta.hyps(3)]])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1,2)])
qed

definition H_BBK_constant_pullback ::
    "((nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow>
      (nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v" where
  "H_BBK_constant_pullback J k g A = J g (H_rename_constants k A)"

lemma H_BBK_constant_pullback_Const:
  "H_BBK_constant_pullback J k g (Const c \<sigma>) = J g (Const (k c) \<sigma>)"
  by (simp only: H_BBK_constant_pullback_def H_rename_constants.simps)

subsection \<open>Renaming constants preserves the exact model conditions\<close>

text \<open>
  𝔐expanded ⊨ ι(S) ⇒ 𝔐original ⊨ S. Bacon–Dorr, Definition 3.1, pp. 43–44.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: The renamed interpretation is checked against every BBK
  field. Variables and their domains are unchanged.

  Status: Actual equality and all logical truth clauses survive the pullback.
\<close>

lemma H_BBK_constant_pullback_model:
  assumes model: "bbk_model (\<lambda>_. UNIV) D J V"
  shows "bbk_model (\<lambda>_. UNIV) D (H_BBK_constant_pullback J k) V"
proof -
  interpret M: bbk_model "\<lambda>_. UNIV" D J V by (rule model)
  have sig: "bbk_in_signature (\<lambda>_. UNIV) A" for A by simp
  show ?thesis
  proof (unfold_locales)
    show "D \<sigma> \<noteq> {}" for \<sigma> by (rule M.domain_nonempty)
  next
    fix \<Gamma> A \<sigma> g
    assume typed: "\<Gamma> \<turnstile> A : \<sigma>" and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and env: "bbk_env_typed D \<Gamma> g"
    show "H_BBK_constant_pullback J k g A \<in> D \<sigma>"
      unfolding H_BBK_constant_pullback_def
      by (rule M.denote_type[OF H_rename_constants_type[OF typed] sig env])
  next
    fix \<Gamma> n \<sigma> g
    assume lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "bbk_env_typed D \<Gamma> g"
    show "H_BBK_constant_pullback J k g (Var n) = g n"
      by (simp only: H_BBK_constant_pullback_def H_rename_constants.simps M.denote_var[OF lookup env])
  next
    fix \<Gamma> F \<sigma> \<tau> A \<Delta> G B g h
    assume F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and A: "\<Gamma> \<turnstile> A : \<sigma>"
      and G: "\<Delta> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>" and B: "\<Delta> \<turnstile> B : \<sigma>"
      and sigF: "bbk_in_signature (\<lambda>_. UNIV) (App F A)"
      and sigG: "bbk_in_signature (\<lambda>_. UNIV) (App G B)"
      and envg: "bbk_env_typed D \<Gamma> g" and envh: "bbk_env_typed D \<Delta> h"
      and eqF: "H_BBK_constant_pullback J k g F = H_BBK_constant_pullback J k h G"
      and eqA: "H_BBK_constant_pullback J k g A = H_BBK_constant_pullback J k h B"
    have eqF': "J g (H_rename_constants k F) = J h (H_rename_constants k G)"
      using eqF by (simp only: H_BBK_constant_pullback_def)
    have eqA': "J g (H_rename_constants k A) = J h (H_rename_constants k B)"
      using eqA by (simp only: H_BBK_constant_pullback_def)
    show "H_BBK_constant_pullback J k g (App F A) = H_BBK_constant_pullback J k h (App G B)"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.denote_application_cong[OF H_rename_constants_type[OF F] H_rename_constants_type[OF A]
            H_rename_constants_type[OF G] H_rename_constants_type[OF B] sig sig envg envh eqF' eqA'])
  next
    fix \<Gamma> A \<sigma> \<Delta> g h
    assume typed: "\<Gamma> \<turnstile> A : \<sigma>" and typed': "\<Delta> \<turnstile> A : \<sigma>"
      and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and envg: "bbk_env_typed D \<Gamma> g" and envh: "bbk_env_typed D \<Delta> h"
      and same: "\<And>n. n \<in> bbk_fv A \<Longrightarrow> g n = h n"
    have same': "\<And>n. n \<in> bbk_fv (H_rename_constants k A) \<Longrightarrow> g n = h n"
      using same by (simp only: H_rename_constants_free_variables)
    show "H_BBK_constant_pullback J k g A = H_BBK_constant_pullback J k h A"
      unfolding H_BBK_constant_pullback_def
      by (rule M.denote_locality[OF H_rename_constants_type[OF typed]
            H_rename_constants_type[OF typed'] sig envg envh same'])
  next
    fix \<Gamma> A \<sigma> r \<Delta> g
    assume typed: "\<Gamma> \<turnstile> A : \<sigma>" and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and injective: "inj r" and env: "bbk_env_typed D \<Delta> g"
      and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
    show "H_BBK_constant_pullback J k g (rename r A) = H_BBK_constant_pullback J k (\<lambda>n. g (r n)) A"
      unfolding H_BBK_constant_pullback_def H_rename_constants_rename
      by (rule M.denote_rename[OF H_rename_constants_type[OF typed] sig injective env ren])
  next
    fix \<Gamma> \<sigma> A B g
    assume conversion: "beta_eta_equiv \<Gamma> \<sigma> A B"
      and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
      and env: "bbk_env_typed D \<Gamma> g"
    show "H_BBK_constant_pullback J k g A = H_BBK_constant_pullback J k g B"
      unfolding H_BBK_constant_pullback_def
      by (rule M.denote_beta_eta[OF H_rename_constants_beta_eta[OF conversion] sig sig env])
  next
    fix \<Gamma> A g
    assume typed: "\<Gamma> \<turnstile> A : Prop" and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Neg A)) = (\<not> V (H_BBK_constant_pullback J k g A))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_neg[OF H_rename_constants_type[OF typed] sig env])
  next
    fix \<Gamma> A B g
    assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
      and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Conj A B)) =
        (V (H_BBK_constant_pullback J k g A) \<and> V (H_BBK_constant_pullback J k g B))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_conj[OF H_rename_constants_type[OF A] H_rename_constants_type[OF B] sig sig env])
  next
    fix \<Gamma> A B g
    assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
      and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Disj A B)) =
        (V (H_BBK_constant_pullback J k g A) \<or> V (H_BBK_constant_pullback J k g B))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_disj[OF H_rename_constants_type[OF A] H_rename_constants_type[OF B] sig sig env])
  next
    fix \<Gamma> A B g
    assume A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
      and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Imp A B)) =
        (V (H_BBK_constant_pullback J k g A) \<longrightarrow> V (H_BBK_constant_pullback J k g B))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_imp[OF H_rename_constants_type[OF A] H_rename_constants_type[OF B] sig sig env])
  next
    fix \<sigma> \<Gamma> A g
    assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Forall \<sigma> A)) =
        (\<forall>a \<in> D \<sigma>. V (H_BBK_constant_pullback J k (bbk_extend a g) A))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_forall[OF H_rename_constants_type[OF body] sig env])
  next
    fix \<sigma> \<Gamma> A g
    assume body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and signature: "bbk_in_signature (\<lambda>_. UNIV) A"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Exists \<sigma> A)) =
        (\<exists>a \<in> D \<sigma>. V (H_BBK_constant_pullback J k (bbk_extend a g) A))"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_exists[OF H_rename_constants_type[OF body] sig env])
  next
    fix \<Gamma> A \<sigma> B g
    assume A: "\<Gamma> \<turnstile> A : \<sigma>" and B: "\<Gamma> \<turnstile> B : \<sigma>"
      and sigA: "bbk_in_signature (\<lambda>_. UNIV) A" and sigB: "bbk_in_signature (\<lambda>_. UNIV) B"
      and env: "bbk_env_typed D \<Gamma> g"
    show "V (H_BBK_constant_pullback J k g (Eq \<sigma> A B)) =
        (H_BBK_constant_pullback J k g A = H_BBK_constant_pullback J k g B)"
      unfolding H_BBK_constant_pullback_def H_rename_constants.simps
      by (rule M.valuation_identity[OF H_rename_constants_type[OF A] H_rename_constants_type[OF B] sig sig env])
  qed
qed

subsection \<open>Model existence for arbitrary consistent sets of sentences\<close>

text \<open>
  Conₕ(S) ⇒ ∃𝔐, ∀A ∈ S, 𝔐 ⊨ A. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem
  15.3, pp. 320–321.

  Isabelle representation: S is a typed set of closed sentences, not necessarily
  finite or deductively closed. The existential model uses the fixed HOL carrier of
  tagged classes.

  Status: Arbitrary-theory model existence for represented H; natural-number transport
  is supplied in h_bbk_countable.
\<close>

theorem H_arbitrary_BBK_model_exists:
  assumes typed: "typed_theory [] S" and consistent: "H_consistent [] S"
  shows "\<exists>D :: otype \<Rightarrow> h_bbk_value set.
    \<exists>J :: (nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value.
    \<exists>V :: h_bbk_value \<Rightarrow> bool.
      bbk_model (\<lambda>_. UNIV) D J V \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  obtain U where henkin_U: "H_Henkin_theory [] U"
    and extends: "H_rename_constants H_original_name ` S \<subseteq> U"
  proof (rule H_arbitrary_Henkin_extension_exists[OF typed consistent])
    fix U
    assume henkin_U: "H_Henkin_theory [] U"
      and extends: "H_rename_constants H_original_name ` S \<subseteq> U"
    show thesis by (rule that[where U=U, OF henkin_U extends])
  qed
  interpret C: H_closed_Henkin U by (unfold_locales) (rule henkin_U)
  let ?D = "H_closed_Henkin.H_BBK_domain U"
  let ?J = "H_closed_Henkin.H_BBK_denote U"
  let ?V = "H_closed_Henkin.H_BBK_holds U"
  let ?K = "H_BBK_constant_pullback ?J H_original_name"
  have canonical_model: "bbk_model (\<lambda>_. UNIV) ?D ?J ?V" by (rule C.H_BBK_canonical_model)
  have pulled_model: "bbk_model (\<lambda>_. UNIV) ?D ?K ?V"
    by (rule H_BBK_constant_pullback_model[where k=H_original_name, OF canonical_model])
  have satisfies: "\<forall>A \<in> S. \<forall>g. ?V (?K g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have A_type: "[] \<turnstile> A : Prop" by (rule typed_theoryD[OF typed member])
    have mapped_type: "[] \<turnstile> H_rename_constants H_original_name A : Prop"
      by (rule H_rename_constants_type[OF A_type])
    have mapped_member: "H_rename_constants H_original_name A \<in> H_rename_constants H_original_name ` S"
      by (rule imageI[OF member])
    have in_U: "H_rename_constants H_original_name A \<in> U"
      by (rule subsetD[OF extends mapped_member])
    have truth: "?V (?J g (H_rename_constants H_original_name A))"
      using C.H_BBK_closed_truth_lemma[OF mapped_type, where g=g] in_U by blast
    show "?V (?K g A)" using truth by (simp only: H_BBK_constant_pullback_def)
  qed
  show ?thesis
    by (rule exI[where x="?D"], rule exI[where x="?K"], rule exI[where x="?V"], rule conjI)
      (rule pulled_model, rule satisfies)
qed

text \<open>
  S need not be finite or deductively closed: every typed H-consistent set
  of closed sentences has a model of the represented universal signature.
  The carrier is the fixed HOL type of tagged classes; no quantification
  over HOL carrier types is hidden in the existential statement.  The
  theorem does not yet identify the canonical carrier with a subset of
  the natural numbers or formalize arbitrary-cardinality signatures.
\<close>

end
