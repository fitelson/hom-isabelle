theory Bacon_Parametric_Henkin_Names
  imports Bacon_Parametric_Henkin_One_Step
begin

section \<open>A single name carrier closed under witness formation\<close>

text \<open>
  Starting from Σσ, use old names ι(c) and witness names cσ,A, where A may
  already contain witness names.  Thus ∃v:σ.A in the final language has a
  witness label in that same language; the carrier does not change each round.

  Isabelle representation: phenkin_full_name is a nested positive datatype.
  Its witness constructor contains a pterm over phenkin_full_name itself.
  The pterm name parameter is positive, so this is a finite-tree datatype,
  not a negative or self-referential function-space equation.

  Status: a self-sufficient name/signature construction only.  No countability,
  consistency, completeness, or completed Henkin theory is assumed.
\<close>

datatype 'c phenkin_full_name =
    PFOriginal 'c
  | PFWitness otype "'c phenkin_full_name pterm"

subsection \<open>The least admissible expanded signature\<close>

text \<open>
  Σ⁺σ contains ι(c) for c ∈ Σσ and cσ,A whenever A:t has only its displayed
  free v:σ and A ∈ ℒ(Σ⁺).  The latter condition includes witness-bearing A.

  Isabelle representation: mutually inductive name and term membership make
  this closure positive and explicit.  Constants use name membership;
  compound terms inherit membership from their immediate subterms.

  Status: the least generated signature, not an assumption of pre-existing
  fresh names.  Membership does not assert truth of a witness axiom.
\<close>

inductive phenkin_full_name_in ::
    "'c psignature \<Rightarrow> otype \<Rightarrow> 'c phenkin_full_name \<Rightarrow> bool"
  and phenkin_full_term_in ::
    "'c psignature \<Rightarrow> 'c phenkin_full_name pterm \<Rightarrow> bool"
  for \<Sigma> :: "'c psignature" where
  Original: "c \<in> \<Sigma> \<sigma> \<Longrightarrow> phenkin_full_name_in \<Sigma> \<sigma> (PFOriginal c)"
| Witness: "has_ptype [\<sigma>] A Prop \<Longrightarrow> phenkin_full_term_in \<Sigma> A \<Longrightarrow>
    phenkin_full_name_in \<Sigma> \<sigma> (PFWitness \<sigma> A)"
| Var: "phenkin_full_term_in \<Sigma> (PVar n)"
| Const: "phenkin_full_name_in \<Sigma> \<sigma> c \<Longrightarrow> phenkin_full_term_in \<Sigma> (PConst c \<sigma>)"
| App: "phenkin_full_term_in \<Sigma> M \<Longrightarrow> phenkin_full_term_in \<Sigma> N \<Longrightarrow>
    phenkin_full_term_in \<Sigma> (PApp M N)"
| Lam: "phenkin_full_term_in \<Sigma> M \<Longrightarrow> phenkin_full_term_in \<Sigma> (PLam \<sigma> M)"
| Eq: "phenkin_full_term_in \<Sigma> M \<Longrightarrow> phenkin_full_term_in \<Sigma> N \<Longrightarrow>
    phenkin_full_term_in \<Sigma> (PEq \<sigma> M N)"
| Neg: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> (PNeg A)"
| Conj: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> B \<Longrightarrow>
    phenkin_full_term_in \<Sigma> (PConj A B)"
| Disj: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> B \<Longrightarrow>
    phenkin_full_term_in \<Sigma> (PDisj A B)"
| Imp: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> B \<Longrightarrow>
    phenkin_full_term_in \<Sigma> (PImp A B)"
| Forall: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> (PForall \<sigma> A)"
| Exists: "phenkin_full_term_in \<Sigma> A \<Longrightarrow> phenkin_full_term_in \<Sigma> (PExists \<sigma> A)"

definition phenkin_full_signature ::
    "'c psignature \<Rightarrow> 'c phenkin_full_name psignature" where
  "phenkin_full_signature \<Sigma> \<sigma> = {n. phenkin_full_name_in \<Sigma> \<sigma> n}"

lemma phenkin_full_original_membership:
  "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
  by (auto simp: phenkin_full_signature_def
    intro: phenkin_full_name_in_phenkin_full_term_in.Original elim: phenkin_full_name_in.cases)

lemma phenkin_full_term_signature:
  "phenkin_full_term_in \<Sigma> A \<longleftrightarrow>
    pterm_in_signature (phenkin_full_signature \<Sigma>) A"
  by (induction A)
    (auto simp: phenkin_full_signature_def
      intro: phenkin_full_name_in_phenkin_full_term_in.intros elim: phenkin_full_term_in.cases)

lemma phenkin_full_witness_membership:
  "PFWitness \<sigma> A \<in> phenkin_full_signature \<Sigma> \<tau> \<longleftrightarrow>
    \<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and>
      pterm_in_signature (phenkin_full_signature \<Sigma>) A"
proof
  assume member: "PFWitness \<sigma> A \<in> phenkin_full_signature \<Sigma> \<tau>"
  have named: "phenkin_full_name_in \<Sigma> \<tau> (PFWitness \<sigma> A)"
    using member by (simp only: phenkin_full_signature_def mem_Collect_eq)
  have parts: "\<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and> phenkin_full_term_in \<Sigma> A"
    using named by (cases rule: phenkin_full_name_in.cases) auto
  have tag: "\<sigma> = \<tau>" by (rule conjunct1[OF parts])
  have body: "has_ptype [\<sigma>] A Prop" by (rule conjunct1[OF conjunct2[OF parts]])
  have admitted: "phenkin_full_term_in \<Sigma> A" by (rule conjunct2[OF conjunct2[OF parts]])
  have sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
    by (rule iffD1[OF phenkin_full_term_signature admitted])
  show "\<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and>
    pterm_in_signature (phenkin_full_signature \<Sigma>) A"
    by (rule conjI[OF tag conjI[OF body sig]])
next
  assume parts: "\<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and>
    pterm_in_signature (phenkin_full_signature \<Sigma>) A"
  have tag: "\<sigma> = \<tau>" by (rule conjunct1[OF parts])
  have body: "has_ptype [\<sigma>] A Prop" by (rule conjunct1[OF conjunct2[OF parts]])
  have sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
    by (rule conjunct2[OF conjunct2[OF parts]])
  have admitted: "phenkin_full_term_in \<Sigma> A"
    by (rule iffD2[OF phenkin_full_term_signature sig])
  have named: "phenkin_full_name_in \<Sigma> \<sigma> (PFWitness \<sigma> A)"
    by (rule phenkin_full_name_in_phenkin_full_term_in.Witness[OF body admitted])
  show "PFWitness \<sigma> A \<in> phenkin_full_signature \<Sigma> \<tau>"
    using named by (simp only: phenkin_full_signature_def mem_Collect_eq tag)
qed

subsection \<open>Injective original-language embedding and disjoint witnesses\<close>

text \<open>
  A ∈ ℒ(Σ) embeds as ι(A) ∈ ℒ(Σ⁺); no cσ,B occurs in ι(A).
  Typing and Σ; Γ ⊢H A are preserved by this embedding.

  Isabelle representation: phenkin_full_embed reuses phenkin_map with
  PFOriginal.  Its projection has an explicit default only off the old-name
  image; the inverse theorem applies to embedded terms.

  Status: injective syntax embedding and forward proof preservation.
  Neither proof reflection nor consistency preservation is asserted.
\<close>

definition phenkin_full_embed ::
    "'c pterm \<Rightarrow> 'c phenkin_full_name pterm" where
  "phenkin_full_embed A = phenkin_map PFOriginal A"

fun phenkin_full_project :: "'c \<Rightarrow> 'c phenkin_full_name \<Rightarrow> 'c" where
  "phenkin_full_project d (PFOriginal c) = c"
| "phenkin_full_project d (PFWitness \<sigma> A) = d"

lemma phenkin_full_embed_left_inverse:
  "phenkin_map (phenkin_full_project d) (phenkin_full_embed A) = A"
  unfolding phenkin_full_embed_def by (induction A) simp_all

lemma phenkin_full_embed_injective:
  fixes d :: 'c
  assumes eq: "phenkin_full_embed (A :: 'c pterm) = phenkin_full_embed B"
  shows "A = B"
proof -
  have projected: "phenkin_map (phenkin_full_project d) (phenkin_full_embed A) =
    phenkin_map (phenkin_full_project d) (phenkin_full_embed B)"
    by (rule arg_cong[where f="phenkin_map (phenkin_full_project d)", OF eq])
  show ?thesis using projected by (simp only: phenkin_full_embed_left_inverse)
qed

lemma phenkin_full_embed_type:
  "has_ptype \<Gamma> A \<tau> \<Longrightarrow> has_ptype \<Gamma> (phenkin_full_embed A) \<tau>"
  unfolding phenkin_full_embed_def by (rule phenkin_map_type)

lemma phenkin_full_embed_signature:
  "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_embed A) =
    pterm_in_signature \<Sigma> A"
  unfolding phenkin_full_embed_def
  by (induction A) (simp_all add: phenkin_full_original_membership)

lemma phenkin_full_embed_language:
  assumes old: "pterm_in_language \<Sigma> \<Gamma> A \<tau>"
  shows "pterm_in_language (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A) \<tau>"
proof -
  note parts = old[unfolded pterm_in_language_def]
  have typed: "has_ptype \<Gamma> A \<tau>" by (rule conjunct1[OF parts])
  have sig: "pterm_in_signature \<Sigma> A" by (rule conjunct2[OF parts])
  have embedded_type: "has_ptype \<Gamma> (phenkin_full_embed A) \<tau>"
    by (rule phenkin_full_embed_type[OF typed])
  have embedded_sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_embed A)"
    using sig by (simp only: phenkin_full_embed_signature)
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF embedded_type embedded_sig])
qed

lemma phenkin_full_embed_proves:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> A"
  shows "pH_proves (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A)"
  unfolding phenkin_full_embed_def
proof (rule phenkin_map_proves[OF derivation])
  fix c \<sigma>
  assume declared: "c \<in> \<Sigma> \<sigma>"
  have membership_iff:
    "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
    by (rule phenkin_full_original_membership[where \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma>])
  show "PFOriginal c \<in> phenkin_full_signature \<Sigma> \<sigma>"
    by (rule iffD2[OF membership_iff declared])
qed

lemma phenkin_full_names_disjoint:
  "PFOriginal c \<noteq> PFWitness \<sigma> A"
  by simp

lemma phenkin_full_witness_labels_injective:
  "PFWitness \<sigma> A = PFWitness \<tau> B \<longleftrightarrow> \<sigma> = \<tau> \<and> A = B"
  by simp

lemma phenkin_full_witness_fresh_original:
  "PFWitness \<sigma> A \<notin> phenkin_names (phenkin_full_embed B)"
  unfolding phenkin_full_embed_def by (induction B) simp_all

subsection \<open>Witness availability and signature closure in the final language\<close>

text \<open>
  For every closed ∃v:σ.A ∈ ℒ(Σ⁺), the same Σ⁺σ contains cσ,A, and
  (∃v:σ.A) → A[cσ,A/v] belongs to ℒ(Σ⁺), even if A contains witnesses.

  Isabelle representation: the final witness and axiom use A directly,
  without another name-type expansion or an embedding into a later carrier.

  Status: typed witness availability and closure of the signature.  No
  witness axiom is asserted as an H theorem or adjoined to a theory here.
\<close>

definition phenkin_full_witness ::
    "otype \<Rightarrow> 'c phenkin_full_name pterm \<Rightarrow> 'c phenkin_full_name pterm" where
  "phenkin_full_witness \<sigma> A = PConst (PFWitness \<sigma> A) \<sigma>"

definition phenkin_full_witness_axiom ::
    "otype \<Rightarrow> 'c phenkin_full_name pterm \<Rightarrow> 'c phenkin_full_name pterm" where
  "phenkin_full_witness_axiom \<sigma> A =
    PImp (PExists \<sigma> A) (psubst0 (phenkin_full_witness \<sigma> A) A)"

lemma phenkin_full_witness_type:
  "has_ptype \<Gamma> (phenkin_full_witness \<sigma> A) \<sigma>"
  unfolding phenkin_full_witness_def by (rule has_ptype.PConst)

lemma phenkin_full_witness_signature:
  assumes body: "has_ptype [\<sigma>] A Prop"
    and sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
  shows "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_witness \<sigma> A)"
proof -
  have admitted: "phenkin_full_term_in \<Sigma> A"
    by (rule iffD2[OF phenkin_full_term_signature sig])
  have named: "phenkin_full_name_in \<Sigma> \<sigma> (PFWitness \<sigma> A)"
    by (rule phenkin_full_name_in_phenkin_full_term_in.Witness[OF body admitted])
  show ?thesis by (simp only: phenkin_full_witness_def pterm_in_signature.simps
    phenkin_full_signature_def mem_Collect_eq named)
qed

lemma phenkin_full_witness_axiom_language:
  assumes body: "has_ptype [\<sigma>] A Prop"
    and sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
  shows "pterm_in_language (phenkin_full_signature \<Sigma>) [] (phenkin_full_witness_axiom \<sigma> A) Prop"
proof -
  have instance_type: "has_ptype [] (psubst0 (phenkin_full_witness \<sigma> A) A) Prop"
    by (rule psubst0_preserves_typing[OF body phenkin_full_witness_type])
  have typed: "has_ptype [] (phenkin_full_witness_axiom \<sigma> A) Prop"
    unfolding phenkin_full_witness_axiom_def
    by (rule has_ptype.PImp[OF has_ptype.PExists[OF body] instance_type])
  have witness_sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_witness \<sigma> A)"
    by (rule phenkin_full_witness_signature[OF body sig])
  have instance_sig: "pterm_in_signature (phenkin_full_signature \<Sigma>)
    (psubst0 (phenkin_full_witness \<sigma> A) A)"
    by (rule psubst0_signature[OF sig witness_sig])
  have guarded: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_witness_axiom \<sigma> A)"
    unfolding phenkin_full_witness_axiom_def
    by (simp only: pterm_in_signature.simps sig instance_sig)
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed guarded])
qed

theorem phenkin_full_every_existential_has_witness:
  assumes existential: "pterm_in_language (phenkin_full_signature \<Sigma>) [] (PExists \<sigma> A) Prop"
  shows "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_witness \<sigma> A) \<and>
    pterm_in_language (phenkin_full_signature \<Sigma>) [] (phenkin_full_witness_axiom \<sigma> A) Prop"
proof -
  note parts = existential[unfolded pterm_in_language_def]
  have ex_type: "has_ptype [] (PExists \<sigma> A) Prop" by (rule conjunct1[OF parts])
  have body: "has_ptype [\<sigma>] A Prop"
    by (rule conjunct2[OF iffD1[OF ptype_exists_iff ex_type]])
  have ex_sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) (PExists \<sigma> A)"
    by (rule conjunct2[OF parts])
  have sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
    using ex_sig by (simp only: pterm_in_signature.simps)
  show ?thesis by (rule conjI[OF phenkin_full_witness_signature[OF body sig]
    phenkin_full_witness_axiom_language[OF body sig]])
qed

text \<open>
  The carrier is now fixed across witness rounds.  The remaining theory
  construction must still organize witness axioms, prove freshness for the
  relevant intermediate theories, preserve consistency, and obtain a
  maximal consistent witness-complete extension.  Disjointness from the
  original embedding is proved; freshness relative to an arbitrary theory
  already using final names is not asserted.

  Isabelle representation: the mutually inductive membership predicates
  describe a generated signature, not a derivability relation.

  Status: no Henkin-consistency or completeness theorem is claimed.
\<close>

end
