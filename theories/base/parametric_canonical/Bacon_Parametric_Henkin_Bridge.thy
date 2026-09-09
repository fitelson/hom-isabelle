theory Bacon_Parametric_Henkin_Bridge
  imports
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Henkin_Existence
    Bacon_Parametric_Henkin_Theory
begin

section \<open>The constructed Henkin theory supplies the canonical locale\<close>

text \<open>
  The existence construction gives T with ∃v:σ.A ∈ T ⇒ A[c/v] ∈ T for
  some c ∈ Σσ.  The canonical theory interface asks only for a closed
  W:σ in ℒ(Σ) with A[W/v] ∈ T.  Taking W = c supplies that requirement.

  Isabelle representation: pH_closed_Henkin_theory Σ T is the construction
  predicate; pH_Henkin_theory Σ [] T is the canonical predicate, and
  pH_closed_Henkin Σ T is its locale predicate.  Their typing, consistency,
  negation-completeness, and deductive-closure fields agree after unfolding.
  Constant witnesses are stronger than arbitrary closed term witnesses.

  Status: a one-way bridge and existence of a canonical locale instance.
  No converse equivalence, canonical modelhood, truth lemma, or completeness
  theorem is asserted by this bridge.
\<close>

lemma pH_constructed_deductively_closed:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_deductively_closed \<Sigma> [] T"
proof (unfold pH_deductively_closed_def, intro allI impI)
  fix A
  assume d: "pH_set_derivable \<Sigma> [] T A"
  show "A \<in> T" by (rule pH_closed_Henkin_closed[OF constructed d])
qed

lemma pH_constructed_negation_complete:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_negation_complete \<Sigma> [] T"
proof (unfold pH_negation_complete_def, intro allI impI)
  fix A
  assume lang: "pterm_in_language \<Sigma> [] A Prop"
  show "A \<in> T \<or> PNeg A \<in> T" by (rule pH_closed_Henkin_decides[OF constructed lang])
qed

lemma pH_constructed_maximal_consistent:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_maximal_consistent \<Sigma> [] T"
proof -
  have typed: "pH_typed_theory \<Sigma> [] T" by (rule pH_closed_Henkin_typed[OF constructed])
  have closed: "pH_deductively_closed \<Sigma> [] T" by (rule pH_constructed_deductively_closed[OF constructed])
  have consistent: "pH_consistent \<Sigma> [] T" by (rule pH_closed_Henkin_consistent[OF constructed])
  have complete: "pH_negation_complete \<Sigma> [] T" by (rule pH_constructed_negation_complete[OF constructed])
  show ?thesis unfolding pH_maximal_consistent_def
    by (rule conjI[OF typed conjI[OF closed conjI[OF consistent complete]]])
qed

subsection \<open>A declared constant is a closed term witness\<close>

text \<open>
  c ∈ Σσ gives c:σ in the empty variable context, so A[c/v] is an
  instance of the canonical requirement A[W/v].

  Isabelle representation: choose the existing PConst c σ; no additional
  name, default denotation, or selection of a semantic representative is needed.
  Status: all signature and typing requirements of the witness are preserved.
\<close>

lemma pH_constructed_term_witness:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
    and member: "PExists \<sigma> A \<in> T"
  shows "\<exists>W. pterm_in_language \<Sigma> [] W \<sigma> \<and> psubst0 W A \<in> T"
proof -
  have constants: "\<exists>c \<in> \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T"
    by (rule pH_closed_Henkin_witness[OF constructed member])
  from constants obtain c where declared: "c \<in> \<Sigma> \<sigma>"
    and instance_member: "psubst0 (PConst c \<sigma>) A \<in> T" by (elim bexE)
  have typed: "has_ptype [] (PConst c \<sigma>) \<sigma>" by (rule has_ptype.PConst)
  have sig: "pterm_in_signature \<Sigma> (PConst c \<sigma>)" using declared by simp
  have lang: "pterm_in_language \<Sigma> [] (PConst c \<sigma>) \<sigma>"
    unfolding pterm_in_language_def by (rule conjI[OF typed sig])
  show ?thesis
  proof (rule exI[where x="PConst c \<sigma>"])
    show "pterm_in_language \<Sigma> [] (PConst c \<sigma>) \<sigma> \<and>
      psubst0 (PConst c \<sigma>) A \<in> T"
      by (rule conjI[OF lang instance_member])
  qed
qed

lemma pH_constructed_Henkin_witnessed:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_Henkin_witnessed \<Sigma> [] T"
proof (unfold pH_Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume body: "pterm_in_language \<Sigma> (\<sigma> # []) A Prop"
    and member: "PExists \<sigma> A \<in> T"
  show "\<exists>W. pterm_in_language \<Sigma> [] W \<sigma> \<and> psubst0 W A \<in> T"
    by (rule pH_constructed_term_witness[OF constructed member])
qed

theorem pH_constructed_Henkin_theory:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_Henkin_theory \<Sigma> [] T"
  unfolding pH_Henkin_theory_def
  by (rule conjI[OF pH_constructed_maximal_consistent[OF constructed]
    pH_constructed_Henkin_witnessed[OF constructed]])

lemma pH_constructed_closed_locale:
  assumes constructed: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_closed_Henkin \<Sigma> T"
  by (unfold_locales) (rule pH_constructed_Henkin_theory[OF constructed])

subsection \<open>Existence of a canonical-locale instance extending the old theory\<close>

text \<open>
  ConH(S) and typed S ⊆ ℒ(Σ) yield T ⊇ ι(S) satisfying the canonical
  Henkin assumptions in the expanded signature Σ⁺.

  Isabelle representation: phenkin_arbitrary_Henkin_extension supplies T;
  the preceding implication discharges the canonical locale predicate.
  Status: no countability hypothesis or semantic-model construction is used.
\<close>

theorem phenkin_canonical_Henkin_extension:
  assumes typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  obtains T where "image phenkin_full_embed S \<subseteq> T"
    and "pH_Henkin_theory (phenkin_full_signature \<Sigma>) [] T"
    and "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
proof -
  obtain T where extends: "image phenkin_full_embed S \<subseteq> T"
    and axioms: "phenkin_all_witness_axioms \<Sigma> \<subseteq> T"
    and constructed: "pH_closed_Henkin_theory (phenkin_full_signature \<Sigma>) T"
    by (rule phenkin_arbitrary_Henkin_extension[OF typed consistent])
  have canonical: "pH_Henkin_theory (phenkin_full_signature \<Sigma>) [] T"
    by (rule pH_constructed_Henkin_theory[OF constructed])
  have locale_instance: "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (rule pH_constructed_closed_locale[OF constructed])
  show thesis by (rule that[OF extends canonical locale_instance])
qed

corollary phenkin_canonical_Henkin_exists:
  assumes typed: "pH_typed_theory \<Sigma> [] S" and consistent: "pH_consistent \<Sigma> [] S"
  shows "\<exists>T. image phenkin_full_embed S \<subseteq> T \<and> pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
proof -
  obtain T where extends: "image phenkin_full_embed S \<subseteq> T"
    and canonical: "pH_Henkin_theory (phenkin_full_signature \<Sigma>) [] T"
    and locale_instance: "pH_closed_Henkin (phenkin_full_signature \<Sigma>) T"
    by (rule phenkin_canonical_Henkin_extension[OF typed consistent])
  show ?thesis by (rule exI[where x=T], rule conjI[OF extends locale_instance])
qed

end
