theory Bacon_Parametric_Henkin_Existence
  imports Bacon_Parametric_Henkin_Consistency
    Bacon_Parametric_Signature_Conservativity
    Bacon_Parametric_Lindenbaum
begin

section \<open>Henkin extension for an arbitrary signature and consistent closed theory\<close>

text \<open>
  If S ⊆ ℒ(Σ) is typed and H-consistent, there is a theory T in ℒ(Σ⁺)
  extending ι(S) that is typed, consistent, negation-complete, deductively
  closed, and witness-complete.  In particular, ∃v:σ.A ∈ T has an instance
  A[c/v] ∈ T for a declared c:σ.  This is the Henkin-extension step of
  Bacon, Proposition 15.4, and Bacon–Dorr, Theorem 3.2, p.45 n.64.

  Isabelle representation: combine syntactic conservativity of ι, consistency
  of all final-language witness axioms, and a Zorn maximal extension.
  Actual membership of a witness instance follows by MP and deductive
  closure; the availability of a witness name alone is not substituted for it.

  Status: arbitrary name carriers and arbitrary typed consistent sets of
  closed sentences, with no countability premise.  Construction of the
  canonical semantic model from this theory is a further step.
\<close>

definition pH_closed_Henkin_theory :: "'c psignature \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_closed_Henkin_theory \<Sigma> T \<longleftrightarrow>
    pH_typed_theory \<Sigma> [] T \<and> pH_consistent \<Sigma> [] T \<and>
    (\<forall>A. pterm_in_language \<Sigma> [] A Prop \<longrightarrow> A \<in> T \<or> PNeg A \<in> T) \<and>
    (\<forall>A. pH_set_derivable \<Sigma> [] T A \<longrightarrow> A \<in> T) \<and>
    (\<forall>\<sigma> A. PExists \<sigma> A \<in> T \<longrightarrow>
      (\<exists>c \<in> \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T))"

lemma pH_closed_Henkin_typed:
  assumes henkin: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_typed_theory \<Sigma> [] T"
  by (rule conjunct1[OF henkin[unfolded pH_closed_Henkin_theory_def]])

lemma pH_closed_Henkin_consistent:
  assumes henkin: "pH_closed_Henkin_theory \<Sigma> T"
  shows "pH_consistent \<Sigma> [] T"
  by (rule conjunct1[OF conjunct2[OF henkin[unfolded pH_closed_Henkin_theory_def]]])

lemma pH_closed_Henkin_decides:
  assumes henkin: "pH_closed_Henkin_theory \<Sigma> T" and lang: "pterm_in_language \<Sigma> [] A Prop"
  shows "A \<in> T \<or> PNeg A \<in> T"
proof -
  note parts = henkin[unfolded pH_closed_Henkin_theory_def]
  have decisions: "\<forall>A. pterm_in_language \<Sigma> [] A Prop \<longrightarrow> A \<in> T \<or> PNeg A \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF parts]]])
  show ?thesis by (rule mp[OF spec[OF decisions] lang])
qed

lemma pH_closed_Henkin_closed:
  assumes henkin: "pH_closed_Henkin_theory \<Sigma> T" and d: "pH_set_derivable \<Sigma> [] T A"
  shows "A \<in> T"
proof -
  note parts = henkin[unfolded pH_closed_Henkin_theory_def]
  have closed: "\<forall>A. pH_set_derivable \<Sigma> [] T A \<longrightarrow> A \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF parts]]]])
  show ?thesis by (rule mp[OF spec[OF closed] d])
qed

lemma pH_closed_Henkin_witness:
  assumes henkin: "pH_closed_Henkin_theory \<Sigma> T" and member: "PExists \<sigma> A \<in> T"
  shows "\<exists>c \<in> \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T"
proof -
  note parts = henkin[unfolded pH_closed_Henkin_theory_def]
  have witnesses: "\<forall>\<sigma> A. PExists \<sigma> A \<in> T \<longrightarrow>
    (\<exists>c \<in> \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T)"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF parts]]]])
  have at_type: "\<forall>A. PExists \<sigma> A \<in> T \<longrightarrow>
    (\<exists>c \<in> \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T)"
    by (rule spec[OF witnesses])
  show ?thesis by (rule mp[OF spec[OF at_type] member])
qed

subsection \<open>The embedded base and all witness axioms are typed and consistent\<close>

lemma phenkin_embedded_typed_theory:
  assumes typed: "pH_typed_theory \<Sigma> [] S"
  shows "pH_typed_theory (phenkin_full_signature \<Sigma>) [] (image phenkin_full_embed S)"
proof (unfold pH_typed_theory_def, intro ballI)
  fix B
  assume member: "B \<in> image phenkin_full_embed S"
  from member obtain A where B: "B = phenkin_full_embed A" and A: "A \<in> S" by (elim imageE)
  note parts = bspec[OF typed[unfolded pH_typed_theory_def] A]
  have ty: "has_ptype [] (phenkin_full_embed A) Prop"
    by (rule phenkin_full_embed_type[OF conjunct1[OF parts]])
  have sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_embed A)"
    using conjunct2[OF parts] by (simp only: phenkin_full_embed_signature)
  show "has_ptype [] B Prop \<and> pterm_in_signature (phenkin_full_signature \<Sigma>) B"
    unfolding B by (rule conjI[OF ty sig])
qed

lemma phenkin_full_base_typed:
  assumes typed: "pH_typed_theory \<Sigma> [] S"
  shows "pH_typed_theory (phenkin_full_signature \<Sigma>) []
    (image phenkin_full_embed S \<union> phenkin_all_witness_axioms \<Sigma>)"
proof -
  have admitted: "phenkin_witness_indices \<Sigma> \<subseteq> phenkin_witness_indices \<Sigma>"
    by (rule subset_refl)
  have combined: "pH_typed_theory (phenkin_full_signature \<Sigma>) []
    (image phenkin_full_embed S \<union> image phenkin_index_axiom (phenkin_witness_indices \<Sigma>))"
    by (rule phenkin_axioms_typed[OF phenkin_embedded_typed_theory[OF typed] admitted])
  show ?thesis using combined by (simp only: phenkin_all_witness_axioms_def)
qed

lemma phenkin_full_base_consistent:
  assumes typed: "pH_typed_theory \<Sigma> [] S" and con: "pH_consistent \<Sigma> [] S"
  shows "pH_consistent (phenkin_full_signature \<Sigma>) []
    (image phenkin_full_embed S \<union> phenkin_all_witness_axioms \<Sigma>)"
proof -
  have embedded: "pH_consistent (phenkin_full_signature \<Sigma>) [] (image phenkin_full_embed S)"
    by (rule phenkin_full_consistency_preserved[OF typed con])
  show ?thesis by (rule phenkin_embedded_all_witness_consistency[OF typed embedded])
qed

lemma pH_typed_member_derivable:
  assumes typed: "pH_typed_theory \<Sigma> [] T" and member: "A \<in> T"
  shows "pH_set_derivable \<Sigma> [] T A"
proof -
  note parts = bspec[OF typed[unfolded pH_typed_theory_def] member]
  show ?thesis by (rule pH_set_Assumption[OF member conjunct1[OF parts] conjunct2[OF parts]])
qed

subsection \<open>Available witness axioms become actual Henkin instances\<close>

lemma phenkin_closed_extension_has_witnesses:
  assumes typed: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] T"
    and all_axioms: "phenkin_all_witness_axioms \<Sigma> \<subseteq> T"
    and closed: "\<And>B. pH_set_derivable (phenkin_full_signature \<Sigma>) [] T B \<Longrightarrow> B \<in> T"
    and existential: "PExists \<sigma> A \<in> T"
  shows "\<exists>c \<in> phenkin_full_signature \<Sigma> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T"
proof -
  note parts = bspec[OF typed[unfolded pH_typed_theory_def] existential]
  have body: "has_ptype [\<sigma>] A Prop"
    by (rule conjunct2[OF iffD1[OF ptype_exists_iff conjunct1[OF parts]]])
  have sigA: "pterm_in_signature (phenkin_full_signature \<Sigma>) A"
    using conjunct2[OF parts] by (simp only: pterm_in_signature.simps)
  have index: "(\<sigma>, A) \<in> phenkin_witness_indices \<Sigma>"
    unfolding phenkin_witness_indices_def
    by (simp only: mem_Collect_eq fst_conv snd_conv; rule conjI[OF body sigA])
  have in_axioms: "phenkin_index_axiom (\<sigma>, A) \<in> phenkin_all_witness_axioms \<Sigma>"
    unfolding phenkin_all_witness_axioms_def by (rule imageI[OF index])
  have axiom_member: "phenkin_full_witness_axiom \<sigma> A \<in> T"
    using subsetD[OF all_axioms in_axioms]
    by (simp only: phenkin_index_axiom_def fst_conv snd_conv)
  have local_axiom: "pH_set_derivable (phenkin_full_signature \<Sigma>) [] T
    (PImp (PExists \<sigma> A) (psubst0 (phenkin_full_witness \<sigma> A) A))"
    using pH_typed_member_derivable[OF typed axiom_member]
    by (simp only: phenkin_full_witness_axiom_def)
  have local_exists: "pH_set_derivable (phenkin_full_signature \<Sigma>) [] T (PExists \<sigma> A)"
    by (rule pH_typed_member_derivable[OF typed existential])
  have instance_derived: "pH_set_derivable (phenkin_full_signature \<Sigma>) [] T
    (psubst0 (phenkin_full_witness \<sigma> A) A)"
    by (rule pH_set_MP[OF local_exists local_axiom])
  have instance_member: "psubst0 (PConst (PFWitness \<sigma> A) \<sigma>) A \<in> T"
    using closed[OF instance_derived] by (simp only: phenkin_full_witness_def)
  have witness_sig: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_witness \<sigma> A)"
    by (rule phenkin_full_witness_signature[OF body sigA])
  have declared: "PFWitness \<sigma> A \<in> phenkin_full_signature \<Sigma> \<sigma>"
    using witness_sig by (simp only: phenkin_full_witness_def pterm_in_signature.simps)
  show ?thesis
  proof (rule bexI[where x="PFWitness \<sigma> A" and A="phenkin_full_signature \<Sigma> \<sigma>"
      and P="\<lambda>c. psubst0 (PConst c \<sigma>) A \<in> T"])
    show "psubst0 (PConst (PFWitness \<sigma> A) \<sigma>) A \<in> T" by (rule instance_member)
    show "PFWitness \<sigma> A \<in> phenkin_full_signature \<Sigma> \<sigma>" by (rule declared)
  qed
qed

subsection \<open>Zorn completion of the consistent witness-axiom base\<close>

theorem phenkin_arbitrary_Henkin_extension:
  assumes typed: "pH_typed_theory \<Sigma> [] S" and con: "pH_consistent \<Sigma> [] S"
  obtains T where "image phenkin_full_embed S \<subseteq> T"
    and "phenkin_all_witness_axioms \<Sigma> \<subseteq> T"
    and "pH_closed_Henkin_theory (phenkin_full_signature \<Sigma>) T"
proof -
  let ?B = "image phenkin_full_embed S \<union> phenkin_all_witness_axioms \<Sigma>"
  let ?\<Omega> = "phenkin_full_signature \<Sigma>"
  have base_typed: "pH_typed_theory ?\<Omega> [] ?B" by (rule phenkin_full_base_typed[OF typed])
  have base_con: "pH_consistent ?\<Omega> [] ?B" by (rule phenkin_full_base_consistent[OF typed con])
  obtain T where maximal: "pH_maximal_extension ?\<Omega> [] ?B T"
    by (rule pH_maximal_extension_exists[OF base_typed base_con])
  note parts = maximal[unfolded pH_maximal_extension_def]
  have base_subset: "?B \<subseteq> T" by (rule conjunct1[OF parts])
  have typed_T: "pH_typed_theory ?\<Omega> [] T" by (rule conjunct1[OF conjunct2[OF parts]])
  have con_T: "pH_consistent ?\<Omega> [] T" by (rule conjunct1[OF conjunct2[OF conjunct2[OF parts]]])
  have old_subset: "image phenkin_full_embed S \<subseteq> T"
    by (rule subset_trans[OF Un_upper1 base_subset])
  have axioms_subset: "phenkin_all_witness_axioms \<Sigma> \<subseteq> T"
    by (rule subset_trans[OF Un_upper2 base_subset])
  have closed: "B \<in> T" if d: "pH_set_derivable ?\<Omega> [] T B" for B
    by (rule pH_maximal_extension_closed[OF maximal d])
  have decisions: "\<forall>A. pterm_in_language ?\<Omega> [] A Prop \<longrightarrow> A \<in> T \<or> PNeg A \<in> T"
  proof (intro allI impI)
    fix A assume lang: "pterm_in_language ?\<Omega> [] A Prop"
    note data = lang[unfolded pterm_in_language_def]
    show "A \<in> T \<or> PNeg A \<in> T"
      by (rule pH_maximal_extension_decides[OF maximal conjunct1[OF data] conjunct2[OF data]])
  qed
  have closure: "\<forall>A. pH_set_derivable ?\<Omega> [] T A \<longrightarrow> A \<in> T"
    by (intro allI impI) (rule closed, assumption)
  have witnesses: "\<forall>\<sigma> A. PExists \<sigma> A \<in> T \<longrightarrow>
    (\<exists>c \<in> ?\<Omega> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T)"
  proof (intro allI impI)
    fix \<sigma> A assume member: "PExists \<sigma> A \<in> T"
    show "\<exists>c \<in> ?\<Omega> \<sigma>. psubst0 (PConst c \<sigma>) A \<in> T"
      by (rule phenkin_closed_extension_has_witnesses[OF typed_T axioms_subset closed member])
  qed
  have henkin: "pH_closed_Henkin_theory ?\<Omega> T"
    unfolding pH_closed_Henkin_theory_def
    by (rule conjI[OF typed_T conjI[OF con_T conjI[OF decisions conjI[OF closure witnesses]]]])
  show thesis by (rule that[OF old_subset axioms_subset henkin])
qed

text \<open>
  Every existential sentence of the final language receives a witness in T,
  including sentences containing earlier witness labels.  T is not obtained
  by assuming an old-language witness stock or enumerating an uncountable
  language.  Signature conservativity, finite-rank witness elimination,
  finite proof support, and Zorn maximality have distinct proved roles.
\<close>

end
