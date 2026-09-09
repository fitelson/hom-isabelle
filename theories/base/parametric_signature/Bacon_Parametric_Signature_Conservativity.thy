theory Bacon_Parametric_Signature_Conservativity
  imports Bacon_Parametric_Finite_Signature_Support
    Bacon_Parametric_Henkin_Names
    Bacon_Parametric_Local_Quantifiers
    Bacon_Parametric_Existential_Witness_Theorem
begin

section \<open>Syntactic conservativity of the disjoint witness signature\<close>

text \<open>
  For old-language S and A, a proof ι(S) ⊢H ι(A) in the full witness
  signature yields S ⊢H A in the original signature.  A finite derivation
  uses finitely many auxiliary names.  We replace one such c:σ by an
  eigenvariable, remove its declaration, and descend using Inst and
  ⊢H ∃v:σ(v =σ v).  No old closed term of type σ is assumed.

  Isabelle representation: the helper theories provide cross-signature
  constant substitution and finite signature support.  This file removes
  the auxiliary names and only then projects the old-name image back.
  Status: proof reflection and preservation of consistency by the embedding;
  no semantic completeness theorem is used.
\<close>

subsection \<open>An unused context slot can be removed\<close>

lemma pH_set_imp_of_right:
  assumes P: "pterm_in_language \<Sigma> \<Gamma> P Prop" and d: "pH_set_derivable \<Sigma> \<Gamma> S Q"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (PImp P Q)"
proof -
  note parts = P[unfolded pterm_in_language_def]
  obtain L where support: "set L \<subseteq> S" and local_d: "pH_derivable \<Sigma> \<Gamma> L Q"
    using d unfolding pH_set_derivable_def by (elim exE conjE)
  have result: "pH_derivable \<Sigma> \<Gamma> L (PImp P Q)"
    by (rule pH_local_imp_of_right[OF conjunct1[OF parts] conjunct2[OF parts] local_d])
  show ?thesis unfolding pH_set_derivable_def by (rule exI[where x=L], rule conjI[OF support result])
qed

lemma pH_remove_unused_slot:
  fixes \<Sigma> :: "'a psignature" and S :: "'a pterm set" and A :: "'a pterm"
  assumes typed_S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and d: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
proof -
  let ?R = "PEq \<sigma> (PVar 0) (PVar 0) :: 'a pterm"
  have R_type: "has_ptype (\<sigma> # \<Gamma>) ?R Prop"
    by (intro has_ptype.PEq has_ptype.PVar) simp_all
  have R_sig: "pterm_in_signature \<Sigma> ?R"
    by (simp add: pterm_in_signature.simps)
  have R: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) ?R Prop"
    unfolding pterm_in_language_def
    by (rule conjI[OF R_type R_sig])
  have implication: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (PImp ?R (pshift A))"
    by (rule pH_set_imp_of_right[OF R d])
  have descended: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PExists \<sigma> ?R) A)"
    by (rule pH_set_Inst[OF typed_S R A implication])
  have existence: "pH_set_derivable \<Sigma> \<Gamma> S (PExists \<sigma> ?R)"
    by (rule pH_set_Theorem[OF pH_all_type_existence])
  show ?thesis by (rule pH_set_MP[OF existence descended])
qed

subsection \<open>Remove one typed name without a closed replacement term\<close>

lemma pH_remove_fresh_declaration:
  fixes \<Sigma> \<Omega> :: "'a psignature" and S :: "'a pterm set" and A :: "'a pterm" and c :: 'a
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A" and typed_S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and fresh_S: "\<And>B. B \<in> S \<Longrightarrow> c \<notin> phenkin_names B"
    and fresh_A: "c \<notin> phenkin_names A"
    and names: "\<And>e \<tau>. e \<in> \<Sigma> \<tau> \<Longrightarrow> e \<noteq> c \<or> \<tau> \<noteq> \<sigma> \<Longrightarrow> e \<in> \<Omega> \<tau>"
  shows "pH_set_derivable \<Omega> \<Gamma> S A"
proof -
  have retained: "pterm_in_signature \<Omega> B"
    if sig: "pterm_in_signature \<Sigma> B" and fresh: "c \<notin> phenkin_names B" for B
  proof -
    have zero_sig: "pterm_in_signature \<Omega> (PVar 0)" by simp
    have replaced: "pterm_in_signature \<Omega> (pconst_subst c \<sigma> (PVar 0) B)"
      by (rule pconst_subst_signature_into[OF sig zero_sig names])
    show ?thesis using replaced by (simp only: pconst_subst_fresh[OF fresh])
  qed
  have target_S: "pH_typed_theory \<Omega> \<Gamma> S"
  proof (unfold pH_typed_theory_def, intro ballI)
    fix B assume member: "B \<in> S"
    note parts = bspec[OF typed_S[unfolded pH_typed_theory_def] member]
    have sig: "pterm_in_signature \<Omega> B" by (rule retained[OF conjunct2[OF parts] fresh_S[OF member]])
    show "has_ptype \<Gamma> B Prop \<and> pterm_in_signature \<Omega> B" by (rule conjI[OF conjunct1[OF parts] sig])
  qed
  have target_A: "pterm_in_language \<Omega> \<Gamma> A Prop"
    unfolding pterm_in_language_def
    by (rule conjI[OF pH_set_formula[OF d] retained[OF pH_set_in_signature[OF d] fresh_A]])
  have shifted_raw: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
    (image (prename Suc) S) (prename Suc A)"
  proof (rule pH_set_prename[where r=Suc and \<Delta>="\<sigma> # \<Gamma>", OF d])
    fix n \<tau>
    assume index: "lookup \<Gamma> n = Some \<tau>"
    show "lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<tau>" using index by simp
  qed
  have shift_function: "(pshift :: 'a pterm \<Rightarrow> 'a pterm) = prename Suc"
    by (rule ext) (simp only: pshift_def)
  have shifted: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
    using shifted_raw by (simp only: shift_function)
  have zero_type: "has_ptype (\<sigma> # \<Gamma>) (PVar 0 :: 'a pterm) \<sigma>"
    by (rule has_ptype.PVar) simp
  have zero_sig: "pterm_in_signature \<Omega> (PVar 0)" by simp
  have replaced: "pH_set_derivable \<Omega> (\<sigma> # \<Gamma>)
    (image (pconst_subst c \<sigma> (PVar 0)) (image pshift S))
    (pconst_subst c \<sigma> (PVar 0) (pshift A))"
    by (rule pH_set_pconst_into[OF shifted zero_type zero_sig names])
  have fixed: "pconst_subst c \<sigma> (PVar 0) (pshift B) = pshift B"
    if "B \<in> S" for B
    by (rule pconst_subst_fresh) (simp only: phenkin_names_pshift; rule fresh_S[OF that])
  have fixed_image: "image (pconst_subst c \<sigma> (PVar 0)) (image pshift S) = image pshift S"
    by (simp only: image_image) (rule image_cong[OF refl], rule fixed)
  have fixed_A: "pconst_subst c \<sigma> (PVar 0) (pshift A) = pshift A"
    by (rule pconst_subst_fresh) (simp only: phenkin_names_pshift; rule fresh_A)
  have eigen: "pH_set_derivable \<Omega> (\<sigma> # \<Gamma>) (image pshift S) (pshift A)"
    using replaced by (simp only: fixed_image fixed_A)
  show ?thesis by (rule pH_remove_unused_slot[OF target_S target_A eigen])
qed

subsection \<open>Finite auxiliary stocks above the complete old signature\<close>

definition phenkin_old_signature :: "'c psignature \<Rightarrow> 'c phenkin_full_name psignature" where
  "phenkin_old_signature \<Sigma> \<tau> = image PFOriginal (\<Sigma> \<tau>)"

definition phenkin_hybrid_signature ::
    "'c psignature \<Rightarrow> 'c phenkin_full_name set \<Rightarrow> 'c phenkin_full_name psignature" where
  "phenkin_hybrid_signature \<Sigma> K \<tau> =
    phenkin_old_signature \<Sigma> \<tau> \<union> (phenkin_full_signature \<Sigma> \<tau> \<inter> K)"

lemma phenkin_hybrid_original:
  "PFOriginal c \<in> phenkin_hybrid_signature \<Sigma> K \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
  by (auto simp: phenkin_hybrid_signature_def phenkin_old_signature_def phenkin_full_original_membership)

lemma phenkin_hybrid_empty:
  "phenkin_hybrid_signature \<Sigma> {} = phenkin_old_signature \<Sigma>"
  by (rule ext) (simp only: phenkin_hybrid_signature_def Int_empty_right Un_empty_right)

lemma phenkin_hybrid_insert_original:
  "phenkin_hybrid_signature \<Sigma> (insert (PFOriginal c) K) = phenkin_hybrid_signature \<Sigma> K"
  by (rule ext) (auto simp: phenkin_hybrid_signature_def phenkin_old_signature_def phenkin_full_original_membership)

lemma phenkin_hybrid_remove_witness:
  assumes declared: "e \<in> phenkin_hybrid_signature \<Sigma> (insert (PFWitness \<sigma> B) K) \<tau>"
    and other: "e \<noteq> PFWitness \<sigma> B \<or> \<tau> \<noteq> \<sigma>"
  shows "e \<in> phenkin_hybrid_signature \<Sigma> K \<tau>"
  using declared other
  by (auto simp: phenkin_hybrid_signature_def phenkin_old_signature_def phenkin_full_witness_membership)

lemma phenkin_hybrid_embed_signature:
  assumes sig: "pterm_in_signature \<Sigma> A"
  shows "pterm_in_signature (phenkin_hybrid_signature \<Sigma> K) (phenkin_full_embed A)"
  unfolding phenkin_full_embed_def
proof (rule phenkin_map_signature[OF sig])
  fix c \<tau> assume declared: "c \<in> \<Sigma> \<tau>"
  have membership: "PFOriginal c \<in> phenkin_hybrid_signature \<Sigma> K \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
    by (rule phenkin_hybrid_original)
  show "PFOriginal c \<in> phenkin_hybrid_signature \<Sigma> K \<tau>" by (rule iffD2[OF membership declared])
qed

lemma phenkin_hybrid_typed_theory:
  assumes typed: "pH_typed_theory \<Sigma> \<Gamma> S"
  shows "pH_typed_theory (phenkin_hybrid_signature \<Sigma> K) \<Gamma> (image phenkin_full_embed S)"
proof (unfold pH_typed_theory_def, intro ballI)
  fix A assume member: "A \<in> image phenkin_full_embed S"
  from member obtain B where eq: "A = phenkin_full_embed B" and B: "B \<in> S" by (elim imageE)
  note parts = bspec[OF typed[unfolded pH_typed_theory_def] B]
  have ty: "has_ptype \<Gamma> (phenkin_full_embed B) Prop" by (rule phenkin_full_embed_type[OF conjunct1[OF parts]])
  have sig: "pterm_in_signature (phenkin_hybrid_signature \<Sigma> K) (phenkin_full_embed B)"
    by (rule phenkin_hybrid_embed_signature[OF conjunct2[OF parts]])
  show "has_ptype \<Gamma> A Prop \<and> pterm_in_signature (phenkin_hybrid_signature \<Sigma> K) A"
    unfolding eq by (rule conjI[OF ty sig])
qed

lemma phenkin_hybrid_reflection:
  assumes finite: "finite K" and typed: "pH_typed_theory \<Sigma> \<Gamma> S"
    and d: "pH_set_derivable (phenkin_hybrid_signature \<Sigma> K) \<Gamma>
      (image phenkin_full_embed S) (phenkin_full_embed A)"
  shows "pH_set_derivable (phenkin_old_signature \<Sigma>) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed A)"
  using finite d
proof (induction K rule: finite_induct)
  case empty
  show ?case using empty.prems by (simp only: phenkin_hybrid_empty)
next
  case (insert n K)
  have reduced: "pH_set_derivable (phenkin_hybrid_signature \<Sigma> K) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed A)"
  proof (cases n)
    case (PFOriginal c)
    show ?thesis using insert.prems by (simp only: PFOriginal phenkin_hybrid_insert_original)
  next
    case (PFWitness \<sigma> B)
    have source: "pH_set_derivable (phenkin_hybrid_signature \<Sigma> (insert (PFWitness \<sigma> B) K)) \<Gamma>
      (image phenkin_full_embed S) (phenkin_full_embed A)" using insert.prems by (simp only: PFWitness)
    have source_typed: "pH_typed_theory (phenkin_hybrid_signature \<Sigma> (insert (PFWitness \<sigma> B) K)) \<Gamma>
      (image phenkin_full_embed S)" by (rule phenkin_hybrid_typed_theory[OF typed])
    have fresh: "PFWitness \<sigma> B \<notin> phenkin_names C" if "C \<in> image phenkin_full_embed S" for C
    proof -
      from that obtain D where C: "C = phenkin_full_embed D" and "D \<in> S" by (elim imageE)
      show ?thesis by (simp add: C phenkin_full_witness_fresh_original)
    qed
    show ?thesis
    proof (rule pH_remove_fresh_declaration[where c="PFWitness \<sigma> B" and \<sigma>=\<sigma>,
        OF source source_typed])
      fix C
      assume member: "C \<in> image phenkin_full_embed S"
      show "PFWitness \<sigma> B \<notin> phenkin_names C" by (rule fresh[OF member])
    next
      show "PFWitness \<sigma> B \<notin> phenkin_names (phenkin_full_embed A)"
        by (rule phenkin_full_witness_fresh_original)
    next
      fix e \<tau>
      assume declared:
        "e \<in> phenkin_hybrid_signature \<Sigma> (insert (PFWitness \<sigma> B) K) \<tau>"
        and other: "e \<noteq> PFWitness \<sigma> B \<or> \<tau> \<noteq> \<sigma>"
      show "e \<in> phenkin_hybrid_signature \<Sigma> K \<tau>"
      proof (cases e)
        case (PFOriginal c)
        have original_member:
          "PFOriginal c \<in> phenkin_hybrid_signature \<Sigma> (insert (PFWitness \<sigma> B) K) \<tau>"
          using declared by (simp only: PFOriginal)
        have old_name: "c \<in> \<Sigma> \<tau>"
          by (rule iffD1[OF phenkin_hybrid_original[where \<Sigma>=\<Sigma>
            and K="insert (PFWitness \<sigma> B) K" and c=c and \<tau>=\<tau>] original_member])
        have retained: "PFOriginal c \<in> phenkin_hybrid_signature \<Sigma> K \<tau>"
          by (rule iffD2[OF phenkin_hybrid_original[where \<Sigma>=\<Sigma>
            and K=K and c=c and \<tau>=\<tau>] old_name])
        show ?thesis using retained by (simp only: PFOriginal)
      next
        case (PFWitness \<rho> C)
        have witness_parts:
          "PFWitness \<rho> C \<in> phenkin_full_signature \<Sigma> \<tau> \<and>
            PFWitness \<rho> C \<in> insert (PFWitness \<sigma> B) K"
          using declared
          by (simp add: PFWitness phenkin_hybrid_signature_def phenkin_old_signature_def image_iff)
        have full: "e \<in> phenkin_full_signature \<Sigma> \<tau>"
          using conjunct1[OF witness_parts] by (simp only: PFWitness)
        have in_insert: "e \<in> insert (PFWitness \<sigma> B) K"
          using conjunct2[OF witness_parts] by (simp only: PFWitness)
        have not_same: "e \<noteq> PFWitness \<sigma> B"
        proof
          assume same: "e = PFWitness \<sigma> B"
          have named: "PFWitness \<sigma> B \<in> phenkin_full_signature \<Sigma> \<tau>"
            using full by (simp only: same)
          have type_parts: "\<sigma> = \<tau> \<and> has_ptype [\<sigma>] B Prop \<and>
              pterm_in_signature (phenkin_full_signature \<Sigma>) B"
            by (rule iffD1[OF phenkin_full_witness_membership
              [where \<Sigma>=\<Sigma> and \<sigma>=\<sigma> and \<tau>=\<tau> and A=B] named])
          have same_type: "\<tau> = \<sigma>" by (rule sym[OF conjunct1[OF type_parts]])
          show False
          proof (rule disjE[OF other])
            assume distinct_name: "e \<noteq> PFWitness \<sigma> B"
            show False by (rule notE[OF distinct_name same])
          next
            assume distinct_type: "\<tau> \<noteq> \<sigma>"
            show False by (rule notE[OF distinct_type same_type])
          qed
        qed
        have in_K: "e \<in> K" using in_insert not_same by simp
        show ?thesis unfolding phenkin_hybrid_signature_def
          by (rule UnI2, rule IntI[OF full in_K])
      qed
    qed
  qed
  show ?case by (rule insert.IH[OF reduced])
qed

subsection \<open>Projection only after all auxiliary declarations are removed\<close>

lemma phenkin_old_project_proof:
  fixes default :: 'c
  assumes d: "pH_set_derivable (phenkin_old_signature \<Sigma>) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed (A :: 'c pterm))"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
proof -
  have names: "phenkin_full_project default c \<in> \<Sigma> \<tau>"
    if "c \<in> phenkin_old_signature \<Sigma> \<tau>" for c \<tau>
    using that by (auto simp: phenkin_old_signature_def)
  have mapped: "pH_set_derivable \<Sigma> \<Gamma>
    (image (phenkin_map (phenkin_full_project default)) (image phenkin_full_embed S))
    (phenkin_map (phenkin_full_project default) (phenkin_full_embed A))"
    by (rule pH_set_map[OF d names])
  show ?thesis using mapped
    by (simp only: image_image phenkin_full_embed_left_inverse image_ident)
qed

theorem phenkin_full_set_reflection:
  assumes typed: "pH_typed_theory \<Sigma> \<Gamma> S"
    and d: "pH_set_derivable (phenkin_full_signature \<Sigma>) \<Gamma>
      (image phenkin_full_embed S) (phenkin_full_embed (A :: 'c pterm))"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
proof -
  obtain K where K: "finite K" and supported:
    "pH_set_derivable (pH_name_restrict (phenkin_full_signature \<Sigma>) K) \<Gamma>
      (image phenkin_full_embed S) (phenkin_full_embed A)"
    by (rule pH_set_finite_signature_support[OF d])
  have inclusion: "pH_name_restrict (phenkin_full_signature \<Sigma>) K \<tau> \<subseteq> phenkin_hybrid_signature \<Sigma> K \<tau>" for \<tau>
    by (auto simp: pH_name_restrict_def phenkin_hybrid_signature_def)
  have hybrid: "pH_set_derivable (phenkin_hybrid_signature \<Sigma> K) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed A)"
    by (rule pH_set_signature_mono[OF supported inclusion])
  have old: "pH_set_derivable (phenkin_old_signature \<Sigma>) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed A)"
    by (rule phenkin_hybrid_reflection[OF K typed hybrid])
  show ?thesis by (rule phenkin_old_project_proof[OF old])
qed

theorem phenkin_full_theorem_reflection:
  assumes d: "pH_proves (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A)"
  shows "pH_proves \<Sigma> \<Gamma> A"
proof -
  have typed_empty: "pH_typed_theory \<Sigma> \<Gamma> {}" by (simp add: pH_typed_theory_def)
  have local_d: "pH_set_derivable (phenkin_full_signature \<Sigma>) \<Gamma>
    (image phenkin_full_embed {}) (phenkin_full_embed A)"
    by (rule pH_set_Theorem[OF d])
  have reflected: "pH_set_derivable \<Sigma> \<Gamma> {} A"
    by (rule phenkin_full_set_reflection[OF typed_empty local_d])
  obtain L where support: "set L \<subseteq> {}" and proof_L: "pH_derivable \<Sigma> \<Gamma> L A"
    using reflected unfolding pH_set_derivable_def by (elim exE conjE)
  have empty: "L = []" using support by simp
  have proof_empty: "pH_derivable \<Sigma> \<Gamma> [] A" using proof_L by (simp only: empty)
  show ?thesis by (rule pH_local_empty_to_theorem[OF proof_empty])
qed

corollary phenkin_full_theorem_iff:
  "pH_proves (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A) \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> A"
proof
  assume d: "pH_proves (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A)"
  show "pH_proves \<Sigma> \<Gamma> A" by (rule phenkin_full_theorem_reflection[OF d])
next
  assume d: "pH_proves \<Sigma> \<Gamma> A"
  show "pH_proves (phenkin_full_signature \<Sigma>) \<Gamma> (phenkin_full_embed A)"
    by (rule phenkin_full_embed_proves[OF d])
qed

theorem phenkin_full_consistency_preserved:
  assumes typed: "pH_typed_theory \<Sigma> \<Gamma> S" and consistent: "pH_consistent \<Sigma> \<Gamma> (S :: 'c pterm set)"
  shows "pH_consistent (phenkin_full_signature \<Sigma>) \<Gamma> (image phenkin_full_embed S)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable (phenkin_full_signature \<Sigma>) \<Gamma> (image phenkin_full_embed S) PObjFalse"
  have embedded_false: "phenkin_full_embed (PObjFalse :: 'c pterm) = PObjFalse"
    by (simp only: phenkin_full_embed_def pH_name_map_PObjFalse)
  have bad_embedded: "pH_set_derivable (phenkin_full_signature \<Sigma>) \<Gamma>
    (image phenkin_full_embed S) (phenkin_full_embed PObjFalse)"
    using bad by (simp only: embedded_false)
  have original_bad: "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
    by (rule phenkin_full_set_reflection[OF typed bad_embedded])
  show False by (rule notE[OF consistent[unfolded pH_consistent_def] original_bad])
qed

text \<open>
  The projection default is never used on a declared constant: after finite
  elimination, only PFOriginal names remain.  Type Existence, not a presumed
  old closed term, removes each eigenvariable.  No witness axioms have yet
  been added, so this conservativity result does not by itself prove
  consistency of an iterated witness-axiom theory.
\<close>

end
