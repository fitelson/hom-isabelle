theory Bacon_Parametric_Declared_Signature_Coding
  imports Bacon_Parametric_Countable_Coding
begin

section \<open>Coding a countable declared signature in an arbitrary name type\<close>

text \<open>
  Let C = ⋃σΣσ be countable, with no restriction on the ambient type of
  names.  Choose an injection e:C → ℕ, put Σᵉσ = e[Σσ], and let d be
  its inverse on e[C].  Then d(e(A)) = A for A ∈ ℒ(Σ).  Translating H
  proofs along d reflects derivability and preserves consistency of e(S).
  Source role: the countable-signature qualification in Bacon–Dorr,
  Theorem 3.2, pp.44–45; coding is a change of names, not a new logical rule.

  Isabelle representation: countability is a set predicate on the union
  of the declared name sets.  The code is injective only on that union;
  inv_into and every inverse theorem retain their signature guard.
  No countable class constraint is put on the original name type.
  This leaf proves syntactic reflection, not semantic model existence.
\<close>

locale pH_countable_signature =
  fixes signature :: "'c psignature"
  assumes declared_countable: "countable (\<Union>\<sigma>. signature \<sigma>)"
begin

definition pHdecl_names :: "'c set" where
  "pHdecl_names = (\<Union>\<sigma>. signature \<sigma>)"

definition pHdecl_code :: "'c \<Rightarrow> nat" where
  "pHdecl_code = (SOME f. inj_on f pHdecl_names)"

definition pHdecl_decode :: "nat \<Rightarrow> 'c" where
  "pHdecl_decode = inv_into pHdecl_names pHdecl_code"

definition pHdecl_signature :: "nat psignature" where
  "pHdecl_signature \<sigma> = pHdecl_code ` signature \<sigma>"

lemma pHdecl_namesI: "c \<in> signature \<sigma> \<Longrightarrow> c \<in> pHdecl_names"
  unfolding pHdecl_names_def by (rule UN_I[where a=\<sigma>]) (rule UNIV_I, assumption)

lemma pHdecl_code_injective: "inj_on pHdecl_code pHdecl_names"
proof -
  have countable: "countable pHdecl_names" using declared_countable unfolding pHdecl_names_def .
  obtain f :: "'c \<Rightarrow> nat" where injective: "inj_on f pHdecl_names" by (rule countableE[OF countable])
  have exists: "\<exists>f :: 'c \<Rightarrow> nat. inj_on f pHdecl_names"
    by (rule exI[where x=f], rule injective)
  show ?thesis unfolding pHdecl_code_def by (rule someI_ex[OF exists])
qed

lemma pHdecl_decode_code:
  assumes declared: "c \<in> signature \<sigma>"
  shows "pHdecl_decode (pHdecl_code c) = c"
  unfolding pHdecl_decode_def by (rule inv_into_f_f[OF pHdecl_code_injective pHdecl_namesI[OF declared]])

lemma pHdecl_encode_name:
  "c \<in> signature \<sigma> \<Longrightarrow> pHdecl_code c \<in> pHdecl_signature \<sigma>"
  unfolding pHdecl_signature_def by (rule imageI)

lemma pHdecl_decode_name:
  assumes declared: "n \<in> pHdecl_signature \<sigma>"
  shows "pHdecl_decode n \<in> signature \<sigma>"
proof -
  have image: "n \<in> pHdecl_code ` signature \<sigma>" using declared unfolding pHdecl_signature_def .
  from image obtain c where eq: "n = pHdecl_code c" and member: "c \<in> signature \<sigma>" by (elim imageE)
  show ?thesis by (simp only: eq pHdecl_decode_code[OF member] member)
qed

lemma pHdecl_term_roundtrip:
  "pterm_in_signature signature A \<Longrightarrow>
    phenkin_map pHdecl_decode (phenkin_map pHdecl_code A) = A"
  by (induction A) (simp_all add: pHdecl_decode_code)

lemma pHdecl_encode_signature:
  "pterm_in_signature signature A \<Longrightarrow> pterm_in_signature pHdecl_signature (phenkin_map pHdecl_code A)"
  by (rule phenkin_map_signature, assumption, rule pHdecl_encode_name, assumption)

lemma pHdecl_decode_signature:
  "pterm_in_signature pHdecl_signature A \<Longrightarrow> pterm_in_signature signature (phenkin_map pHdecl_decode A)"
  by (rule phenkin_map_signature, assumption, rule pHdecl_decode_name, assumption)

subsection \<open>Proof reflection is guarded by the original signature\<close>

lemma pHdecl_proves_reflect:
  assumes sig: "pterm_in_signature signature A"
    and encoded: "pH_proves pHdecl_signature \<Gamma> (phenkin_map pHdecl_code A)"
  shows "pH_proves signature \<Gamma> A"
proof -
  have decoded: "pH_proves signature \<Gamma> (phenkin_map pHdecl_decode (phenkin_map pHdecl_code A))"
    by (rule phenkin_map_proves[where k=pHdecl_decode, OF encoded pHdecl_decode_name])
  show ?thesis using decoded by (simp only: pHdecl_term_roundtrip[OF sig])
qed

lemma pHdecl_proves_iff:
  assumes sig: "pterm_in_signature signature A"
  shows "pH_proves pHdecl_signature \<Gamma> (phenkin_map pHdecl_code A) \<longleftrightarrow> pH_proves signature \<Gamma> A"
proof
  assume encoded: "pH_proves pHdecl_signature \<Gamma> (phenkin_map pHdecl_code A)"
  show "pH_proves signature \<Gamma> A" by (rule pHdecl_proves_reflect[OF sig encoded])
next
  assume original: "pH_proves signature \<Gamma> A"
  show "pH_proves pHdecl_signature \<Gamma> (phenkin_map pHdecl_code A)"
    by (rule phenkin_map_proves[where k=pHdecl_code, OF original pHdecl_encode_name])
qed

lemma pHdecl_member_signature:
  assumes typed: "pH_typed_theory signature \<Gamma> S" and member: "A \<in> S"
  shows "pterm_in_signature signature A"
proof -
  have all: "\<forall>B \<in> S. has_ptype \<Gamma> B Prop \<and> pterm_in_signature signature B"
    using typed unfolding pH_typed_theory_def .
  show ?thesis by (rule conjunct2[OF bspec[OF all member]])
qed

lemma pHdecl_set_roundtrip:
  assumes typed: "pH_typed_theory signature \<Gamma> S"
  shows "phenkin_map pHdecl_decode ` (phenkin_map pHdecl_code ` S) = S"
proof -
  have roundtrip: "phenkin_map pHdecl_decode (phenkin_map pHdecl_code A) = id A"
    if member: "A \<in> S" for A
    by (simp only: pHdecl_term_roundtrip[OF pHdecl_member_signature[OF typed member]] id_apply)
  have "phenkin_map pHdecl_decode ` (phenkin_map pHdecl_code ` S) =
      (\<lambda>A. phenkin_map pHdecl_decode (phenkin_map pHdecl_code A)) ` S"
    by (simp only: image_image)
  also have "... = id ` S" by (rule image_cong[OF refl roundtrip])
  also have "... = S" by simp
  finally show ?thesis .
qed

lemma pHdecl_set_reflect:
  assumes typed: "pH_typed_theory signature \<Gamma> S" and sig: "pterm_in_signature signature A"
    and encoded: "pH_set_derivable pHdecl_signature \<Gamma> (phenkin_map pHdecl_code ` S) (phenkin_map pHdecl_code A)"
  shows "pH_set_derivable signature \<Gamma> S A"
proof -
  have decoded: "pH_set_derivable signature \<Gamma>
      (phenkin_map pHdecl_decode ` (phenkin_map pHdecl_code ` S))
      (phenkin_map pHdecl_decode (phenkin_map pHdecl_code A))"
    by (rule pH_set_map[where k=pHdecl_decode, OF encoded pHdecl_decode_name])
  show ?thesis using decoded by (simp only: pHdecl_set_roundtrip[OF typed] pHdecl_term_roundtrip[OF sig])
qed

lemma pHdecl_encoded_typed:
  assumes typed: "pH_typed_theory signature \<Gamma> S"
  shows "pH_typed_theory pHdecl_signature \<Gamma> (phenkin_map pHdecl_code ` S)"
proof (unfold pH_typed_theory_def, rule ballI)
  fix B
  assume member: "B \<in> phenkin_map pHdecl_code ` S"
  from member obtain A where eq: "B = phenkin_map pHdecl_code A" and original: "A \<in> S" by (elim imageE)
  have all: "\<forall>A \<in> S. has_ptype \<Gamma> A Prop \<and> pterm_in_signature signature A"
    using typed unfolding pH_typed_theory_def .
  have parts: "has_ptype \<Gamma> A Prop \<and> pterm_in_signature signature A" by (rule bspec[OF all original])
  have at: "has_ptype \<Gamma> (phenkin_map pHdecl_code A) Prop"
    by (rule phenkin_map_type[OF conjunct1[OF parts]])
  have asig: "pterm_in_signature pHdecl_signature (phenkin_map pHdecl_code A)"
    by (rule pHdecl_encode_signature[OF conjunct2[OF parts]])
  show "has_ptype \<Gamma> B Prop \<and> pterm_in_signature pHdecl_signature B"
    unfolding eq by (rule conjI[OF at asig])
qed

theorem pHdecl_encoded_consistent:
  assumes typed: "pH_typed_theory signature \<Gamma> S" and consistent: "pH_consistent signature \<Gamma> S"
  shows "pH_consistent pHdecl_signature \<Gamma> (phenkin_map pHdecl_code ` S)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable pHdecl_signature \<Gamma> (phenkin_map pHdecl_code ` S) PObjFalse"
  have decoded: "pH_set_derivable signature \<Gamma>
      (phenkin_map pHdecl_decode ` (phenkin_map pHdecl_code ` S)) (phenkin_map pHdecl_decode PObjFalse)"
    by (rule pH_set_map[where k=pHdecl_decode, OF bad pHdecl_decode_name])
  have contradiction: "pH_set_derivable signature \<Gamma> S PObjFalse"
    using decoded by (simp only: pHdecl_set_roundtrip[OF typed] pH_name_map_PObjFalse)
  have no_contradiction: "\<not> pH_set_derivable signature \<Gamma> S PObjFalse"
    using consistent unfolding pH_consistent_def .
  show False by (rule notE[OF no_contradiction contradiction])
qed

end
end
