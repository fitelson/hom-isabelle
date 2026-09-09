theory Bacon_H_BBK_Countable_Coding
  imports Bacon_H_BBK_Canonical_Development.Bacon_H_BBK_Completeness
begin

section \<open>Bacon--Dorr Theorem 3.2: canonical domains in the naturals\<close>

text \<open>
  c(σ,[M]ₜ) = ⟨code(σ), code(rep([M]ₜ))⟩ ∈ ℕ. Bacon–Dorr, Theorem 3.2, pp. 44–45,
  countable-domain refinement.

  Isabelle representation: The implementation uses to_nat, prod_encode, and a chosen
  closed representative. Type tags preserve distinctions between domains.

  Status: Injection is on the union of canonical domains, not on arbitrary ambient
  sets; coding is choice-based, not an equality algorithm.
\<close>

context H_closed_Henkin
begin

definition H_BBK_canonical_universe :: "h_bbk_value set" where
  "H_BBK_canonical_universe = (\<Union>\<sigma>. H_BBK_domain \<sigma>)"

definition H_BBK_nat_code :: "h_bbk_value \<Rightarrow> nat" where
  "H_BBK_nat_code v = prod_encode (to_nat (fst v), to_nat (H_BBK_rep v))"

definition H_BBK_nat_decode :: "nat \<Rightarrow> h_bbk_value" where
  "H_BBK_nat_decode n =
    H_BBK_class (from_nat (fst (prod_decode n))) (from_nat (snd (prod_decode n)))"

definition H_BBK_nat_domain :: "otype \<Rightarrow> nat set" where
  "H_BBK_nat_domain \<sigma> = image H_BBK_nat_code (H_BBK_domain \<sigma>)"

subsection \<open>Typed union and reconstruction\<close>

text \<open>
  c⁻¹(c(a)) = a for a ∈ ⋃σDσ. Bacon–Dorr, Theorem 3.2, pp. 44–45, countable-domain
  refinement.

  Isabelle representation: The representative and type components reconstruct a
  canonical value. No reconstruction theorem is asserted outside this typed union.

  Status: Domain-restricted inverse laws; interpretation transport comes later.
\<close>

lemma H_BBK_canonical_universeI:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "v \<in> H_BBK_canonical_universe"
  unfolding H_BBK_canonical_universe_def
  by (rule UN_I[where a=\<sigma>]) (rule UNIV_I, rule domain)

lemma H_BBK_canonical_universeE:
  assumes universe: "v \<in> H_BBK_canonical_universe"
  obtains \<sigma> where "v \<in> H_BBK_domain \<sigma>"
proof -
  have member: "v \<in> (\<Union>\<sigma>. H_BBK_domain \<sigma>)"
    using universe by (simp only: H_BBK_canonical_universe_def)
  from member show thesis
  proof (rule UN_E)
    fix \<sigma>
    assume "\<sigma> \<in> UNIV" and domain: "v \<in> H_BBK_domain \<sigma>"
    show thesis by (rule that[OF domain])
  qed
qed

lemma H_BBK_nat_decode_code_domain:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_nat_decode (H_BBK_nat_code v) = v"
proof -
  have decoded:
    "H_BBK_nat_decode (H_BBK_nat_code v) = H_BBK_class (fst v) (H_BBK_rep v)"
    by (simp only: H_BBK_nat_decode_def H_BBK_nat_code_def
        prod_encode_inverse fst_conv snd_conv from_nat_to_nat)
  have tag: "fst v = \<sigma>" by (rule H_BBK_domain_tag[OF domain])
  have reconstruction: "H_BBK_class \<sigma> (H_BBK_rep v) = v"
    by (rule H_BBK_rep_reconstruct[OF domain])
  show ?thesis by (simp only: decoded tag reconstruction)
qed

lemma H_BBK_nat_decode_code:
  assumes universe: "v \<in> H_BBK_canonical_universe"
  shows "H_BBK_nat_decode (H_BBK_nat_code v) = v"
proof -
  obtain \<sigma> where domain: "v \<in> H_BBK_domain \<sigma>"
    by (rule H_BBK_canonical_universeE[OF universe])
  show ?thesis by (rule H_BBK_nat_decode_code_domain[OF domain])
qed

subsection \<open>Injection on individual domains and their union\<close>

text \<open>
  a,b ∈ ⋃σDσ and c(a) = c(b) ⇒ a = b. Bacon–Dorr, Theorem 3.2, pp. 44–45,
  countable-domain refinement.

  Isabelle representation: Pair coding first recovers the type tag and then the chosen
  representative; its class recovers the original typed value.

  Status: Injection is proved for each domain and their union, not the entire ambient
  HOL carrier.
\<close>

lemma H_BBK_nat_code_cross_type_injective:
  assumes v: "v \<in> H_BBK_domain \<sigma>" and w: "w \<in> H_BBK_domain \<tau>"
    and codes: "H_BBK_nat_code v = H_BBK_nat_code w"
  shows "v = w"
proof -
  have "v = H_BBK_nat_decode (H_BBK_nat_code v)"
    by (rule sym[OF H_BBK_nat_decode_code_domain[OF v]])
  also have "... = H_BBK_nat_decode (H_BBK_nat_code w)" by (simp only: codes)
  also have "... = w" by (rule H_BBK_nat_decode_code_domain[OF w])
  finally show ?thesis .
qed

lemma H_BBK_nat_code_inj_on_domain:
  "inj_on H_BBK_nat_code (H_BBK_domain \<sigma>)"
proof (rule inj_onI)
  fix v w
  assume v: "v \<in> H_BBK_domain \<sigma>" and w: "w \<in> H_BBK_domain \<sigma>"
    and codes: "H_BBK_nat_code v = H_BBK_nat_code w"
  show "v = w" by (rule H_BBK_nat_code_cross_type_injective[OF v w codes])
qed

theorem H_BBK_nat_code_inj_on_universe:
  "inj_on H_BBK_nat_code H_BBK_canonical_universe"
proof (rule inj_onI)
  fix v w
  assume v: "v \<in> H_BBK_canonical_universe"
    and w: "w \<in> H_BBK_canonical_universe"
    and codes: "H_BBK_nat_code v = H_BBK_nat_code w"
  have "v = H_BBK_nat_decode (H_BBK_nat_code v)"
    by (rule sym[OF H_BBK_nat_decode_code[OF v]])
  also have "... = H_BBK_nat_decode (H_BBK_nat_code w)" by (simp only: codes)
  also have "... = w" by (rule H_BBK_nat_decode_code[OF w])
  finally show "v = w" .
qed

lemma H_BBK_nat_code_equal_implies_type_equal:
  assumes v: "v \<in> H_BBK_domain \<sigma>" and w: "w \<in> H_BBK_domain \<tau>"
    and codes: "H_BBK_nat_code v = H_BBK_nat_code w"
  shows "\<sigma> = \<tau>"
proof -
  have vw_eq: "v = w" by (rule H_BBK_nat_code_cross_type_injective[OF v w codes])
  have "\<sigma> = fst v" by (rule sym[OF H_BBK_domain_tag[OF v]])
  also have "... = fst w" by (simp only: vw_eq)
  also have "... = \<tau>" by (rule H_BBK_domain_tag[OF w])
  finally show ?thesis .
qed

subsection \<open>Image domains and inverse maps\<close>

text \<open>
  Dσⁿᵃᵗ = c[Dσ], c⁻¹ ∘ c = id on Dσ, and c ∘ c⁻¹ = id on Dσⁿᵃᵗ. Bacon–Dorr, Theorem
  3.2, pp. 44–45, countable-domain refinement.

  Isabelle representation: H_BBK_nat_domain is the image domain, and the inverse is
  used only at valid codes.

  Status: Both typed roundtrips are proved; invalid codes have no asserted inverse
  behavior.
\<close>

lemma H_BBK_nat_domainI:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_nat_code v \<in> H_BBK_nat_domain \<sigma>"
  unfolding H_BBK_nat_domain_def by (rule imageI[OF domain])

lemma H_BBK_nat_domainE:
  assumes image: "n \<in> H_BBK_nat_domain \<sigma>"
  obtains v where "v \<in> H_BBK_domain \<sigma>" and "n = H_BBK_nat_code v"
proof -
  have member: "n \<in> image H_BBK_nat_code (H_BBK_domain \<sigma>)"
    using image by (simp only: H_BBK_nat_domain_def)
  from member show thesis
  proof (rule imageE)
    fix v
    assume code: "n = H_BBK_nat_code v" and domain: "v \<in> H_BBK_domain \<sigma>"
    show thesis by (rule that[OF domain code])
  qed
qed

lemma H_BBK_nat_decode_typed:
  assumes image: "n \<in> H_BBK_nat_domain \<sigma>"
  shows "H_BBK_nat_decode n \<in> H_BBK_domain \<sigma>"
proof -
  obtain v where domain: "v \<in> H_BBK_domain \<sigma>" and code: "n = H_BBK_nat_code v"
    by (rule H_BBK_nat_domainE[OF image])
  have decoded: "H_BBK_nat_decode n = v"
    by (simp only: code H_BBK_nat_decode_code_domain[OF domain])
  show ?thesis by (simp only: decoded domain)
qed

lemma H_BBK_nat_code_decode:
  assumes image: "n \<in> H_BBK_nat_domain \<sigma>"
  shows "H_BBK_nat_code (H_BBK_nat_decode n) = n"
proof -
  obtain v where domain: "v \<in> H_BBK_domain \<sigma>" and code: "n = H_BBK_nat_code v"
    by (rule H_BBK_nat_domainE[OF image])
  show ?thesis by (simp only: code H_BBK_nat_decode_code_domain[OF domain])
qed

lemma H_BBK_nat_domain_bijection:
  "bij_betw H_BBK_nat_code (H_BBK_domain \<sigma>) (H_BBK_nat_domain \<sigma>)"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on H_BBK_nat_code (H_BBK_domain \<sigma>)"
    by (rule H_BBK_nat_code_inj_on_domain)
  show "image H_BBK_nat_code (H_BBK_domain \<sigma>) = H_BBK_nat_domain \<sigma>"
    by (simp only: H_BBK_nat_domain_def)
qed

lemma H_BBK_nat_domain_subset_nat:
  "H_BBK_nat_domain \<sigma> \<subseteq> (UNIV :: nat set)"
proof (rule subsetI)
  fix n
  assume "n \<in> H_BBK_nat_domain \<sigma>"
  show "n \<in> (UNIV :: nat set)" by (rule UNIV_I)
qed

lemma H_BBK_nat_domain_nonempty:
  "H_BBK_nat_domain \<sigma> \<noteq> {}"
proof -
  have typed: "[] \<turnstile> Const '''' \<sigma> : \<sigma>" by (rule has_type.Const)
  have domain: "H_BBK_class \<sigma> (Const '''' \<sigma>) \<in> H_BBK_domain \<sigma>"
    by (rule H_BBK_class_in_domain[OF typed])
  have member: "H_BBK_nat_code (H_BBK_class \<sigma> (Const '''' \<sigma>)) \<in> H_BBK_nat_domain \<sigma>"
    by (rule H_BBK_nat_domainI[OF domain])
  show ?thesis
  proof
    assume empty: "H_BBK_nat_domain \<sigma> = {}"
    have "H_BBK_nat_code (H_BBK_class \<sigma> (Const '''' \<sigma>)) \<in> {}"
      using member by (simp only: empty)
    then show False by (simp only: empty_iff)
  qed
qed

lemma H_BBK_nat_domains_disjoint:
  assumes distinct: "\<sigma> \<noteq> \<tau>"
  shows "H_BBK_nat_domain \<sigma> \<inter> H_BBK_nat_domain \<tau> = {}"
proof (rule equalityI)
  show "H_BBK_nat_domain \<sigma> \<inter> H_BBK_nat_domain \<tau> \<subseteq> {}"
  proof (rule subsetI)
    fix n
    assume both: "n \<in> H_BBK_nat_domain \<sigma> \<inter> H_BBK_nat_domain \<tau>"
    have left: "n \<in> H_BBK_nat_domain \<sigma>" by (rule IntD1[OF both])
    have right: "n \<in> H_BBK_nat_domain \<tau>" by (rule IntD2[OF both])
    obtain v where v: "v \<in> H_BBK_domain \<sigma>" and nv: "n = H_BBK_nat_code v"
      by (rule H_BBK_nat_domainE[OF left])
    obtain w where w: "w \<in> H_BBK_domain \<tau>" and nw: "n = H_BBK_nat_code w"
      by (rule H_BBK_nat_domainE[OF right])
    have codes: "H_BBK_nat_code v = H_BBK_nat_code w"
      by (simp only: sym[OF nv] sym[OF nw])
    have equal_types: "\<sigma> = \<tau>"
      by (rule H_BBK_nat_code_equal_implies_type_equal[OF v w codes])
    have False by (rule notE[OF distinct equal_types])
    then show "n \<in> {}" by (rule FalseE)
  qed
  show "{} \<subseteq> H_BBK_nat_domain \<sigma> \<inter> H_BBK_nat_domain \<tau>" by (rule empty_subsetI)
qed

text \<open>
  The domains now have injective codes in one specified countable carrier.
  Both round-trip laws hold on the appropriate typed domains.  The next stage
  must transport interpretation and truth and verify the BBK clauses before
  claiming completeness for models whose domains are subsets of the naturals.
\<close>

end
end
