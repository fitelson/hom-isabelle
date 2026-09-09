theory Bacon_Parametric_Countable_Coding
  imports Bacon_Parametric_Canonical_Development.Bacon_Parametric_Canonical_Model
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Henkin_Names
    "HOL-Library.Countable_Set"
begin

section \<open>Countable syntax without a legacy type instance\<close>

text \<open>
  For countably many original names, both finite terms and their finite
  nested witness-name trees are countable.  Thus ⋃σDσ is countable when
  Dσ consists of canonical classes of closed terms.  Source: Bacon–Dorr,
  Theorem 3.2, pp.44–45, countable-signature refinement and p.45 n.64.

  Isabelle representation: first establish countability of the set of
  object types, without declaring an otype class instance or importing the
  legacy string construction.  A small natural-number-labelled tree codes
  terms and recursive witness names.  Only actual canonical values, not
  the ambient powerset-valued HOL carrier, receive an injective code.
  This leaf supplies no semantic model transport.
\<close>

lemma pHct_otypes_countable: "countable (UNIV :: otype set)"
  unfolding countable_def by countable_datatype

definition pHct_type_code :: "otype \<Rightarrow> nat" where
  "pHct_type_code = (SOME f. inj f)"

lemma pHct_type_code_inj: "inj pHct_type_code"
  unfolding pHct_type_code_def
  by (rule someI_ex[OF pHct_otypes_countable[unfolded countable_def]])

lemma pHct_type_code_eq [simp]:
  "pHct_type_code \<sigma> = pHct_type_code \<tau> \<longleftrightarrow> \<sigma> = \<tau>"
  by (rule inj_eq[OF pHct_type_code_inj])

datatype pHct_tree = pHct_Atom nat
  | pHct_Unary nat pHct_tree | pHct_Binary nat pHct_tree pHct_tree

instance pHct_tree :: countable by countable_datatype

fun pHct_term_tree :: "('c \<Rightarrow> pHct_tree) \<Rightarrow> 'c pterm \<Rightarrow> pHct_tree" where
  "pHct_term_tree k (PVar n) = pHct_Unary 0 (pHct_Atom n)"
| "pHct_term_tree k (PConst c \<sigma>) = pHct_Binary 1 (k c) (pHct_Atom (pHct_type_code \<sigma>))"
| "pHct_term_tree k (PApp M N) = pHct_Binary 2 (pHct_term_tree k M) (pHct_term_tree k N)"
| "pHct_term_tree k (PLam \<sigma> M) = pHct_Binary 3 (pHct_Atom (pHct_type_code \<sigma>)) (pHct_term_tree k M)"
| "pHct_term_tree k (PEq \<sigma> M N) = pHct_Binary 4 (pHct_Atom (pHct_type_code \<sigma>))
    (pHct_Binary 0 (pHct_term_tree k M) (pHct_term_tree k N))"
| "pHct_term_tree k (PNeg A) = pHct_Unary 5 (pHct_term_tree k A)"
| "pHct_term_tree k (PConj A B) = pHct_Binary 6 (pHct_term_tree k A) (pHct_term_tree k B)"
| "pHct_term_tree k (PDisj A B) = pHct_Binary 7 (pHct_term_tree k A) (pHct_term_tree k B)"
| "pHct_term_tree k (PImp A B) = pHct_Binary 8 (pHct_term_tree k A) (pHct_term_tree k B)"
| "pHct_term_tree k (PForall \<sigma> A) = pHct_Binary 9 (pHct_Atom (pHct_type_code \<sigma>)) (pHct_term_tree k A)"
| "pHct_term_tree k (PExists \<sigma> A) = pHct_Binary 10 (pHct_Atom (pHct_type_code \<sigma>)) (pHct_term_tree k A)"

lemma pHct_term_tree_map:
  "pHct_term_tree k (map_pterm f A) = pHct_term_tree (\<lambda>c. k (f c)) A"
  by (induction A) simp_all

lemma pHct_term_tree_reflects:
  assumes names: "\<forall>c \<in> set_pterm A. \<forall>d. k c = k d \<longrightarrow> c = d"
    and code: "pHct_term_tree k A = pHct_term_tree k B"
  shows "A = B"
  using names code
proof (induction A arbitrary: B)
  case (PVar n) then show ?case by (cases B) simp_all
next
  case (PConst c \<sigma>) then show ?case by (cases B) auto
next
  case (PApp M N) then show ?case by (cases B) auto
next
  case (PLam \<sigma> M) then show ?case by (cases B) auto
next
  case (PEq \<sigma> M N) then show ?case by (cases B) auto
next
  case (PNeg A) then show ?case by (cases B) auto
next
  case (PConj A C) then show ?case by (cases B) auto
next
  case (PDisj A C) then show ?case by (cases B) auto
next
  case (PImp A C) then show ?case by (cases B) auto
next
  case (PForall \<sigma> A) then show ?case by (cases B) auto
next
  case (PExists \<sigma> A) then show ?case by (cases B) auto
qed

lemma pHct_pterms_countable: "countable (UNIV :: 'c::countable pterm set)"
proof (rule countableI'[where f="pHct_term_tree (\<lambda>c. pHct_Atom (to_nat c))"])
  show "inj_on (pHct_term_tree (\<lambda>c :: 'c. pHct_Atom (to_nat c))) UNIV"
  proof (rule inj_onI)
    fix A B :: "'c pterm"
    assume "A \<in> UNIV" and "B \<in> UNIV"
      and code: "pHct_term_tree (\<lambda>c. pHct_Atom (to_nat c)) A =
        pHct_term_tree (\<lambda>c. pHct_Atom (to_nat c)) B"
    have names: "\<forall>c \<in> set_pterm A. \<forall>d.
      pHct_Atom (to_nat c) = pHct_Atom (to_nat d) \<longrightarrow> c = d" by simp
    show "A = B" by (rule pHct_term_tree_reflects[OF names code])
  qed
qed

instance pterm :: (countable) countable
  by intro_classes (rule pHct_pterms_countable[unfolded countable_def])

subsection \<open>The recursively enlarged name carrier is countable\<close>

text \<open>
  ι(c) and cσ,A are finite trees, even though A may contain earlier
  witness names.  This is a proof about the nested datatype, not an
  assumption that the witness stock is countable.  Constructor tags keep
  original names and witness names disjoint, as in the construction cited
  above.  The statement assumes a countable original name carrier.
\<close>

primrec pHct_name_tree :: "'c::countable phenkin_full_name \<Rightarrow> pHct_tree" where
  "pHct_name_tree (PFOriginal c) = pHct_Unary 11 (pHct_Atom (to_nat c))"
| "pHct_name_tree (PFWitness \<sigma> A) = pHct_Binary 12 (pHct_Atom (pHct_type_code \<sigma>))
    (pHct_term_tree id (map_pterm pHct_name_tree A))"

lemma pHct_name_tree_reflects:
  "pHct_name_tree a = pHct_name_tree b \<Longrightarrow> a = b"
proof (induction a arbitrary: b)
  case (PFOriginal c)
  then show ?case by (cases b) simp_all
next
  case (PFWitness \<sigma> A)
  show ?case
  proof (cases b)
    case (PFOriginal c)
    with PFWitness.prems show ?thesis by simp
  next
    case target: (PFWitness \<tau> B)
    have parts: "\<sigma> = \<tau> \<and> pHct_term_tree pHct_name_tree A = pHct_term_tree pHct_name_tree B"
      using PFWitness.prems by (simp only: target pHct_name_tree.simps
        pHct_tree.inject pHct_type_code_eq pHct_term_tree_map id_apply)
    have names: "\<forall>c \<in> set_pterm A. \<forall>d. pHct_name_tree c = pHct_name_tree d \<longrightarrow> c = d"
      using PFWitness.IH by blast
    have body: "A = B" by (rule pHct_term_tree_reflects[OF names conjunct2[OF parts]])
    show ?thesis by (simp only: target body conjunct1[OF parts])
  qed
qed

lemma pHct_names_countable: "countable (UNIV :: 'c::countable phenkin_full_name set)"
  by (rule countableI'[where f=pHct_name_tree], rule inj_onI,
    rule pHct_name_tree_reflects, assumption)

instance phenkin_full_name :: (countable) countable
  by intro_classes (rule pHct_names_countable[unfolded countable_def])

locale pH_countable_closed_Henkin = pH_closed_Henkin signature T
  for signature :: "'c::countable psignature" and T :: "'c pterm set"
begin

section \<open>Only the inhabited canonical universe is coded\<close>

definition pHct_universe :: "'c pHc_value set" where
  "pHct_universe = (\<Union>\<sigma>. pHc_domain \<sigma>)"

definition pHct_closed_terms :: "'c pterm set" where
  "pHct_closed_terms = {M. \<exists>\<sigma>. pterm_in_language signature [] M \<sigma>}"

lemma pHct_universeI:
  "v \<in> pHc_domain \<sigma> \<Longrightarrow> v \<in> pHct_universe"
  unfolding pHct_universe_def by (rule UN_I[where a=\<sigma>]) (rule UNIV_I, assumption)

lemma pHct_universeE:
  assumes "v \<in> pHct_universe"
  obtains \<sigma> where "v \<in> pHc_domain \<sigma>"
  using assms unfolding pHct_universe_def by (elim UN_E) (rule that, assumption)

lemma pHct_universe_closed_image:
  "pHct_universe \<subseteq> (\<lambda>M. pHc_class (pHc_type_of M) M) ` pHct_closed_terms"
proof (rule subsetI)
  fix v
  assume member: "v \<in> pHct_universe"
  obtain \<sigma> where domain: "v \<in> pHc_domain \<sigma>" by (rule pHct_universeE[OF member])
  obtain M where lang: "pterm_in_language signature [] M \<sigma>"
    and representation: "v = pHc_class \<sigma> M"
    by (rule pHc_domain_representation[OF domain])
  have typed: "has_ptype [] M \<sigma>" using lang unfolding pterm_in_language_def by (rule conjunct1)
  have closed: "M \<in> pHct_closed_terms"
    unfolding pHct_closed_terms_def by (rule CollectI, rule exI[where x=\<sigma>], rule lang)
  have image: "pHc_class (pHc_type_of M) M \<in> (\<lambda>N. pHc_class (pHc_type_of N) N) ` pHct_closed_terms"
    by (rule imageI[OF closed])
  show "v \<in> (\<lambda>M. pHc_class (pHc_type_of M) M) ` pHct_closed_terms"
    using image by (simp only: representation pHc_type_of_typed[OF typed])
qed

theorem pHct_universe_countable: "countable pHct_universe"
proof -
  have terms: "countable pHct_closed_terms" by (rule countableI_type)
  have image: "countable ((\<lambda>M. pHc_class (pHc_type_of M) M) ` pHct_closed_terms)"
    by (rule countable_image[OF terms])
  show ?thesis by (rule countable_subset[OF pHct_universe_closed_image image])
qed

text \<open>
  c(σ,[M]ₜ) = ⟨code(σ), code(rep([M]ₜ))⟩ and c⁻¹(c(v)) = v for
  v ∈ ⋃σDσ.  Source: Bacon–Dorr Theorem 3.2, countable-domain refinement.
  Choice selects representatives and the object-type code; these are not
  claimed to be computable equality tests.  Invalid natural-number codes
  have no specified semantic behavior.
\<close>

definition pHct_code :: "'c pHc_value \<Rightarrow> nat" where
  "pHct_code v = prod_encode (pHct_type_code (fst v), to_nat (pHc_rep v))"

definition pHct_decode :: "nat \<Rightarrow> 'c pHc_value" where
  "pHct_decode n = pHc_class (inv pHct_type_code (fst (prod_decode n)))
    (from_nat (snd (prod_decode n)))"

definition pHct_nat_domain :: "otype \<Rightarrow> nat set" where
  "pHct_nat_domain \<sigma> = pHct_code ` pHc_domain \<sigma>"

lemma pHct_decode_code_domain:
  assumes domain: "v \<in> pHc_domain \<sigma>"
  shows "pHct_decode (pHct_code v) = v"
proof -
  have decoded: "pHct_decode (pHct_code v) = pHc_class (fst v) (pHc_rep v)"
    by (simp only: pHct_decode_def pHct_code_def prod_encode_inverse fst_conv snd_conv
      inv_f_f[OF pHct_type_code_inj] from_nat_to_nat)
  show ?thesis by (simp only: decoded pHc_domain_tag[OF domain] pHc_rep_reconstruct[OF domain])
qed

lemma pHct_decode_code:
  "v \<in> pHct_universe \<Longrightarrow> pHct_decode (pHct_code v) = v"
  by (erule pHct_universeE, rule pHct_decode_code_domain, assumption)

theorem pHct_code_inj_on_universe: "inj_on pHct_code pHct_universe"
proof (rule inj_onI)
  fix v w
  assume v: "v \<in> pHct_universe" and w: "w \<in> pHct_universe" and eq: "pHct_code v = pHct_code w"
  have "v = pHct_decode (pHct_code v)" by (rule sym[OF pHct_decode_code[OF v]])
  also have "... = pHct_decode (pHct_code w)" by (simp only: eq)
  also have "... = w" by (rule pHct_decode_code[OF w])
  finally show "v = w" .
qed

lemma pHct_code_inj_on_domain: "inj_on pHct_code (pHc_domain \<sigma>)"
proof (rule inj_onI)
  fix v w
  assume v: "v \<in> pHc_domain \<sigma>" and w: "w \<in> pHc_domain \<sigma>" and eq: "pHct_code v = pHct_code w"
  show "v = w" by (rule inj_onD[OF pHct_code_inj_on_universe eq pHct_universeI[OF v] pHct_universeI[OF w]])
qed

lemma pHct_nat_domainI:
  "v \<in> pHc_domain \<sigma> \<Longrightarrow> pHct_code v \<in> pHct_nat_domain \<sigma>"
  unfolding pHct_nat_domain_def by (rule imageI)

lemma pHct_nat_domainE:
  assumes "n \<in> pHct_nat_domain \<sigma>"
  obtains v where "v \<in> pHc_domain \<sigma>" and "n = pHct_code v"
  using assms unfolding pHct_nat_domain_def by (elim imageE) (rule that; assumption)

lemma pHct_decode_typed:
  assumes code: "n \<in> pHct_nat_domain \<sigma>"
  shows "pHct_decode n \<in> pHc_domain \<sigma>"
proof -
  obtain v where domain: "v \<in> pHc_domain \<sigma>" and eq: "n = pHct_code v"
    by (rule pHct_nat_domainE[OF code])
  show ?thesis by (simp only: eq pHct_decode_code_domain[OF domain] domain)
qed

lemma pHct_code_decode:
  assumes code: "n \<in> pHct_nat_domain \<sigma>"
  shows "pHct_code (pHct_decode n) = n"
proof -
  obtain v where domain: "v \<in> pHc_domain \<sigma>" and eq: "n = pHct_code v"
    by (rule pHct_nat_domainE[OF code])
  show ?thesis by (simp only: eq pHct_decode_code_domain[OF domain])
qed

lemma pHct_nat_domain_bijection:
  "bij_betw pHct_code (pHc_domain \<sigma>) (pHct_nat_domain \<sigma>)"
  unfolding bij_betw_def pHct_nat_domain_def
  by (rule conjI[OF pHct_code_inj_on_domain refl])

lemma pHct_nat_domain_nonempty: "pHct_nat_domain \<sigma> \<noteq> {}"
proof
  assume empty: "pHct_nat_domain \<sigma> = {}"
  have source_empty: "pHc_domain \<sigma> = {}"
    using empty unfolding pHct_nat_domain_def by blast
  show False by (rule notE[OF pHc_domain_nonempty source_empty])
qed

end

end
