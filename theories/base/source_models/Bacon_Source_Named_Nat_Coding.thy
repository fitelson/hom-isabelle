theory Bacon_Source_Named_Nat_Coding
  imports Bacon_Parametric_Countable_Development.Bacon_Parametric_Countable_Coding
    "HOL-Library.Nat_Bijection"
begin

section \<open>Coding a type-tagged natural number by one natural number\<close>

text \<open>
  Send ⟨σ,n⟩ to pair(code(σ),n). The resulting map from F × ℕ
  to ℕ is injective. Source role: the countable-domain refinement in
  Bacon–Dorr Theorem 3.2, pp.44–45.

  Isabelle representation. pHct_type_code is the existing proved injection
  of otype into nat, and prod_encode is the library's natural-number
  pairing function. The inverse is total in HOL but its right-inverse
  equation is asserted only on the code's range. Surjectivity onto every
  natural number is neither needed nor claimed.

  Status. Pure carrier coding, with no named model or model-existence
  premise. Countability here concerns the whole carrier otype × nat,
  not the arbitrary canonical-class carrier or nonlogical-name type.
\<close>

definition named_nat_code :: "otype \<times> nat \<Rightarrow> nat" where
  "named_nat_code x = prod_encode (pHct_type_code (fst x), snd x)"

theorem named_nat_code_inj: "inj named_nat_code"
proof (rule injI)
  fix x y
  assume codes: "named_nat_code x = named_nat_code y"
  have pairs: "(pHct_type_code (fst x), snd x) = (pHct_type_code (fst y), snd y)"
    using codes by (simp only: named_nat_code_def prod_encode_eq)
  have type_codes: "pHct_type_code (fst x) = pHct_type_code (fst y)"
    using pairs by simp
  have types: "fst x = fst y" by (rule injD[OF pHct_type_code_inj type_codes])
  have payloads: "snd x = snd y" using pairs by simp
  show "x = y" using types payloads by (cases x; cases y) simp
qed

lemma named_nat_code_eq_iff:
  "named_nat_code x = named_nat_code y \<longleftrightarrow> x = y"
  by (rule inj_eq[OF named_nat_code_inj])

lemma named_nat_code_inv_left:
  "inv named_nat_code (named_nat_code x) = x"
  by (rule inv_f_f[OF named_nat_code_inj])

lemma named_nat_code_inv_right:
  assumes member: "n \<in> range named_nat_code"
  shows "named_nat_code (inv named_nat_code n) = n"
proof -
  obtain x where encoded: "n = named_nat_code x" using member by blast
  show ?thesis by (simp only: encoded named_nat_code_inv_left)
qed

theorem named_nat_carrier_countable:
  "countable (UNIV :: (otype \<times> nat) set)"
  unfolding countable_def
  by (rule exI[where x=named_nat_code], rule named_nat_code_inj)

end
