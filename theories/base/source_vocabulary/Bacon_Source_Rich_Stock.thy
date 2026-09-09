theory Bacon_Source_Rich_Stock
  imports Bacon_Source_Global_Typing "HOL-Library.Nat_Bijection"
begin

section \<open>An explicit infinite family of variables at every F type\<close>

text \<open>
  There are infinitely many variables of each type (Bacon–Dorr §1.1,
  p. 5).  We realize this with variables indexed by pairs (σ,k), where
  σ is a full F type and k is a natural number.

  Isabelle representation: sg_type_code recursively injects otype into nat.
  The library's natural-number pairing encodes (sg_type_code σ,k) as a
  slot.  sg_standard_stock decodes the type component using the inverse of
  that injection.  Slots whose first component is outside its range receive
  the total HOL inverse's unspecified value; the displayed witness slots
  never use those components.

  Status: a closed definition satisfying sg_rich, without a new axiom,
  an otype class instance, or a canonical-model dependency.  This codes
  variable slots only and imposes no countability condition on nonlogical
  source names.
\<close>

fun sg_type_code :: "otype \<Rightarrow> nat" where
  "sg_type_code Ind = 0"
| "sg_type_code Prop = 1"
| "sg_type_code (Arr \<sigma> \<tau>) = Suc (Suc (prod_encode (sg_type_code \<sigma>, sg_type_code \<tau>)))"

lemma sg_type_code_eq_iff:
  "sg_type_code \<sigma> = sg_type_code \<tau> \<longleftrightarrow> \<sigma> = \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case Ind
  show ?case by (cases \<tau>) simp_all
next
  case Prop
  show ?case by (cases \<tau>) simp_all
next
  case (Arr \<sigma> \<rho>)
  show ?case by (cases \<tau>) (simp_all add: Arr.IH)
qed

lemma sg_type_code_inj:
  "inj sg_type_code"
  by (rule injI) (simp only: sg_type_code_eq_iff)

definition sg_stock_index :: "otype \<Rightarrow> nat \<Rightarrow> nat" where
  "sg_stock_index \<sigma> k = prod_encode (sg_type_code \<sigma>, k)"

definition sg_standard_stock :: sgcontext where
  "sg_standard_stock n = inv sg_type_code (fst (prod_decode n))"

lemma sg_standard_stock_index:
  "sg_standard_stock (sg_stock_index \<sigma> k) = \<sigma>"
  unfolding sg_standard_stock_def sg_stock_index_def
  by (simp only: prod_encode_inverse fst_conv inv_f_f[OF sg_type_code_inj])

lemma sg_stock_index_inj:
  "inj (sg_stock_index \<sigma>)"
  unfolding sg_stock_index_def by (rule injI) simp

lemma sg_stock_index_infinite:
  "infinite (image (sg_stock_index \<sigma>) UNIV)"
proof
  assume finite_image: "finite (image (sg_stock_index \<sigma>) UNIV)"
  have finite_nat: "finite (UNIV :: nat set)"
    by (rule finite_imageD[OF finite_image sg_stock_index_inj])
  show False using finite_nat by simp
qed

theorem sg_standard_stock_rich:
  "sg_rich sg_standard_stock"
proof (unfold sg_rich_def, rule allI)
  fix \<sigma>
  have contained: "image (sg_stock_index \<sigma>) UNIV \<subseteq> {n. sg_standard_stock n = \<sigma>}"
  proof (rule subsetI)
    fix n
    assume "n \<in> image (sg_stock_index \<sigma>) UNIV"
    then obtain k where eq: "n = sg_stock_index \<sigma> k" by (elim imageE)
    show "n \<in> {n. sg_standard_stock n = \<sigma>}"
      by (simp only: eq mem_Collect_eq sg_standard_stock_index)
  qed
  show "infinite {n. sg_standard_stock n = \<sigma>}"
    by (rule infinite_super[OF contained sg_stock_index_infinite])
qed

corollary sg_rich_stock_exists:
  "\<exists>G :: sgcontext. sg_rich G"
  by (rule exI[where x=sg_standard_stock], rule sg_standard_stock_rich)

section \<open>A fresh variable outside every finite forbidden set\<close>

text \<open>
  For each type σ and finite set S of variables, some v:σ lies outside S.
  This supplies the finite freshness choices needed by the variable
  conventions and Gen/Inst side conditions in Bacon–Dorr Figures 1–2.

  Isabelle representation: the statement holds for every sg_rich G, not
  just the constructed stock.  A finite set cannot contain a whole infinite
  type fiber.

  Status: fresh variable availability, not an object-language existence
  theorem or a named-variable/α-equivalence correspondence.
\<close>

lemma sg_rich_fresh:
  assumes rich: "sg_rich G" and finite_S: "finite S"
  shows "\<exists>n. G n = \<sigma> \<and> n \<notin> S"
proof (rule ccontr)
  assume absent: "\<not> (\<exists>n. G n = \<sigma> \<and> n \<notin> S)"
  have contained: "{n. G n = \<sigma>} \<subseteq> S" using absent by auto
  have finite_fiber: "finite {n. G n = \<sigma>}"
    by (rule finite_subset[OF contained finite_S])
  have infinite_fiber: "infinite {n. G n = \<sigma>}" by (rule sg_rich_type_fiber[OF rich])
  show False by (rule notE[OF infinite_fiber finite_fiber])
qed

lemma sg_rich_fresh_variable:
  assumes "sg_rich G" and "finite S"
  obtains n where "G n = \<sigma>" and "n \<notin> S"
proof -
  obtain n where typed: "G n = \<sigma>" and fresh: "n \<notin> S"
    using sg_rich_fresh[where \<sigma>=\<sigma>, OF assms] by (elim exE conjE)
  show thesis by (rule that[OF typed fresh])
qed

corollary sg_standard_stock_fresh:
  assumes "finite S"
  shows "\<exists>n. sg_standard_stock n = \<sigma> \<and> n \<notin> S"
  by (rule sg_rich_fresh[OF sg_standard_stock_rich assms])

end
