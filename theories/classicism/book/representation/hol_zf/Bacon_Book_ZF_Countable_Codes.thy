theory Bacon_Book_ZF_Countable_Codes
  imports Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Natural_Bounds
    Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Embedded_Carriers
    Bacon_Book_Classicism_Development.Bacon_Book_Name_Countability
begin

section \<open>Explicit natural-number and powerset bounds\<close>

definition book_ZF_countable_code :: "'a::countable \<Rightarrow> ZF" where
  "book_ZF_countable_code x = nat2Nat (to_nat x)"

lemma book_ZF_countable_code_injective:
  "inj (book_ZF_countable_code :: 'a::countable \<Rightarrow> ZF)"
proof (rule injI)
  fix x y :: 'a
  assume equal: "book_ZF_countable_code x = book_ZF_countable_code y"
  have codes: "nat2Nat (to_nat x) = nat2Nat (to_nat y)" using equal unfolding book_ZF_countable_code_def .
  have numbers: "to_nat x = to_nat y" by (rule injD[OF inj_nat2Nat codes])
  show "x = y" using numbers by simp
qed

lemma book_ZF_countable_code_bound:
  "range (book_ZF_countable_code :: 'a::countable \<Rightarrow> ZF) \<subseteq> explode HOLZF.Nat"
  by (auto simp: book_ZF_countable_code_def explode_Elem intro: Elem_nat2Nat_Nat)

definition book_ZF_countable_set_code :: "'a::countable set \<Rightarrow> ZF" where
  "book_ZF_countable_set_code S = paper_ZF_image_code HOLZF.Nat book_ZF_countable_code S"

theorem book_ZF_countable_set_elements:
  "explode (book_ZF_countable_set_code S) = book_ZF_countable_code ` S"
  unfolding book_ZF_countable_set_code_def
  by (rule paper_ZF_image_code_elements[OF book_ZF_countable_code_bound subset_UNIV])

lemma book_ZF_countable_set_bound:
  "book_ZF_countable_set_code S \<in> explode (Power HOLZF.Nat)"
  unfolding book_ZF_countable_set_code_def by (rule paper_ZF_image_code_type)

theorem book_ZF_countable_set_code_injective:
  "inj (book_ZF_countable_set_code :: 'a::countable set \<Rightarrow> ZF)"
proof (rule injI)
  fix S T :: "'a set"
  assume equal: "book_ZF_countable_set_code S = book_ZF_countable_set_code T"
  have decoded: "explode (book_ZF_countable_set_code S) = explode (book_ZF_countable_set_code T)"
    by (rule arg_cong[OF equal])
  have images: "book_ZF_countable_code ` S = book_ZF_countable_code ` T"
    using decoded by (simp only: book_ZF_countable_set_elements)
  show "S = T" using images book_ZF_countable_code_injective by (auto dest: injD)
qed

lemma book_ZF_countable_sets_bound:
  "range (book_ZF_countable_set_code :: 'a::countable set \<Rightarrow> ZF) \<subseteq> explode (Power HOLZF.Nat)"
  using book_ZF_countable_set_bound by blast

lemma book_ZF_countable_set_inverse:
  "inv book_ZF_countable_set_code (book_ZF_countable_set_code S) = S"
  by (rule inv_f_f[OF book_ZF_countable_set_code_injective])

text \<open>
  FOUNDATION: standard HOL-ZF set axioms, not pure HOL.
  A countable HOL carrier embeds explicitly into the elements of Nat.
  Every subset of that carrier is then encoded by separation in Nat;
  its code lies in Power(Nat), with exact elements and injectivity proved.
  This does not assert representability of arbitrary HOL carriers or
  identify the entire HOL type ZF with an internal set.
\<close>

end
