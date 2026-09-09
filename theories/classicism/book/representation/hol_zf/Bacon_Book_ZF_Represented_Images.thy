theory Bacon_Book_ZF_Represented_Images
  imports Bacon_Book_ZF_Term_Class_Codes
begin

section \<open>Replacement on a proved bounded source carrier\<close>

definition book_ZF_powerset_image :: "('a::countable set \<Rightarrow> ZF) \<Rightarrow> 'a set set \<Rightarrow> ZF" where
  "book_ZF_powerset_image f S = Repl
    (paper_ZF_image_code (Power HOLZF.Nat) book_ZF_countable_set_code S)
    (\<lambda>z. f (inv book_ZF_countable_set_code z))"

theorem book_ZF_powerset_image_elements:
  "explode (book_ZF_powerset_image f S) = f ` S"
proof -
  let ?C = "paper_ZF_image_code (Power HOLZF.Nat) book_ZF_countable_set_code S"
  have source: "explode ?C = book_ZF_countable_set_code ` S"
    by (rule paper_ZF_image_code_elements[OF book_ZF_countable_sets_bound subset_UNIV])
  show ?thesis
  proof
    show "explode (book_ZF_powerset_image f S) \<subseteq> f ` S"
    proof
      fix y
      assume member: "y \<in> explode (book_ZF_powerset_image f S)"
      obtain z where zm: "Elem z ?C" and shape: "y = f (inv book_ZF_countable_set_code z)"
        using member unfolding book_ZF_powerset_image_def by (simp only: explode_Elem Repl; blast)
      have image_member: "z \<in> book_ZF_countable_set_code ` S"
        using zm by (simp only: explode_Elem[symmetric] source)
      obtain X where xm: "X \<in> S" and zs: "z = book_ZF_countable_set_code X" using image_member by blast
      show "y \<in> f ` S" by (simp only: shape zs book_ZF_countable_set_inverse; rule imageI[OF xm])
    qed
    show "f ` S \<subseteq> explode (book_ZF_powerset_image f S)"
    proof
      fix y
      assume member: "y \<in> f ` S"
      obtain X where xm: "X \<in> S" and shape: "y = f X" using member by blast
      have coded: "book_ZF_countable_set_code X \<in> explode ?C" by (simp only: source; rule imageI[OF xm])
      have internal: "Elem (book_ZF_countable_set_code X) ?C" using coded by (simp only: explode_Elem)
      have equation: "y = f (inv book_ZF_countable_set_code (book_ZF_countable_set_code X))"
        by (simp only: book_ZF_countable_set_inverse shape)
      show "y \<in> explode (book_ZF_powerset_image f S)"
        unfolding book_ZF_powerset_image_def
        by (simp only: explode_Elem Repl; rule exI[where x="book_ZF_countable_set_code X"], rule conjI[OF internal equation])
    qed
  qed
qed

text \<open>
  An arbitrary ZF-valued image of a set of subsets of a countable
  carrier is an actual HOL-ZF set: first encode the source inside
  Power(Nat), then use Replacement. Exact image membership is proved.
  This is the range construction needed for Dσw from hσ and the
  already bounded typed term-class domain. It needs no guessed bound
  on the target range and makes no universe-wide representability claim.
\<close>

end
