theory Bacon_Book_ZF_Represented_Images
  imports Bacon_Book_ZF_Term_Class_Codes
begin

section \<open>Replacement on a proved bounded source carrier\<close>

context book_full_C_coded_frame
begin

definition book_ZF_powerset_image :: "('c book_named_term set \<Rightarrow> ZF) \<Rightarrow> 'c book_named_term set set \<Rightarrow> ZF" where
  "book_ZF_powerset_image f S = Repl
    (paper_ZF_image_code (Power term_bound) class_code S)
    (\<lambda>z. f (class_decode z))"

theorem book_ZF_powerset_image_elements:
  assumes admitted: "S \<subseteq> admitted_term_sets"
  shows "explode (book_ZF_powerset_image f S) = f ` S"
proof -
  let ?C = "paper_ZF_image_code (Power term_bound) class_code S"
  have source: "explode ?C = class_code ` S"
    by (rule paper_ZF_image_code_elements[OF class_codes_bound subset_UNIV])
  show ?thesis
  proof
    show "explode (book_ZF_powerset_image f S) \<subseteq> f ` S"
    proof
      fix y
      assume member: "y \<in> explode (book_ZF_powerset_image f S)"
      obtain z where zm: "Elem z ?C" and shape: "y = f (class_decode z)"
        using member unfolding book_ZF_powerset_image_def by (simp only: explode_Elem Repl; blast)
      have image_member: "z \<in> class_code ` S"
        using zm by (simp only: explode_Elem[symmetric] source)
      obtain X where xm: "X \<in> S" and zs: "z = class_code X" using image_member by blast
      have xs: "X \<in> admitted_term_sets" by (rule subsetD[OF admitted xm])
      show "y \<in> f ` S" by (simp only: shape zs class_code_inverse[OF xs]; rule imageI[OF xm])
    qed
    show "f ` S \<subseteq> explode (book_ZF_powerset_image f S)"
    proof
      fix y
      assume member: "y \<in> f ` S"
      obtain X where xm: "X \<in> S" and shape: "y = f X" using member by blast
      have coded: "class_code X \<in> explode ?C" by (simp only: source; rule imageI[OF xm])
      have internal: "Elem (class_code X) ?C" using coded by (simp only: explode_Elem)
      have xs: "X \<in> admitted_term_sets" by (rule subsetD[OF admitted xm])
      have equation: "y = f (class_decode (class_code X))"
        by (simp only: class_code_inverse[OF xs] shape)
      show "y \<in> explode (book_ZF_powerset_image f S)"
        unfolding book_ZF_powerset_image_def
        by (simp only: explode_Elem Repl; rule exI[where x="class_code X"], rule conjI[OF internal equation])
    qed
  qed
qed

end

text \<open>
  An arbitrary ZF-valued image of a family of subsets of the terms
  admitted by the ambient signature B is an actual HOL-ZF set: first
  encode the source inside Power(term_bound), then use Replacement through
  the class decoder. The exact-image law requires the family to consist of
  admitted term sets (S ⊆ admitted_term_sets), because the term code is
  total on raw terms but injective only on admitted terms; the
  construction itself is total. This is the range construction needed for Dσw from hσ and the
  already bounded typed term-class domain. It needs no guessed bound
  on the target range and makes no universe-wide representability claim.
\<close>

end
