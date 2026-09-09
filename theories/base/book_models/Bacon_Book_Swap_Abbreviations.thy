theory Bacon_Book_Swap_Abbreviations
  imports Bacon_Book_Minimal_Formula_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Characterization
begin

section \<open>Swapping closed terms changes bound names only\<close>

text \<open>
  A same-type swap (x y) sends a closed term A to an α-equivalent
  term. Source role: preserving the literal closed abbreviations of
  Table 4.1, p.93, during the proof substitutions discussed on p.102.

  Isabelle representation. Swap encoding is free-slot renaming. A closed
  encoding has no free slots, so that renaming has no effect. The proved
  encoding characterization supplies the independently generated α
  relation in rich G. This argument works even on raw closed terms;
  typed book specializations also retain their independently proved types.

  Status. No semantic or H judgment is assumed. The rich-stock premise
  is explicit. α-equivalence is not replaced by literal syntactic equality:
  the swap can move binder names inside the chosen definitions.
\<close>

theorem book_swap_closed_alpha:
  fixes A :: "('c, 'l) named_term"
  assumes rich: "sg_rich G" and same_type: "G x = G y" and closed: "named_fv A = {}"
  shows "named_alpha G (named_swap x y A) A"
proof -
  let ?E = "named_to_source G [] A"
  have empty: "sfv ?E = {}" by (rule named_to_source_closed[OF closed])
  have agrees: "srename (named_swap_index x y) ?E = srename (named_index []) ?E"
  proof (rule srename_fv_agreement)
    fix n
    assume member: "n \<in> sfv ?E"
    show "named_swap_index x y n = named_index [] n"
      using member by (simp only: empty; simp)
  qed
  have identity: "srename (named_index []) ?E = ?E"
    by (rule named_to_source_stack_from_empty[where G=G and ns="[]" and A=A])
  have encoded: "named_to_source G [] (named_swap x y A) = ?E"
    by (rule trans[OF sym[OF named_swap_encoding_empty[where G=G and A=A, OF same_type]]
      trans[OF agrees identity]])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich encoded])
qed

corollary book_swap_bottom_alpha:
  fixes G :: sgcontext
  assumes rich: "sg_rich G" and same_type: "G x = G y"
  shows "named_alpha G (named_swap x y (book_bottom G :: 'c book_named_term)) (book_bottom G)"
  by (rule book_swap_closed_alpha[OF rich same_type book_bottom_closed])

corollary book_swap_not_const_alpha:
  fixes G :: sgcontext
  assumes rich: "sg_rich G" and same_type: "G x = G y"
  shows "named_alpha G (named_swap x y (book_not_const G :: 'c book_named_term)) (book_not_const G)"
  by (rule book_swap_closed_alpha[OF rich same_type book_not_const_closed])

lemma book_swap_imp:
  fixes A B :: "'c book_named_term"
  shows "named_swap x y (book_imp A B) = book_imp (named_swap x y A) (named_swap x y B)"
  by (simp only: book_imp_def named_swap.simps)

text \<open>
  Thus swapping ¬A yields the literal negation of the swapped A up to
  α-equivalence, with the original closed negation operator retained.
  This is the syntactic fact needed to transport the PC3 schema; it
  neither expands ¬A into A→⊥ nor proves a rule of H.
\<close>

lemma book_swap_not_alpha:
  fixes A :: "'c book_named_term"
  assumes rich: "sg_rich G" and same_type: "G x = G y"
  shows "named_alpha G (named_swap x y (book_not G A)) (book_not G (named_swap x y A))"
  by (simp only: book_not_def named_swap.simps;
    rule named_alpha.App[OF book_swap_not_const_alpha[OF rich same_type] named_alpha.Refl])

end
