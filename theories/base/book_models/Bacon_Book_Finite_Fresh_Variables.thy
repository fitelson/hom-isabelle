theory Bacon_Book_Finite_Fresh_Variables
  imports Bacon_Book_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Rich_Stock
begin

section \<open>Distinct fresh variables for finitely many typed replacements\<close>

text \<open>
  For a finite collection K of replacement keys, assign a distinct variable
  v(k) of each prescribed type τ(k), avoiding a finite set F of names.
  This uses richness of the source variable stock, not an enumeration of
  nonlogical constants. The intended F contains all names of the original
  formula and of every replacement term. Consequently later insertion of
  one replacement cannot introduce another placeholder.

  This is only the name-selection lemma for Definition 5.2's simultaneous
  substitution proof. It asserts no substitution admissibility or model
  existence, and puts no cardinality restriction on the ambient key type.
\<close>

theorem book_finite_fresh_variables:
  assumes rich: "sg_rich G" and finite_K: "finite K" and finite_F: "finite F"
  shows "\<exists>v. inj_on v K \<and> (\<forall>k\<in>K. G (v k) = \<tau> k \<and> v k \<notin> F)"
  using finite_K
proof (induction rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert k K)
  obtain v where injective: "inj_on v K"
    and assigned: "\<forall>j\<in>K. G (v j) = \<tau> j \<and> v j \<notin> F"
    using insert.IH by (elim exE conjE)
  have finite_forbidden: "finite (F \<union> v ` K)"
    by (rule finite_UnI[OF finite_F], rule finite_imageI[OF insert.hyps(1)])
  obtain n where typed: "G n = \<tau> k" and fresh: "n \<notin> F \<union> v ` K"
    using sg_rich_fresh[where \<sigma>="\<tau> k" and S="F \<union> v ` K",
      OF rich finite_forbidden] by (elim exE conjE)
  let ?w = "v(k := n)"
  have agrees: "?w j = v j" if "j \<in> K" for j
    using that insert.hyps(2) by auto
  have new_injective: "inj_on ?w (insert k K)"
    using injective fresh insert.hyps(2)
    by (auto simp: inj_on_def split: if_splits)
  have new_assigned: "\<forall>j\<in>insert k K. G (?w j) = \<tau> j \<and> ?w j \<notin> F"
    using assigned typed fresh agrees by auto
  show ?case by (rule exI[where x="?w"], rule conjI[OF new_injective new_assigned])
qed

end
