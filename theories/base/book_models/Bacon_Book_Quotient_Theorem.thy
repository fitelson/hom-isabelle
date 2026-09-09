theory Bacon_Book_Quotient_Theorem
  imports Bacon_Book_Full_Minimal_Quotient Bacon_Book_Quotient_Truth
begin

section \<open>Leibnizianity and the full-language minimal-basis quotient theorem\<close>

text \<open>
  A structure with valuation is Leibnizian when Leibniz-equivalent
  elements are equal (Bacon, Definition 15.6, p.322). The quotient
  has this property without assuming it in the original model.

  The final theorem collects three proved conclusions for the specified
  full-language minimal model: its displayed quotient is a model of the
  same kind, is Leibnizian, and makes exactly the same formulas true
  under universal quantification over typed assignments. This includes
  the sentence-preservation conclusion of Proposition 15.5, p.322.

  This is a qualified source case, not the result for every general
  𝒥(Σ), every partial primitive basis, or alternative conventions for
  closed denotations without an assignment. Those remain explicit
  obligations in the source matrix. No claim of H soundness or
  completeness follows from this quotient theorem alone.
\<close>

definition book_leibnizian where
  "book_leibnizian D app V \<longleftrightarrow>
    (\<forall>\<sigma> a b. book_leibniz_equiv D app V \<sigma> a b \<longrightarrow> a = b)"

context book_full_environment
begin

theorem book_leibniz_quotient_is_leibnizian:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "book_leibnizian (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V)"
proof (unfold book_leibnizian_def, intro allI impI)
  fix \<sigma> X Y
  assume equivalent: "book_leibniz_equiv (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V) \<sigma> X Y"
  have left: "X \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    by (rule book_leibniz_left[OF equivalent])
  have right: "Y \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    by (rule book_leibniz_right[OF equivalent])
  show "X = Y" by (rule iffD1[OF book_leibniz_quotient_separation[OF rich typed left right] equivalent])
qed

end

context book_full_minimal_model
begin

theorem book_proposition_15_5_full_minimal:
  assumes rich: "sg_rich stock"
  shows "book_full_minimal_model (book_leibniz_quotient_domain domain app V)
      (book_leibniz_quotient_app domain app V) signature stock
      (book_leibniz_quotient_denote V) (book_leibniz_quotient_valuation V)
      (\<lambda>l. book_leibniz_class domain app V (book_minimal_logical_type l) (\<kappa> l)) \<and>
    book_leibnizian (book_leibniz_quotient_domain domain app V)
      (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V) \<and>
    (\<forall>A. book_in_language book_minimal_logical_type UNIV signature stock A Prop \<longrightarrow>
      ((\<forall>q. book_env_typed (book_leibniz_quotient_domain domain app V) stock q \<longrightarrow>
          book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)) \<longleftrightarrow>
       (\<forall>g. book_env_typed domain stock g \<longrightarrow> V (denote g A))))"
proof (rule conjI[OF book_full_minimal_quotient_model[OF rich]], rule conjI)
  obtain g where typed: "book_env_typed domain stock g"
    using book_minimal_assignment_exists by (elim exE)
  show "book_leibnizian (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V)"
    by (rule book_leibniz_quotient_is_leibnizian[OF rich typed])
next
  show "\<forall>A. book_in_language book_minimal_logical_type UNIV signature stock A Prop \<longrightarrow>
    ((\<forall>q. book_env_typed (book_leibniz_quotient_domain domain app V) stock q \<longrightarrow>
        book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)) \<longleftrightarrow>
     (\<forall>g. book_env_typed domain stock g \<longrightarrow> V (denote g A)))"
    by (intro allI impI, rule book_leibniz_quotient_validity_iff[OF rich], assumption)
qed

end

end
