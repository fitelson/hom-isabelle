theory Bacon_Book_H_Typed_Name_Map
  imports Bacon_Book_Typed_Name_Conversion
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Derivation
begin

section \<open>All nine book theory constructors preserve type-indexed name maps\<close>

theorem book_theory_typed_name_map:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "book_theory_derivable \<Omega> G (image (book_typed_name_map \<rho>) S)
    (book_typed_name_map \<rho> A)"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case (Assumption A S)
  have member: "book_typed_name_map \<rho> A \<in> image (book_typed_name_map \<rho>) S"
    by (rule imageI[OF Assumption.hyps(1)])
  have language: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> A)"
    by (rule book_typed_name_map_language[OF Assumption.hyps(2) maps])
  show ?case by (rule book_theory_derivable.Assumption[OF member language])
next
  case PC1
  show ?case by (simp only: book_typed_name_map_imp;
    rule book_theory_derivable.PC1[OF book_typed_name_map_language[OF PC1.hyps(1) maps]
      book_typed_name_map_language[OF PC1.hyps(2) maps]])
next
  case PC2
  show ?case by (simp only: book_typed_name_map_imp;
    rule book_theory_derivable.PC2[OF book_typed_name_map_language[OF PC2.hyps(1) maps]
      book_typed_name_map_language[OF PC2.hyps(2) maps]
      book_typed_name_map_language[OF PC2.hyps(3) maps]])
next
  case PC3
  show ?case by (simp only: book_typed_name_map_imp book_typed_name_map_not;
    rule book_theory_derivable.PC3[OF book_typed_name_map_language[OF PC3.hyps(1) maps]
      book_typed_name_map_language[OF PC3.hyps(2) maps]])
next
  case UI
  show ?case by (simp only: book_typed_name_map_imp book_typed_name_map.simps;
    rule book_theory_derivable.UI[OF book_typed_name_map_language[OF UI.hyps(1) maps]
      book_typed_name_map_language[OF UI.hyps(2) maps]])
next
  case (Beta A B S)
  have steps: "named_compatible_step named_beta_contract
      (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B) \<or>
    named_compatible_step named_beta_contract
      (book_typed_name_map \<rho> B) (book_typed_name_map \<rho> A)"
  proof (rule disjE[OF Beta.hyps(3)])
    assume step: "named_compatible_step named_beta_contract A B"
    show ?thesis by (rule disjI1; rule book_typed_name_map_beta_step[OF step])
  next
    assume step: "named_compatible_step named_beta_contract B A"
    show ?thesis by (rule disjI2; rule book_typed_name_map_beta_step[OF step])
  qed
  show ?case by (simp only: book_typed_name_map_imp;
    rule book_theory_derivable.Beta[OF book_typed_name_map_language[OF Beta.hyps(1) maps]
      book_typed_name_map_language[OF Beta.hyps(2) maps] steps])
next
  case (Eta A B S)
  have steps: "named_compatible_step named_eta_contract
      (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B) \<or>
    named_compatible_step named_eta_contract
      (book_typed_name_map \<rho> B) (book_typed_name_map \<rho> A)"
  proof (rule disjE[OF Eta.hyps(3)])
    assume step: "named_compatible_step named_eta_contract A B"
    show ?thesis by (rule disjI1; rule book_typed_name_map_eta_step[OF step])
  next
    assume step: "named_compatible_step named_eta_contract B A"
    show ?thesis by (rule disjI2; rule book_typed_name_map_eta_step[OF step])
  qed
  show ?case by (simp only: book_typed_name_map_imp;
    rule book_theory_derivable.Eta[OF book_typed_name_map_language[OF Eta.hyps(1) maps]
      book_typed_name_map_language[OF Eta.hyps(2) maps] steps])
next
  case (MP S A B)
  have implication: "book_theory_derivable \<Omega> G (image (book_typed_name_map \<rho>) S)
    (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using MP.IH(2) by (simp only: book_typed_name_map_imp)
  show ?case by (rule book_theory_derivable.MP[OF MP.IH(1) implication
    book_typed_name_map_language[OF MP.hyps(3) maps]])
next
  case (Gen S A B n)
  have implication: "book_theory_derivable \<Omega> G (image (book_typed_name_map \<rho>) S)
    (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using Gen.IH by (simp only: book_typed_name_map_imp)
  have fresh: "n \<notin> named_fv (book_typed_name_map \<rho> A)"
    by (simp only: book_typed_name_map_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_typed_name_map_imp book_typed_name_map_all;
    rule book_theory_derivable.Gen[OF implication
      book_typed_name_map_language[OF Gen.hyps(2) maps]
      book_typed_name_map_language[OF Gen.hyps(3) maps] fresh])
qed

text \<open>
  The name map may depend on the occurrence type. Each H theory
  constructor is checked in the original full-F book basis, including
  both directions of contextual β/η and the original Gen freshness
  condition. No injectivity, model or new logical rule is assumed.
\<close>

end

