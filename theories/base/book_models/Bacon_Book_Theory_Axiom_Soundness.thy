theory Bacon_Book_Theory_Axiom_Soundness
  imports Bacon_Book_Minimal_Validity
begin

section \<open>The printed propositional and universal-instantiation schemas are valid\<close>

text \<open>
  PC1: A→(B→A).
  PC2: (A→(B→C))→((A→B)→(A→C)).
  PC3: ((¬A)→(¬B))→(B→A).
  UI: (∀σ F)→Fa.
  Source: Bacon, Chapter 5, pp.97–98, and Theorem 15.1, p.318.

  Isabelle representation. Each operand has its displayed language/type
  guard. Nested implications use the primitive implication truth theorem;
  PC3 uses the proved truth of the literal λ-defined negation. UI applies
  the primitive universal quantifier to an arbitrary typed predicate F,
  and tests it at the actual typed denotation of a.

  Scope. Full-language minimal models with witnessed logical values.
  Richness is explicit for PC3's defined negation. No arbitrary-tautology
  axiom, proof-calculus assumption, Functionality, identity principle, or
  complete book-H soundness theorem is introduced by these four lemmas.
  Immediate symmetric β/η schemas are handled separately as implications.
\<close>

context book_full_minimal_model
begin

theorem book_PC1_valid:
  assumes al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "book_formula_valid domain stock denote V (book_imp A (book_imp B A))"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have ba: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp B A) Prop"
    by (rule book_imp_language[OF bl al])
  show "V (denote g (book_imp A (book_imp B A)))"
    by (simp only: book_imp_truth[OF typed al ba] book_imp_truth[OF typed bl al]; blast)
qed

theorem book_PC2_valid:
  assumes al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
    and cl: "book_in_language book_minimal_logical_type UNIV signature stock C Prop"
  shows "book_formula_valid domain stock denote V
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have bc: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp B C) Prop"
    by (rule book_imp_language[OF bl cl])
  have abc: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp A (book_imp B C)) Prop"
    by (rule book_imp_language[OF al bc])
  have ab: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp A B) Prop"
    by (rule book_imp_language[OF al bl])
  have ac: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp A C) Prop"
    by (rule book_imp_language[OF al cl])
  have conclusion: "book_in_language book_minimal_logical_type UNIV signature stock
    (book_imp (book_imp A B) (book_imp A C)) Prop"
    by (rule book_imp_language[OF ab ac])
  show "V (denote g
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C))))"
    by (simp only: book_imp_truth[OF typed abc conclusion] book_imp_truth[OF typed al bc]
      book_imp_truth[OF typed bl cl] book_imp_truth[OF typed ab ac]
      book_imp_truth[OF typed al bl] book_imp_truth[OF typed al cl]; blast)
qed

theorem book_PC3_valid:
  assumes rich: "sg_rich stock"
    and al: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and bl: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "book_formula_valid domain stock denote V
    (book_imp (book_imp (book_not stock A) (book_not stock B)) (book_imp B A))"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have na: "book_in_language book_minimal_logical_type UNIV signature stock (book_not stock A) Prop"
    by (rule book_not_language[OF rich al])
  have nb: "book_in_language book_minimal_logical_type UNIV signature stock (book_not stock B) Prop"
    by (rule book_not_language[OF rich bl])
  have nab: "book_in_language book_minimal_logical_type UNIV signature stock
    (book_imp (book_not stock A) (book_not stock B)) Prop"
    by (rule book_imp_language[OF na nb])
  have ba: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp B A) Prop"
    by (rule book_imp_language[OF bl al])
  show "V (denote g (book_imp (book_imp (book_not stock A) (book_not stock B)) (book_imp B A)))"
    by (simp only: book_imp_truth[OF typed nab ba] book_imp_truth[OF typed na nb]
      book_not_truth[OF rich typed al] book_not_truth[OF rich typed bl]
      book_imp_truth[OF typed bl al]; blast)
qed

theorem book_UI_valid:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV signature stock F (Arr \<sigma> Prop)"
    and argument: "book_in_language book_minimal_logical_type UNIV signature stock a \<sigma>"
  shows "book_formula_valid domain stock denote V
    (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof (rule book_formula_validI)
  fix g
  assume typed: "book_env_typed domain stock g"
  have universal_language: "book_in_language book_minimal_logical_type UNIV signature stock
    (NApp (NLogical (SBAll \<sigma>)) F) Prop"
    by (rule book_language_App[OF book_all_operator_language predicate])
  have application_language: "book_in_language book_minimal_logical_type UNIV signature stock (NApp F a) Prop"
    by (rule book_language_App[OF predicate argument])
  have implication: "V (denote g (NApp (NLogical (SBAll \<sigma>)) F)) \<longrightarrow> V (denote g (NApp F a))"
  proof
    assume all_true: "V (denote g (NApp (NLogical (SBAll \<sigma>)) F))"
    have every: "\<forall>x \<in> domain \<sigma>. V (app \<sigma> Prop (denote g F) x)"
      by (rule iffD1[OF book_forall_application_truth[OF typed predicate] all_true])
    have member: "denote g a \<in> domain \<sigma>" by (rule denote_type[OF UNIV_I argument typed])
    have tested: "V (app \<sigma> Prop (denote g F) (denote g a))"
      by (rule bspec[OF every member])
    have application: "denote g (NApp F a) = app \<sigma> Prop (denote g F) (denote g a)"
      by (rule denote_app[OF UNIV_I UNIV_I UNIV_I predicate argument typed])
    show "V (denote g (NApp F a))" by (simp only: application; rule tested)
  qed
  show "V (denote g (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a)))"
    by (rule iffD2[OF book_imp_truth[OF typed universal_language application_language] implication])
qed

end

end
