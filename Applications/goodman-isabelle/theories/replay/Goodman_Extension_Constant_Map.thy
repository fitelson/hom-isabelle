theory Goodman_Extension_Constant_Map
  imports Goodman_Extension_Retraction
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Name_Map
begin

section \<open>Typed constant maps preserve the complete axiom extension\<close>

text \<open>
  A type-indexed constant map ρ sends each declared c:τ in Σ to a declared
  ρτ(c):τ in Ω. It leaves variables, binders, logical symbols, and occurrence
  types unchanged. A C+[T] proof then becomes a C+[ρ(T)] proof. In particular
  the additional axiom stock is mapped, not silently held fixed.

  No injectivity assumption is needed for this forward theorem. Both Gen
  and PE are checked in the induction, including PE above added axioms.
  This result neither reflects proofs nor supplies a semantic model.
\<close>

theorem gi_goodman_typed_constant_map:
  fixes \<rho> :: "otype \<Rightarrow> 'c \<Rightarrow> 'd"
    and \<Sigma> :: "'c ssignature" and \<Omega> :: "'d ssignature"
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "goodman_book_proves \<Omega> G
    (image (book_typed_name_map \<rho>) T) (book_typed_name_map \<rho> A)"
  using derivation
proof (induction rule: goodman_book_proves.induct)
  case (Axiom A)
  have member: "book_typed_name_map \<rho> A \<in> image (book_typed_name_map \<rho>) T"
    using Axiom.hyps(1) by blast
  have language: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> A)"
    by (rule book_typed_name_map_language[OF Axiom.hyps(2) maps])
  show ?case by (rule goodman_book_proves.Axiom[OF member language])
next
  case (Base A)
  have mapped: "book_full_C_proves \<Omega> G (book_typed_name_map \<rho> A)"
    by (rule book_full_C_typed_name_map[OF rich Base.hyps maps])
  show ?case by (rule goodman_book_proves.Base[OF mapped])
next
  case (MP A B)
  have conditional: "goodman_book_proves \<Omega> G (image (book_typed_name_map \<rho>) T)
    (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using MP.IH(2) by (simp only: book_typed_name_map_imp)
  have language: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> B)"
    by (rule book_typed_name_map_language[OF MP.hyps(3) maps])
  show ?case by (rule goodman_book_proves.MP[OF MP.IH(1) conditional language])
next
  case (Gen A B n)
  have conditional: "goodman_book_proves \<Omega> G (image (book_typed_name_map \<rho>) T)
    (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using Gen.IH by (simp only: book_typed_name_map_imp)
  have antecedent: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> A)"
    by (rule book_typed_name_map_language[OF Gen.hyps(2) maps])
  have consequent: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> B)"
    by (rule book_typed_name_map_language[OF Gen.hyps(3) maps])
  have fresh: "n \<notin> named_fv (book_typed_name_map \<rho> A)"
    by (simp only: book_typed_name_map_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_typed_name_map_imp book_typed_name_map_all;
    rule goodman_book_proves.Gen[OF conditional antecedent consequent fresh])
next
  case (PE P Q)
  have premise: "goodman_book_proves \<Omega> G (image (book_typed_name_map \<rho>) T)
    (book_iff G (book_typed_name_map \<rho> P) (book_typed_name_map \<rho> Q))"
    using PE.IH by (simp only: book_C_typed_rename_iff)
  have pl: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> P)"
    by (rule book_typed_name_map_language[OF PE.hyps(2) maps])
  have ql: "book_theory_formula \<Omega> G (book_typed_name_map \<rho> Q)"
    by (rule book_typed_name_map_language[OF PE.hyps(3) maps])
  show ?case by (simp only: book_C_typed_rename_leibniz;
    rule goodman_book_proves.PE[OF premise pl ql])
qed

section \<open>The declared Pure/Fun signature in string notation\<close>

fun gi_goodman_string_name :: "goodman_constant \<Rightarrow> string" where
  "gi_goodman_string_name PureName = pp_pure_name"
| "gi_goodman_string_name FunName = pp_fun_name"

definition gi_goodman_string_signature :: "string ssignature" where
  "gi_goodman_string_signature \<tau> =
    (if \<exists>\<sigma>. \<tau> = Arr \<sigma> Prop then {pp_pure_name, pp_fun_name} else {})"

abbreviation gi_goodman_string_term :: "gb_term \<Rightarrow> string book_named_term" where
  "gi_goodman_string_term A \<equiv> book_typed_name_map (\<lambda>_. gi_goodman_string_name) A"

lemma gi_goodman_string_signature_map:
  "c \<in> gb_signature \<tau> \<Longrightarrow>
    gi_goodman_string_name c \<in> gi_goodman_string_signature \<tau>"
  by (cases c; auto simp: gb_signature_def gi_goodman_string_signature_def split: if_splits)

lemma gi_goodman_string_signature_exact:
  "gi_goodman_string_name ` gb_signature \<tau> = gi_goodman_string_signature \<tau>"
  by (auto simp: gb_signature_def gi_goodman_string_signature_def split: if_splits)

lemma gi_goodman_string_signature_predicate:
  "gi_goodman_string_signature (Arr \<sigma> Prop) = {pp_pure_name, pp_fun_name}"
  by (simp add: gi_goodman_string_signature_def)

lemma gi_goodman_string_signature_nonpredicate:
  "(\<nexists>\<sigma>. \<tau> = Arr \<sigma> Prop) \<Longrightarrow> gi_goodman_string_signature \<tau> = {}"
  by (simp add: gi_goodman_string_signature_def)

lemma gi_goodman_string_term_language:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<tau>"
  shows "book_in_language book_minimal_logical_type UNIV gi_goodman_string_signature G
    (gi_goodman_string_term A) \<tau>"
  by (rule book_typed_name_map_language[OF language gi_goodman_string_signature_map])

lemma gi_goodman_string_term_fv:
  "named_fv (gi_goodman_string_term A) = named_fv A"
  by (rule book_typed_name_map_fv)

lemma gi_goodman_string_term_Pure:
  "gi_goodman_string_term (gb_Pure \<sigma>) = NConst pp_pure_name (Arr \<sigma> Prop)"
  by (simp add: gb_Pure_def)

lemma gi_goodman_string_term_Fun:
  "gi_goodman_string_term (gb_Fun \<sigma>) = NConst pp_fun_name (Arr \<sigma> Prop)"
  by (simp add: gb_Fun_def)

theorem gi_goodman_string_proof_preservation:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves gb_signature G T A"
  shows "goodman_book_proves gi_goodman_string_signature G
    (image gi_goodman_string_term T) (gi_goodman_string_term A)"
  by (rule gi_goodman_typed_constant_map[OF rich derivation gi_goodman_string_signature_map])

text \<open>
  Native PureName and FunName are now represented by the original strings
  Pure and Fun, but only at predicate types σ → t. This is not the universal
  string signature. The operation changes nonlogical names only: variables,
  binders, Leibniz identity, modal abbreviations, and logical representatives
  are preserved as syntax. The result supplies the proof transport needed by
  a string-based evaluator; soundness for that evaluator remains a separate
  theorem and no denotational-stock identification is inferred here.
\<close>

end
