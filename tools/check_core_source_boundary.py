#!/usr/bin/env python3
"""Check structural source-fidelity boundaries for the Bacon core.

This is a drift detector, not a proof of historical interpretation. Isabelle
checks theorem derivations; the dated audit and reader guide record the human
source comparison.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]

# Match actual foundation names, not the "Zet" prefix inside "Zeta".
# Include continuation lines of the imports block as well as its first line.
FOUNDATION_IMPORT = (
    r"^\s*imports\b(?:(?!^\s*begin\b)[\s\S])*?"
    r"(?<![A-Za-z0-9_])(?:HOL-ZF|HOLZF|MainZF|Zet)(?![A-Za-z0-9_])"
)


def check_foundation_import_guard() -> None:
    for imported in ("HOL-ZF.MainZF", "HOLZF", "MainZF", "Zet"):
        for prefix in ("imports ", "imports Main\n  "):
            example = prefix + imported + "\nbegin\n"
            if not re.search(FOUNDATION_IMPORT, example, flags=re.MULTILINE):
                raise AssertionError(f"Foundation-import positive control missed {example!r}")
    for example in (
        "imports Bacon_Source_Relational_Zeta_Theory\nbegin\n",
        'imports Main\nbegin\ntext \\<open>No HOL-ZF premise.\\<close>\n',
    ):
        if re.search(FOUNDATION_IMPORT, example, flags=re.MULTILINE):
            raise AssertionError(f"Foundation-import negative control rejected {example!r}")


def require(path: str, fragments: list[str]) -> None:
    source = (ROOT / path).read_text(encoding="utf-8")
    for fragment in fragments:
        if fragment not in source:
            raise AssertionError(f"{path}: missing required marker {fragment!r}")


def forbid(path: str, patterns: list[str]) -> None:
    source = (ROOT / path).read_text(encoding="utf-8")
    for pattern in patterns:
        if re.search(pattern, source, flags=re.MULTILINE):
            raise AssertionError(f"{path}: forbidden pattern {pattern!r}")


def main() -> int:
    check_foundation_import_guard()
    # Full-F syntax alone is not Chapter 8 full-type Classicism. Keep
    # the older Equivalence base and the source MF+PE presentation distinct.
    for filename, judgment, expected in (
        ("Bacon_Book_Classicism_Derivation.thy", "book_C_proves", ["H", "MP", "Gen", "Equivalence"]),
        ("Bacon_Book_Full_Classicism_Calculus.thy", "book_full_C_proves", ["H", "MF", "MP", "Gen", "PE"]),
        ("Bacon_Book_Full_Equivalence_Presentation.thy", "book_full_C_vector_proves", ["H", "MF", "MP", "Gen", "Equivalence"]),
    ):
        source = (ROOT / "theories/classicism/book" / filename).read_text(encoding="utf-8")
        clauses = source.split(f"inductive {judgment} ::", 1)[1].split("\ntheorem ", 1)[0]
        actual = re.findall(r"^\s*(?:\|\s*)?([A-Za-z_]\w*):", clauses, flags=re.MULTILINE)
        if actual != expected:
            raise AssertionError(f"{filename}: source calculus constructors {actual!r}, expected {expected!r}")
    require("theories/classicism/book/Bacon_Book_Full_Modalized_Functionality.thy", [
        "definition book_MF_axiom", "definition book_MF_body",
        "book_MF_names_distinct", "book_MF_axiom_language", "book_MF_axiom_closed",
        'book_leibniz G (Arr \\<sigma> \\<tau>)',
    ])
    action_dir = "theories/classicism/action_models"
    require("ROOT", [
        'session Bacon_Book_Modal_Representation in "theories/classicism/book/representation" = Bacon_Book_Classicism_Development +',
        "Bacon_Book_Modal_Representation_Audit",
    ])
    require("check_isabelle.sh", ["Bacon_Book_Modal_Representation"])
    require("ROOT", ["Bacon_Book_Term_Interpretation_Audit", "Bacon_Book_ZF_Interpretation_Audit"])
    require("ROOT", ["Bacon_Book_Term_Logical_Audit", "Bacon_Book_ZF_Logical_Audit"])
    require("ROOT", ["Bacon_Book_Term_Identity_Audit", "Bacon_Book_ZF_Identity_Audit"])
    require("ROOT", ["Bacon_Book_Combinator_Syntax_Audit", "Bacon_Book_ZF_Operators_Audit"])
    require("theories/classicism/book/representation/Bacon_Book_Combinator_Syntax_Audit.thy", [
        "FOUNDATION: pure HOL; no HOL-ZF import", "Bacon_Core_Audit_Check.run",
        "book-combinator-syntax-audit.txt", "book_canonical_K_closed_terms", "book_canonical_S_closed_terms",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Operators_Audit.thy", [
        "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL combinator-syntax audit",
        "Bacon_Core_Audit_Check.run", "book-zf-operators-audit.txt", "explicit future restriction",
        "book_full_C_canonical_frame.full_ZF_implication_future_set",
        "book_full_C_canonical_frame.full_ZF_forall_future_value",
        "book_full_C_canonical_frame.full_ZF_K_future_value",
        "book_full_C_canonical_frame.full_ZF_S_future_value",
    ])
    require("theories/classicism/book/representation/Bacon_Book_Term_Identity_Audit.thy", [
        "FOUNDATION: pure HOL; no HOL-ZF import",
        "Bacon_Core_Audit_Check.run", "book-term-identity-audit.txt",
        "book_full_C_canonical_frame.full_term_leibniz_iff_equal",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Identity_Audit.thy", [
        "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term-identity audit",
        "Bacon_Core_Audit_Check.run", "book-zf-identity-audit.txt",
        "book_full_C_canonical_frame.full_ZF_equality_future_value",
    ])
    require("theories/classicism/book/representation/Bacon_Book_Term_Logical_Audit.thy", [
        "FOUNDATION: pure HOL; no HOL-ZF import", "Bacon_Core_Audit_Check.run",
        "book-term-logical-audit.txt", "not the complete modal-model certificate",
        "book_full_C_canonical_frame.full_term_general_model",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Logical_Audit.thy", [
        "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term-model audit",
        "Bacon_Core_Audit_Check.run", "book-zf-logical-audit.txt",
        "book_full_C_canonical_frame.full_ZF_general_model",
        "book_full_C_canonical_frame.full_ZF_forall_truth",
    ])
    require("theories/classicism/book/representation/Bacon_Book_Term_Interpretation_Audit.thy", [
        "FOUNDATION: pure HOL; no HOL-ZF import",
        "Bacon_Core_Audit_Check.run", "book-term-interpretation-audit.txt",
        "book_C_identity_world.identity_environment_representative_independence",
        "book_full_C_canonical_frame.full_term_denote_natural",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Interpretation_Audit.thy", [
        "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term interpretation audit",
        "Bacon_Core_Audit_Check.run", "book-zf-interpretation-audit.txt",
        "book_full_C_canonical_frame.full_ZF_denote_lambda_future",
    ])
    for path in (ROOT / "theories/classicism/book/representation").glob("*.thy"):
        forbid(str(path.relative_to(ROOT)), [FOUNDATION_IMPORT, r"^\s*(?:axiomatization|axioms)\b"])
    require("ROOT", [
        'session Bacon_Book_ZF_Modal_Representation in "theories/classicism/book/representation/hol_zf" = Bacon_Book_Modal_Representation +',
        'sessions Bacon_Classicism_ZF_Representation "HOL-ZF"',
        "Bacon_Book_ZF_Representation_Audit",
    ])
    require("check_isabelle.sh", ["Bacon_Book_ZF_Modal_Representation"])
    require("ROOT", [
        'session Bacon_Book_ZF_Modal_Semantics in "theories/classicism/book/modal_semantics/hol_zf" = "HOL-ZF" +',
        "Bacon_Book_ZF_Model_Definition_Audit", "Bacon_Book_ZF_Reindexed_Structure_Audit",
    ])
    require("check_isabelle.sh", ["Bacon_Book_ZF_Modal_Semantics"])
    require("ROOT", ["Bacon_Book_ZF_Canonical_Modal_Model", "Bacon_Book_ZF_Canonical_Model_Audit"])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Canonical_Model_Audit.thy", [
        "Bacon_Core_Audit_Check.run", "book-zf-canonical-model-audit.txt",
        "book_full_C_canonical_frame.full_ZF_canonical_modal_model",
    ])
    canonical_model_source = (ROOT / "theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Canonical_Modal_Model.thy").read_text(encoding="utf-8")
    canonical_model_statement = canonical_model_source.split("theorem full_ZF_canonical_modal_model:", 1)[1].split("\nproof ", 1)[0]
    if "assumes" in canonical_model_statement or "book_ZF_modal_model full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at" not in canonical_model_statement:
        raise AssertionError("Canonical endpoint must instantiate the complete independent model predicate without an added model premise")
    require("tools/isabelle_kg/build_graph.sh", ["Bacon_Book_ZF_Modal_Semantics"])
    model_dir = "theories/classicism/book/modal_semantics/hol_zf"
    for path in (ROOT / model_dir).glob("*.thy"):
        forbid(str(path.relative_to(ROOT)), [
            r"\b(?:book_full_C_\w*|book_C_\w*|full_ZF_\w*|H_proves|pH_proves|C_proves|CE_proves|CEV_proves|book_full_minimal_model|book_env_typed)\b",
            r"^\s*(?:axiomatization|axioms)\b",
            r"::\s*countable\b",
        ])
    require(f"{model_dir}/Bacon_Book_ZF_Modal_Structure.thy", [
        "F = Lambda (book_ZF_pairs W R (D \\<sigma>) w) (app F)",
        "function_graph_domain", "function_natural:", "function_restriction:",
    ])
    require(f"{model_dir}/Bacon_Book_ZF_Model_Definition_Audit.thy", [
        "Bacon_Core_Audit_Check.run", "book-zf-model-definition-audit.txt",
        "book_ZF_isFun_domain_insufficient", "book_ZF_modal_structure.future_function_extensionality",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Reindexed_Structure_Audit.thy", [
        "Bacon_Core_Audit_Check.run", "book-zf-reindexed-structure-audit.txt",
        "book_full_C_canonical_frame.full_ZF_reindexed_graph_exact",
        "book_full_C_canonical_frame.full_ZF_reindexed_structure",
    ])
    require("theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Representation_Audit.thy", [
        "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL core audit",
        "Bacon_Core_Audit_Check.run", "book-zf-representation-audit.txt",
        "no complete modal-model or completeness claim",
    ])
    for path in (ROOT / "theories/classicism/book/representation/hol_zf").glob("*.thy"):
        forbid(str(path.relative_to(ROOT)), [
            r"^\s*(?:axiomatization|axioms)\b",
            r"^\s*imports\b(?:(?!^\s*begin\b)[\s\S])*?(?:Bacon_PP_|Goodman_)",
        ])
    require("theories/classicism/book/representation/Bacon_Book_Modal_Representation_Audit.thy", [
        "Bacon_Core_Audit_Check.run", "modal-representation-audit.txt",
        "no all-type recursion or modal completeness claim",
    ])
    for path in (ROOT / action_dir).rglob("*.thy"):
        # Isar schematic index-zero aliases can overwrite the unindexed name.
        # Old/new semantic objects must have genuinely distinct proof names.
        forbid(str(path.relative_to(ROOT)), [
            r"\blet\s+\?[A-Za-z_][A-Za-z_0-9]*0\s*=",
            r"^\s*(?:assumes|and|have)\s+(?:proof|instance|premises|binder|value|values|output|functions|structure|constant|back|syntax):",
        ])
    for path in (ROOT / action_dir).glob("*.thy"):
        forbid(str(path.relative_to(ROOT)), [
            FOUNDATION_IMPORT,
        ])
    require("theories/classicism/action_models/Bacon_Source_Rooted_Category.thy", [
        'root_object: "root \\<in> objects"',
        'root_reaches: "A \\<in> objects \\<Longrightarrow> \\<exists>h\\<in>arrows.',
        "theorem paper_root_arrows_need_not_be_unique",
    ])
    require("ROOT", [
        'session Bacon_Classicism_ZF_Representation in "theories/classicism/action_models/hol_zf" = "HOL-ZF" +',
    ])
    require("theories/classicism/action_models/hol_zf/Bacon_Classicism_ZF_Audit.thy", [
        "FOUNDATION: standard HOL-ZF set axioms, not pure HOL",
        "Bacon_Core_Audit_Check.run",
        "UNIV_is_not_in_ZF",
        "zf-representation-audit.txt",
    ])
    zf_exp = (ROOT / action_dir / "hol_zf/Bacon_Source_ZF_Exponential_Code.thy").read_text(encoding="utf-8")
    zf_pair_locale = zf_exp.split("locale paper_ZF_action_pair =", 1)[1].split("\nbegin", 1)[0]
    if "paper_exponential_actions" not in zf_pair_locale or "assumes" in zf_pair_locale:
        raise AssertionError("Coded exponential must assume only the two source actions, not its target action")
    require(f"{action_dir}/hol_zf/Bacon_Source_ZF_Exponential_Transport.thy", [
        "Lambda (paper_ZF_pair_code A source target X (target f))",
        "Opair (compose (Fst z) f) (Snd z)",
    ])
    # Definition 3.19 is independent of the model used in Proposition 3.22.
    # These source checks supplement, rather than replace, kernel/dependency
    # checks and the literal comparison with the six printed clauses.
    for filename in ("Bacon_Source_ZF_Logical_Values.thy",
                     "Bacon_Source_ZF_Partial_Abstraction.thy",
                     "Bacon_Source_ZF_Partial_Interpretation.thy",
                     "Bacon_Source_ZF_Action_Model.thy"):
        forbid(f"{action_dir}/hol_zf/{filename}", [
            r"\b(?:paper_bbk_denote|paper_ZF_rep_encode|paper_ZF_R_type_representation|paper_R_bbk_model|paper_named_bbk_model|H_proves|pH_proves|C_proves|CE_proves|CEV_proves)\b",
        ])
    require(f"{action_dir}/hol_zf/Bacon_Source_ZF_Graph_Application.thy", [
        "if isFun F \\<and> Elem x (Domain F) then Some (app F x) else None",
    ])
    require(f"{action_dir}/hol_zf/Bacon_Source_ZF_Partial_Abstraction.thy", [
        "B (compose (Fst z) h)",
        "(paper_ZF_action_transport_assignment G T (Fst z) g)(n := Some (Snd z))",
        "\\<forall>z\\<in>explode P. V z \\<noteq> None",
        "then Some (Lambda P",
    ])
    eval_source = (ROOT / action_dir / "hol_zf/Bacon_Source_ZF_Partial_Interpretation.thy").read_text(encoding="utf-8")
    eval_clauses = eval_source.split("primrec paper_ZF_action_eval", 1)[1].split("lemma ", 1)[0]
    eval_constructors = re.findall(r'^\s*(?:\|\s*)?"paper_ZF_action_eval[^\n]*\((NVar|NConst|NLogical|NApp|NLam)\b',
                                   eval_clauses, flags=re.MULTILINE)
    if eval_constructors != ["NVar", "NConst", "NLogical", "NApp", "NLam"]:
        raise AssertionError(f"Independent action interpretation constructors changed: {eval_constructors}")
    if "paper_ZF_graph_apply f (Opair (identity (target h)) b)" not in eval_clauses:
        raise AssertionError("Partial interpretation must guard graph application")
    require(f"{action_dir}/hol_zf/Bacon_Source_ZF_Action_Model.thy", [
        "paper_R_rich G", "paper_ZF_action_premodel", "paper_R_in_language",
        "h \\<in> explode Ar", "source h = root",
        "paper_ZF_action_env_typed D G (target h) g", "named_adequate g B",
        "v \\<in> explode (D \\<rho> (target h))",
    ])
    require(f"{action_dir}/Bacon_Source_BBK_Homomorphism.thy", [
        "definition paper_bbk_homomorphism", "paper_hom_assignment G h g",
        "named_adequate g A", "theorem paper_bbk_homomorphism_compose",
    ])
    raw_hom_source = (ROOT / action_dir / "Bacon_Source_BBK_Homomorphism.thy").read_text(encoding="utf-8")
    raw_hom_clause = raw_hom_source.split("definition paper_bbk_homomorphism", 1)[1].split("lemma ", 1)[0]
    if re.search(r"\b(valuation|named_valid|named_satisfies|paper_named_bbk_model)\b", raw_hom_clause):
        raise AssertionError("Raw BBK homomorphism condition must preserve interpretation, not valuation")
    require(f"{action_dir}/Bacon_Source_BBK_Model_Morphism.thy", [
        "paper_named_bbk_model \\<Sigma> G D J V", "paper_named_bbk_model \\<Sigma> G E K W",
        "paper_bbk_homomorphism \\<Sigma> G D J E K h",
    ])
    require(f"{action_dir}/Bacon_Source_Action.thy", [
        "locale paper_action", "transport_type", "transport_identity", "transport_compose",
        "transport (compose g f) x = transport g (transport f x)",
    ])
    require(f"{action_dir}/Bacon_Source_BBK_Subcategory.thy", [
        "definition paper_bbk_subcategory", "Arrows \\<subseteq> paper_bbk_arrows",
        "paper_typed_identity paper_bbk_domain M \\<in> Arrows",
        "paper_typed_compose paper_bbk_domain g f \\<in> Arrows",
    ])
    require(f"{action_dir}/Bacon_Source_BBK_Selected_Truth_Profile.thy", [
        "definition paper_bbk_truth_profile_on", "paper_bbk_truth_profile_on Arrows M p",
        "paper_bbk_truth_profile_on_naturality",
    ])
    require(f"{action_dir}/Bacon_Source_Typed_Arrows.thy", [
        "paper_typed_map_normal (D (paper_arrow_source f)) (paper_arrow_map f)",
        "paper_typed_map_normalize (D A)",
        "paper_typed_map_normalize (D (paper_arrow_source f))",
    ])
    book_dir = "theories/base/book_models"
    book_structure = (ROOT / book_dir / "Bacon_Book_Applicative_Structure.thy").read_text(encoding="utf-8")
    raw_structure = book_structure.split("locale book_applicative_structure", 1)[1].split("lemma book_empty_applicative_structure", 1)[0]
    if "domain_nonempty" in raw_structure or "functional" in raw_structure:
        raise AssertionError("Raw book applicative structures must not silently require nonemptiness or Functionality")
    book_environment = (ROOT / book_dir / "Bacon_Book_Environment.thy").read_text(encoding="utf-8")
    environment_clause = book_environment.split("locale book_environment_conditions", 1)[1].split("begin", 1)[0]
    if "named_fv A \\<inter> named_fv B" not in environment_clause or "\\<union>" in environment_clause:
        raise AssertionError("Book Definition 14.13 uses the intersection of free-variable sets")
    if re.search(r"\b(paper_named_bbk_model|paper_db_bbk_structure|bacon_general_model|denote_rename)\b", environment_clause):
        raise AssertionError("Book environment conditions must remain independent of the paper/legacy model interfaces")
    require(f"{book_dir}/Bacon_Book_Language.thy", [
        "definition book_in_language", "named_logical_occurrences A \\<subseteq> \\<Lambda>",
    ])
    theory_source = (ROOT / book_dir / "Bacon_Book_Theory_Derivation.thy").read_text(encoding="utf-8")
    theory_rules = theory_source.split("inductive book_theory_derivable ::", 1)[1].split("lemma book_theory_UI_language", 1)[0]
    constructors = re.findall(r"(?m)^\s*(?:\|\s*)?([A-Za-z_][A-Za-z_0-9]*):", theory_rules)
    if constructors != ["Assumption", "PC1", "PC2", "PC3", "UI", "Beta", "Eta", "MP", "Gen"]:
        raise AssertionError(f"Book theory calculus must retain exactly the printed schemas/rules: {constructors}")
    if "named_raw_beta_eta" in theory_rules or "named_beta_eta_in_language" in theory_rules:
        raise AssertionError("Book primitive conversion axioms use immediate steps, not whole conversion chains")
    require(f"{book_dir}/Bacon_Book_Theory_Derivation.thy", [
        "book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A)",
        "named_compatible_step named_beta_contract A B \\<or> named_compatible_step named_beta_contract B A",
        "named_compatible_step named_eta_contract A B \\<or> named_compatible_step named_eta_contract B A",
    ])
    for filename, judgment, following, expected in (
        ("Bacon_Book_Printed_Theory_Derivation.thy", "book_printed_theory_derivable",
         "lemma book_printed_theory_UI_language",
         ["Assumption", "PC1", "PC2", "PC3", "UI", "Beta", "Eta", "MP", "Gen"]),
        ("Bacon_Book_Primitive_Conjunction_Theory_Derivation.thy", "book_conj_theory_derivable",
         "lemma book_conj_theory_UI_language",
         ["Assumption", "PC1", "PC2", "PC3", "UI", "Beta", "Eta", "MP", "Gen", "AndI", "AndE1", "AndE2"]),
        ("Bacon_Book_Primitive_Disjunction_Theory_Derivation.thy", "book_disj_theory_derivable",
         "lemma book_disj_theory_UI_language",
         ["Assumption", "PC1", "PC2", "PC3", "UI", "Beta", "Eta", "MP", "Gen", "AndI", "AndE1", "AndE2", "OrE", "OrI1", "OrI2"]),
    ):
        text = (ROOT / book_dir / filename).read_text(encoding="utf-8")
        clauses = text.split(f"inductive {judgment} ::", 1)[1].split(following, 1)[0]
        actual = re.findall(r"(?m)^\s*(?:\|\s*)?([A-Za-z_][A-Za-z_0-9]*):", clauses)
        if actual != expected:
            raise AssertionError(f"Independent {judgment} has unexpected rules: {actual}")
        if "named_compatible_step book_printed_beta_contract A B" not in clauses:
            raise AssertionError(f"{judgment} must retain the printed immediate beta guard")
        forbidden = ["book_theory_derivable", "named_alpha", "named_raw_beta_eta",
                     "named_beta_eta_in_language", "book_printed_conversion", "book_source_reduces",
                     "book_conj_encode", "book_formula_valid", "book_full_minimal_model", "book_conjunction_model"]
        if judgment == "book_conj_theory_derivable":
            forbidden.append("book_printed_theory_derivable")
        if judgment == "book_disj_theory_derivable":
            forbidden.extend(["book_conj_theory_derivable", "book_printed_theory_derivable", "book_disj_encode"])
        if re.search(r"\b(" + "|".join(forbidden) + r")\b", clauses):
            raise AssertionError(f"{judgment} must not acquire an encoding, old-theorem, alpha, or semantic rule")
    require(f"{book_dir}/Bacon_Book_Conjunction_Logic.thy", [
        "definition book_conj_higher_order_logic", "definition book_conj_H",
        "book_subst_table_language book_conj_logical_type UNIV", "book_simult_free_for G",
        "book_conj_theory_simultaneous_substitution", "theorem book_conj_H_iff_theory",
    ])
    forbid(f"{book_dir}/Bacon_Book_Conjunction_Logic.thy", [
        r"\b(book_formula_valid|book_conj_canonical_consequence|book_conjunction_model)\b",
    ])
    clause_source = (ROOT / book_dir / "Bacon_Book_Conjunction_Theory_Clauses.thy").read_text(encoding="utf-8")
    native_clauses = clause_source.split("definition book_conj_theory_rules", 1)[1].split("text ", 1)[0]
    if re.search(r"\b(book_conj_theory_derivable|book_theory_derivable|book_conj_encode|book_formula_valid)\b", native_clauses):
        raise AssertionError("Literal conjunction rule clauses must not be defined by derivability, encoding or validity")
    require(f"{book_dir}/Bacon_Book_Conjunction_Theory_Clauses.thy", [
        "theorem book_conj_higher_order_theory_iff_rules",
        "named_compatible_step book_printed_beta_contract A B",
        "book_conj_imp A (book_conj_imp B (book_conj_apply A B))",
    ])
    require(f"{book_dir}/Bacon_Book_Minimal_Formula_Syntax.thy", [
        "book_not G A = NApp (book_not_const G) A",
        "book_not_const G = NLam (book_prop_name G)",
    ])
    require("theories/base/Bacon_Deduction.thy", [
        "inductive H_proves", "IndividualExistence", "H_proves_formula",
    ])
    require("theories/classicism/Bacon_Abbreviations.thy", [
        "bool_comm_conj", "bool_dissolve_disj_conj", "bool_material_imp",
        "classic_identity_identity", "classic_dist_conj_exists",
    ])
    require("theories/classicism/Bacon_Classicism.thy", [
        "inductive C_proves", "BooleanIdentity", "IdentityIdentity",
    ])
    require("theories/classicism/Bacon_Completeness.thy", [
        "definition assumptions_typed", "assumptions_typed \\<Gamma> \\<Delta>",
    ])

    c_dir = "theories/classicism/equivalence_development"
    for path in (ROOT / c_dir).glob("*.thy"):
        relative = str(path.relative_to(ROOT))
        forbid(relative, [r"\bCE_proves\.", r"\bCEV_proves\."])

    h_only_dir = "theories/classicism/h_only_presentations"
    for path in (ROOT / h_only_dir).glob("*.thy"):
        forbid(str(path.relative_to(ROOT)), [
            r"\bC_proves\.", r"\bCE_proves\.", r"\bCEV_proves\.",
        ])
    require(f"{h_only_dir}/Bacon_H_Equivalence_Presentations.thy", [
        "imports Bacon_Base.Bacon_Deduction",
        "inductive HE_proves", "inductive HLE_proves",
    ])
    independent = (ROOT / h_only_dir / "Bacon_H_Equivalence_Presentations.thy").read_text(encoding="utf-8")
    for predicate in ("HE_proves", "HLE_proves"):
        clauses = independent.split(f"inductive {predicate}", 1)[1].split(f"lemma {predicate}_formula", 1)[0]
        constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", clauses, flags=re.MULTILINE)
        equivalence = "LogicalEquivalence" if predicate == "HLE_proves" else "Equivalence"
        if constructors != ["H", equivalence, "MP", "Gen", "Inst"]:
            raise AssertionError(f"Independent {predicate} has unexpected axioms/rules: {constructors}")

    require(f"{c_dir}/Bacon_C_Primitive_Basis.thy", [
        "C_closure_material_imp_instance",
    ])

    bbk_dir = "theories/classicism/bbk_semantics_development"
    require(f"{bbk_dir}/Bacon_BBK_Semantics.thy", [
        "locale bbk_model", "valuation_identity", "denote_application_cong",
    ])
    for path in (ROOT / bbk_dir).glob("*.thy"):
        relative = str(path.relative_to(ROOT))
        forbid(relative, [
            r"^\s*imports[^\n]*Bacon_Semantics",
            r"^\s*(locale|sublocale|interpretation)[^\n]*applicative_structure",
            r"^\s*(fixes|and)\s+truth_den\b",
            r"^\s*(fixes|and)\s+lam_den\b",
        ])

    pbbk = "theories/base/parametric_signature/Bacon_Parametric_BBK_Semantics.thy"
    require(pbbk, [
        "inductive pbeta_eta_equiv_in_signature",
        "locale pbbk_model",
        "pbeta_eta_equiv_in_signature signature",
        "valuation_identity",
    ])
    require(
        "theories/base/parametric_canonical/Bacon_Parametric_BBK_Strong_Completeness.thy",
        [
            "pH_set_BBK_closed_soundness",
            "pH_BBK_closed_countermodel",
            "pH_BBK_closed_strong_completeness",
        ],
    )
    require(
        "theories/base/parametric_countable/Bacon_Parametric_Countable_Model_Existence.thy",
        ["pH_BBK_nat_model_existence", "pH_BBK_nat_closed_countermodel"],
    )
    require("theories/base/source_vocabulary/Bacon_Source_Syntax.thy", [
        "datatype ('c, 'l) sterm",
        "datatype paper_logical",
        "datatype book_minimal_logical",
        "inductive has_stype",
    ])
    source_h_path = "theories/base/source_vocabulary/Bacon_Source_Global_H.thy"
    require(source_h_path, [
        "inductive paper_global_H", "and G :: sgcontext where",
        "paper_global_PC_translation",
    ])
    source_h = (ROOT / source_h_path).read_text(encoding="utf-8")
    rules = source_h.split("inductive paper_global_H", 1)[1].split(
        "lemma paper_global_H_language", 1
    )[0]
    constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", rules, flags=re.MULTILINE)
    expected = ["PC", "UI", "EG", "Ref", "LL", "Beta", "Eta", "MP", "Gen", "Inst"]
    if constructors != expected:
        raise AssertionError(f"Source H must retain exactly Figure 2's ten rules: {constructors}")
    named_h_path = "theories/base/source_vocabulary/Bacon_Source_Named_H.thy"
    named_h = (ROOT / named_h_path).read_text(encoding="utf-8")
    named_rules = named_h.split("inductive paper_named_H", 1)[1].split(
        "lemma paper_named_H_language", 1
    )[0]
    named_constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", named_rules, flags=re.MULTILINE)
    if named_constructors != expected:
        raise AssertionError(f"Named H must retain exactly Figure 2's ten rules: {named_constructors}")
    if re.search(r"\b(paper_global_H|pH_proves|named_valid|paper_db_valid)\b", named_rules):
        raise AssertionError("Named H must not be defined through another proof or validity judgment")
    named_local_rules = named_h.split("inductive paper_named_derivable", 1)[1].split(
        "lemma paper_named_derivable_language", 1
    )[0]
    named_local_constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", named_local_rules, flags=re.MULTILINE)
    if named_local_constructors != ["Assumption", "Theorem", "MP"]:
        raise AssertionError(f"Named local consequence has extra rules: {named_local_constructors}")
    named_pc = (ROOT / "theories/base/source_vocabulary/Bacon_Source_Named_Propositional.thy").read_text(encoding="utf-8")
    named_pc_definition = named_pc.split("definition named_PC", 1)[1].split("lemma named_PC_language", 1)[0]
    if re.search(r"\b(paper_global_PC|paper_global_H|pH_proves|named_valid)\b", named_pc_definition):
        raise AssertionError("Named PC must be defined from native instances, not the encoded target")
    named_consistency = (ROOT / "theories/base/source_vocabulary/Bacon_Source_Named_Consistency_Correspondence.thy").read_text(encoding="utf-8")
    named_consistency_definition = named_consistency.split("definition paper_named_consistent", 1)[1].split(
        "lemma paper_named_consistent_no_pair", 1
    )[0]
    if re.search(r"\b(paper_global_consistent|named_to_source|named_fv|paper_named_sentence_set)\b", named_consistency_definition):
        raise AssertionError("Native consistency must not be translated or restricted to closed witnesses")
    require("theories/base/source_vocabulary/Bacon_Source_Named_Consistency_Correspondence.thy", [
        "paper_named_derivable \\<Sigma> G S A", "paper_named_derivable \\<Sigma> G S (named_paper_not A)",
    ])
    native_completeness = (ROOT / "theories/base/source_models/Bacon_Source_Named_Closed_Strong_Completeness.thy").read_text(encoding="utf-8")
    native_consequence_definition = native_completeness.split("definition paper_named_canonical_consequence", 1)[1].split(
        "lemma paper_named_canonical_consequence_apply", 1
    )[0]
    if re.search(r"\b(named_to_source|named_tag_domain|paper_db_bbk_model|paper_db_bbk_structure|paper_global_H)\b", native_consequence_definition):
        raise AssertionError("Native semantic consequence must range independently over named models")
    for marker in ("\\<forall>D", "\\<forall>J", "\\<forall>V", "paper_named_bbk_model", "named_env_typed"):
        if marker not in native_consequence_definition:
            raise AssertionError(f"Native consequence lacks its independent typed model quantifier: {marker}")
    native_nat = (ROOT / "theories/base/source_models/Bacon_Source_Named_Nat_Strong_Completeness.thy").read_text(encoding="utf-8")
    native_nat_definition = native_nat.split("definition paper_named_nat_consequence", 1)[1].split(
        "lemma paper_named_nat_consequence_apply", 1
    )[0]
    if re.search(r"\b(named_to_source|named_tag_domain|named_image_domain|paper_db_bbk_model|paper_db_bbk_structure)\b", native_nat_definition):
        raise AssertionError("Nat consequence must range over all independent nat-carrier named models")
    for marker in ("\\<forall>D", "\\<forall>J", "\\<forall>V", "nat set", "paper_named_bbk_model", "named_env_typed"):
        if marker not in native_nat_definition:
            raise AssertionError(f"Nat consequence lacks its independent typed model quantifier: {marker}")
    local_path = "theories/base/source_vocabulary/Bacon_Source_Local_Deduction.thy"
    local_text = (ROOT / local_path).read_text(encoding="utf-8")
    local_rules = local_text.split("inductive paper_global_derivable", 1)[1].split(
        "lemma paper_global_derivable_language", 1
    )[0]
    local_constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", local_rules, flags=re.MULTILINE)
    if local_constructors != ["Assumption", "Theorem", "MP"]:
        raise AssertionError(f"Source local consequence must use only assumption/theorem/MP: {local_constructors}")
    require("theories/base/source_vocabulary/Bacon_Source_Global_Existence.thy", [
        "theorem paper_global_type_existence",
        "paper_standard_stock_type_existence",
    ])
    forbid("theories/base/source_vocabulary/Bacon_Source_Global_Existence.thy", [
        r"\bpH_proves\.", r"\bH_proves\.",
    ])
    require("theories/base/source_vocabulary/Bacon_Source_Proof_Correspondence.thy", [
        "theorem paper_global_H_closed_iff", "corollary paper_standard_H_closed_iff",
        "paper_roundtrip_conversion", "pH_closed_to_paper_global_H",
    ])
    interface_path = "theories/base/source_vocabulary/Bacon_Source_BBK_Interface.thy"
    require(interface_path, [
        "locale paper_db_bbk_structure", "locale paper_db_bbk_model",
        "definition paper_db_satisfies", "definition paper_db_valid",
    ])
    interface = (ROOT / interface_path).read_text(encoding="utf-8")
    structure_fields = interface.split("locale paper_db_bbk_structure", 1)[1].split("\nbegin", 1)[0]
    if "denote_rename" in structure_fields:
        raise AssertionError("Source structure must not assume the renaming field whose redundancy is being proved")
    require("theories/base/source_models/Bacon_Source_BBK_Model_Existence.thy", [
        "theorem paper_db_BBK_model_existence",
        "theorem paper_db_BBK_countable_signature_model_existence",
        "pbbk_to_paper_db_model",
    ])
    named_interface_path = "theories/base/source_models/Bacon_Source_Named_BBK_Interface.thy"
    require(named_interface_path, [
        "locale paper_named_bbk_model", "named_raw_beta_eta",
        "H (Arr \\<upsilon> \\<rho>)", "B \\<upsilon>",
        "named_adequate g A", "named_adequate g B",
    ])
    named_interface = (ROOT / named_interface_path).read_text(encoding="utf-8")
    named_fields = named_interface.split("locale paper_named_bbk_model", 1)[1].split("\nbegin", 1)[0]
    labels = re.findall(r"(?:assumes|and)\s+(\w+):\s*\"", named_fields)
    expected_named_fields = ["stock_rich", "domain_nonempty", "denote_type", "denote_var",
        "denote_application_cong", "denote_locality", "denote_beta_eta", "valuation_neg",
        "valuation_conj", "valuation_disj", "valuation_forall", "valuation_exists", "valuation_identity"]
    if labels != expected_named_fields:
        raise AssertionError(f"Independent named model fields changed: {labels}")

    r_interface = (ROOT / action_dir / "Bacon_Source_Relational_BBK_Interface.thy").read_text(encoding="utf-8")
    r_fields = r_interface.split("locale paper_R_bbk_model", 1)[1].split("\nbegin", 1)[0]
    r_labels = re.findall(r"(?:assumes|and)\s+(\w+):\s*\"", r_fields)
    expected_r_fields = expected_named_fields[:2] + ["domain_empty"] + expected_named_fields[2:]
    if r_labels != expected_r_fields:
        raise AssertionError(f"Independent R model fields changed: {r_labels}")
    r_h = (ROOT / action_dir / "Bacon_Source_Relational_H.thy").read_text(encoding="utf-8")
    r_h_rules = r_h.split("inductive paper_R_named_H", 1)[1].split("lemma paper_R_named_H_language", 1)[0]
    r_h_constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", r_h_rules, flags=re.MULTILINE)
    if r_h_constructors != ["PC", "UI", "EG", "Ref", "LL", "Beta", "Eta", "MP", "Gen", "Inst"]:
        raise AssertionError(f"Independent R H must retain the ten source constructors: {r_h_constructors}")
    r_local = (ROOT / action_dir / "Bacon_Source_Relational_Local_Consequence.thy").read_text(encoding="utf-8")
    r_local_rules = r_local.split("inductive paper_R_named_derivable", 1)[1].split("lemma paper_R_named_derivable_language", 1)[0]
    r_local_constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", r_local_rules, flags=re.MULTILINE)
    if r_local_constructors != ["Assumption", "Theorem", "MP"]:
        raise AssertionError(f"R local consequence must not generalize open assumptions: {r_local_constructors}")
    for filename, judgment, endpoint, expected in [
        ("Bacon_Source_Relational_Equivalence_Presentation.thy", "paper_R_equivalence_proves",
         "paper_R_equivalence_proves_language", ["H", "MP", "Gen", "Inst", "Equivalence"]),
        ("Bacon_Source_Relational_Classicism_Presentation.thy", "paper_R_classicism_proves",
         "paper_R_classicism_proves_language", ["H", "Logical_Equivalence", "MP", "Gen", "Inst"]),
    ]:
        source = (ROOT / action_dir / filename).read_text(encoding="utf-8")
        rules = source.split(f"inductive {judgment}", 1)[1].split(f"theorem {endpoint}", 1)[0]
        constructors = re.findall(r"^\s*(?:\|\s*)?(\w+):", rules, flags=re.MULTILINE)
        if constructors != expected:
            raise AssertionError(f"Native R presentation closure changed: {filename}: {constructors}")
        if judgment == "paper_R_classicism_proves":
            le_clause = rules.split("| Logical_Equivalence:", 1)[1].split("| MP:", 1)[0]
            if '"paper_R_named_H ' not in le_clause:
                raise AssertionError("Source Logical Equivalence must use an H certificate, not a C certificate")
    for marker in ("paper_R_rich stock", "paper_R_in_language",
                   "paper_R_raw_beta_eta", "domain_empty", "named_adequate"):
        if marker not in r_fields:
            raise AssertionError(f"Independent R interface lost guard: {marker}")
    # R-to-F syntax embeddings and the one-way reduct are explicit bridges.
    # The remaining independent R semantic leaves must not invoke F model
    # validation. Graph checks separately inspect actual proof dependencies.
    r_bridge_files = {
        "Bacon_Source_Relational_Model_Restriction.thy",
        "Bacon_Source_Relational_Types.thy",
        "Bacon_Source_Relational_Syntax.thy",
        "Bacon_Source_Relational_Conversion.thy",
    }
    for path in (ROOT / action_dir).glob("Bacon_Source_Relational_*.thy"):
        if path.name not in r_bridge_files:
            forbid(str(path.relative_to(ROOT)), [
                r"\bpaper_named_bbk_model\b", r"\bpaper_bbk_data_valid\b",
                r"\bpaper_bbk_model_morphism\b",
            ])
    r_hom_source = (ROOT / action_dir / "Bacon_Source_Relational_Homomorphism.thy").read_text(encoding="utf-8")
    r_hom_clause = r_hom_source.split("definition paper_R_bbk_homomorphism", 1)[1].split("lemma ", 1)[0]
    if re.search(r"\b(valuation|paper_R_bbk_model|paper_named_bbk_model)\b", r_hom_clause):
        raise AssertionError("Raw R homomorphisms must not add model or valuation preservation")

    for directory in [
        ROOT / "theories/base/parametric_signature",
        ROOT / "theories/base/parametric_canonical",
        ROOT / "theories/base/parametric_countable",
        ROOT / "theories/base/source_vocabulary",
        ROOT / "theories/base/source_models",
    ]:
        for path in directory.glob("*.thy"):
            relative = str(path.relative_to(ROOT))
            forbid(relative, [
                r"^\s*imports[^\n]*Goodman",
                r"^\s*imports[^\n]*Bacon_Classicism",
                r"\bCE_proves\.",
                r"\bCEV_proves\.",
            ])

    for directory in [ROOT / "theories/base", ROOT / "theories/classicism"]:
        for path in directory.rglob("*.thy"):
            relative = str(path.relative_to(ROOT))
            forbid(relative, [
                r"^\s*imports[^\n]*goodman",
            ])
    # Proof-hole/trust tokens are checked by check_isabelle_trust.py, which
    # also covers core_audit, embedded ML, and referenced local ML files.
    # Do not restore a line-anchored keyword regex here: it both misses
    # inline commands and mistakes documentation/comments for executable code.

    require("ROOT", [
        "session Bacon_C_Equivalence_Development",
        "session Bacon_C_Presentation_Development",
        "session Bacon_H_Only_Classicism_Development",
        "session Bacon_H_Henkin_Equality_Development",
        "session Bacon_H_Henkin_Substitution_Development",
        "session Bacon_BBK_Semantics_Development",
        "session Bacon_Source_Vocabulary_Development",
        "session Bacon_Parametric_Signature_Development",
        "session Bacon_Parametric_Canonical_Development",
        "session Bacon_Parametric_Countable_Development",
        "session Bacon_Auxiliary_Bridge_Development",
        "session Bacon_Core_Audit_Catalog",
        "session Bacon_Core_Audit_First",
        "session Bacon_Core_Theorem_Audit",
    ])
    audit_headers = (
        'session Bacon_Core_Audit_Catalog in "theories/core_audit/catalog" = Bacon_Book_Environment_Development +',
        'session Bacon_Core_Audit_First in "theories/core_audit/first" = Bacon_Core_Audit_Catalog +',
        'session Bacon_Core_Theorem_Audit in "theories/core_audit" = Bacon_Core_Audit_First +',
    )
    root_source = (ROOT / "ROOT").read_text(encoding="utf-8")
    for header in audit_headers:
        if header not in root_source:
            raise AssertionError(f"Principal audit session chain changed: {header}")
        block = root_source.split(header, 1)[1].split("\nsession ", 1)[0]
        if "options [timeout = 60, export_theory = true]" not in block:
            raise AssertionError(f"Principal audit must retain timeout60/theory exports: {header}")
    require("theories/core_audit/Bacon_Core_Audit_Check.ML", [
        "Thm_Deps.all_oracles", "Thm.hyps_of", "Thm.tpairs_of",
        "Proof_Context.get_thm", "Thm.nprems_of", "Thm.shyps_of",
        "if null collective_oracles then ()", "actual = expected",
        "aggregate index/label/fact coverage mismatch",
        "CORE-PRINCIPAL-THEOREMS-KERNEL-CLEAN",
    ])
    require("theories/core_audit/catalog/Bacon_Core_Audit_Catalog.thy", [
        'ML_file "../Bacon_Core_Audit_Check.ML"',
        "val targets: (string * string) list", "map_index",
        "take first_count indexed_targets", "drop first_count indexed_targets",
    ])
    forbid("theories/core_audit/catalog/Bacon_Core_Audit_Catalog.thy", [r"@\{thm\b"])
    require("theories/core_audit/first/Bacon_Core_Audit_First.thy", [
        "Bacon_Core_Audit_Catalog.Bacon_Core_Audit_Catalog",
        "Bacon_Core_Audit_Check.run", "Bacon_Core_Audit_Catalog.first_targets",
    ])
    require("theories/core_audit/Bacon_Core_Theorem_Audit.thy", [
        "Bacon_Core_Audit_First.Bacon_Core_Audit_First",
        "Bacon_Core_Audit_Check.run", "Bacon_Core_Audit_Catalog.second_targets",
        "Bacon_Core_Audit_First.checked @ second_checked",
        "Bacon_Core_Audit_Check.aggregate Bacon_Core_Audit_Catalog.targets",
        'Path.basic "core-audit.txt"',
    ])

    print("Core source-boundary check passed: H/C markers, full-type MF/PE separation, primitive-basis bridge,")
    print("C-only Equivalence work, exact parametric BBK completeness, countable")
    print("transport, source vocabulary, and auxiliary boundaries are intact.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as error:
        print(f"Core source-boundary check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
