"""Lexical regressions use strings, never admitted Isabelle theory fixtures."""

from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_isabelle_trust as trust


class OuterSyntaxTests(unittest.TestCase):
    def assert_clean(self, source):
        self.assertEqual(trust.inspect_theory(source)[0], [])

    def assert_rejected(self, source, expected):
        issues = trust.inspect_theory(source)[0]
        self.assertTrue(any(expected in message for _, message in issues), issues)

    def test_inline_and_multiline_proof_holes(self):
        for keyword in sorted(trust.FORBIDDEN_OUTER):
            for separator in (" ", "\n", " (* explanation (* nested *) *) "):
                with self.subTest(keyword=keyword, separator=separator):
                    self.assert_rejected(f'lemma probe: "True"{separator}{keyword}', keyword)

    def test_schematic_oracle_command_and_options(self):
        self.assert_rejected('oracle trust = ‹fn _ => @{prop True}›', "oracle")
        self.assert_rejected('declare [[quick_and_dirty = true]]', "quick_and_dirty")
        self.assert_rejected('session X = HOL + options [quick_and_dirty = true]', "quick_and_dirty")

    def test_proof_symbol_alias_of_sorry(self):
        self.assert_rejected(r'lemma x: "True" \<proof>', r"\<proof>")
        self.assert_clean('lemma x: "True" proof - show ?thesis by simp qed')
        self.assert_clean(r'text \<open>\<proof>\<close> lemma x: "True" by simp')

    def test_real_proofs_and_similar_identifiers(self):
        self.assert_clean('lemma sorry_free: "True" by simp\nlemmas oracle_free = sorry_free')
        self.assert_clean('lemma sample: ‹True› by simp')
        self.assert_clean('definition axioms_count where "axioms_count = (0::nat)"')

    def test_locale_axioms_fact_and_local_binding_are_not_commands(self):
        self.assert_clean('by (rule model.axioms(1)[OF model])')
        self.assert_clean('obtain T where keeps: "P T" and axioms: "Q T" by blast')
        self.assert_rejected('by simp . sorry', "sorry")
        self.assert_rejected('lemma probe: "True" by simp axioms inconsistent: "False"', "axioms")

    def test_comments_including_nested_comments(self):
        self.assert_clean('(* sorry (* axiomatization oracle *) quick_and_dirty *)\nlemma x: "True" by simp')
        self.assert_rejected('(* sorry (* oracle *) *) lemma x: "True" sorry', "sorry")

    def test_escaped_quoted_terms(self):
        self.assert_clean(r'lemma x: "P \"sorry\"" by simp')
        self.assert_rejected(r'lemma x: "P \"sorry\"" sorry', "sorry")
        self.assert_clean('text "sorry oops axioms oracle quick_and_dirty"')

    def test_prose_cartouches_unicode_and_symbol_spelling(self):
        for opening, closing in (("‹", "›"), (r"\<open>", r"\<close>")):
            for command in sorted(trust.PROSE):
                self.assert_clean(f'{command} {opening}sorry oracle Skip_Proof.cheat_tac {closing}')

    def test_nested_cartouches_and_document_comments(self):
        self.assert_clean(r'text \<open>outer ‹Skip_Proof.cheat_tac› sorry\<close>')
        for comment in ("--", "―", r"\<comment>"):
            self.assert_clean(f'by simp {comment} ‹Skip_Proof.cheat_tac, oracle, sorry›')

    def test_post_prose_commands_are_not_hidden(self):
        self.assert_rejected('text ‹sorry› lemma x: "True" sorry', "sorry")
        self.assert_rejected('text ‹ML is discussed› ML ‹Skip_Proof.cheat_tac @{context}›', "Skip_Proof")

    def test_ml_document_antiquotations_need_review(self):
        self.assert_rejected('text ‹@{ML_val ‹Skip_Proof.cheat_tac›}›', "ML document antiquotation")
        self.assert_rejected(r'text ‹\<^ML>‹Thm.add_axiom››', "ML document antiquotation")
        self.assert_clean('text ‹We use ML, Skip_Proof and @{thm TrueI} as words or fact references.›')

    def test_unclosed_or_unmatched_lexical_regions_fail(self):
        for source in ('(* comment', 'text "unfinished', 'text ‹unfinished', r'text \<open>unfinished',
                       '*) lemma x: "True" by simp', '›'):
            with self.subTest(source=source):
                self.assertTrue(trust.inspect_theory(source)[0])

    def test_locations_follow_original_lines(self):
        source = 'text ‹sorry\n(* prose *)›\nlemma x: "True" sorry'
        offset, message = trust.inspect_theory(source)[0][0]
        self.assertEqual(source.count("\n", 0, offset) + 1, 3)
        self.assertIn("sorry", message)


class MLTests(unittest.TestCase):
    def test_all_policy_identifiers_are_rejected(self):
        for name in sorted(trust.FORBIDDEN_ML):
            with self.subTest(name=name):
                self.assertTrue(trust.inspect_ml(f'val bypass = Module.{name};'))

    def test_qualified_names_with_whitespace_and_nested_comments(self):
        self.assertTrue(trust.inspect_ml('val bad = Skip_Proof (* outer (* inner *) *) . cheat_tac;'))
        self.assertTrue(trust.inspect_ml('val bad = Thm\n.\nadd_axiom;'))
        self.assertTrue(trust.inspect_ml('open Skip_Proof; val bad = cheat_tac;'))

    def test_ml_strings_and_comments_are_not_executable(self):
        self.assertEqual(trust.inspect_ml('val report = "Skip_Proof.cheat_tac, add_axiom";'), [])
        self.assertEqual(trust.inspect_ml('(* Thm.add_oracle (* skip_proof *) *) val x = 1;'), [])
        self.assertEqual(trust.inspect_ml(r'val s = "say \"Skip_Proof.cheat_tac\"";'), [])

    def test_existing_audit_style_is_accepted(self):
        self.assertEqual(trust.inspect_ml('''
          val targets = [("no oracle dependencies", "a.theorem")];
          val facts = map (Proof_Context.get_thm @{context} o #2) targets;
          val dependencies = Thm_Deps.all_oracles facts;
          val premises = map Thm.nprems_of facts;
          val _ = Export.export @{theory} (Path.binding0 (Path.basic "audit.txt")) [];
        '''), [])

    def test_embedded_ml_cartouches_and_quoted_bodies(self):
        for command in ("ML", "ML_val", "ML_prf", "ML_command", "setup", "local_setup"):
            for body in ('‹Skip_Proof.cheat_tac›', r'\<open>Thm.add_axiom\<close>', '"Thm.add_oracle"'):
                with self.subTest(command=command, body=body):
                    self.assertTrue(trust.inspect_theory(f'{command} {body}')[0])

    def test_methods_and_antiquotation_cartouches(self):
        self.assertTrue(trust.inspect_theory('by (tactic ‹Skip_Proof.cheat_tac @{context}›)')[0])
        self.assertTrue(trust.inspect_theory('method_setup bad = ‹fn _ => Thm.add_axiom› "description"')[0])
        self.assertTrue(trust.inspect_theory('ML ‹val bad = @{ML ‹Skip_Proof.cheat_tac›}›')[0])
        self.assertTrue(trust.inspect_theory('method_setup text = ‹fn _ => Thm.add_axiom› "description"')[0])

    def test_ml_quoted_strings_in_cartouches_remain_opaque(self):
        self.assertEqual(trust.inspect_theory('ML ‹val s = "Thm.add_oracle";›')[0], [])
        self.assertEqual(trust.inspect_theory(r'ML "val s = \"Thm.add_oracle\";"')[0], [])

    def test_dynamic_evaluation_and_command_registration_policy(self):
        for source in ('ML_Context.eval_source flags text', 'ML_Compiler.eval flags pos text',
                       'use "unreviewed.ML"', 'PolyML.Compiler.compiler input options',
                       'Outer_Syntax.command name description parser'):
            self.assertTrue(trust.inspect_ml(source))

    def test_literal_quick_and_dirty_option_setters(self):
        for source in ('Options.put_bool "quick_and_dirty" true opts',
                       'Options.put_bool (* comment *) "quick_and_dirty" true opts'):
            self.assertTrue(trust.inspect_ml(source))
        self.assertEqual(trust.inspect_ml('val report = "quick_and_dirty";'), [])

    def test_lexical_scope_limit_is_explicit(self):
        # Aliases or code assembled elsewhere cannot be resolved lexically.
        self.assertEqual(trust.inspect_ml('val result = unknown_function ctxt;'), [])


class FilePolicyTests(unittest.TestCase):
    ROOT = Path(__file__).resolve().parents[2]

    def test_literal_ml_references(self):
        for command in sorted(trust.ML_FILES):
            issues, references = trust.inspect_theory(f'{command} "../audit.ML"')
            self.assertEqual(issues, [])
            self.assertEqual(references[0][1], '../audit.ML')
        for source in ('ML_file audit.ML', 'ML_file ‹audit.ML›', 'ML_file'):
            self.assertTrue(trust.inspect_theory(source)[0])

    def test_documentation_does_not_create_file_references(self):
        self.assertEqual(trust.inspect_theory('text ‹ML_file "missing.ML"›'), ([], []))

    def test_repository_scope_includes_core_audit_ml_and_root(self):
        files = trust.source_files(self.ROOT)
        self.assertIn(self.ROOT / 'ROOT', files)
        self.assertIn(self.ROOT / 'theories/core_audit/Bacon_Core_Audit_Check.ML', files)
        self.assertIn(self.ROOT / 'theories/core_audit/Bacon_Core_Theorem_Audit.thy', files)

    def check_virtual(self, sources):
        # All dangerous fixture text lives in memory. No .thy files are made.
        with patch.object(trust, 'source_files', return_value=list(sources)), \
             patch.object(Path, 'read_text', lambda path, **kwargs: sources[path]), \
             patch.object(Path, 'is_file', lambda path: path in sources):
            return trust.check_repository(self.ROOT)

    def test_core_audit_unused_inline_hole_is_rejected(self):
        path = self.ROOT / 'theories/core_audit/Virtual.thy'
        count, issues = self.check_virtual({path: 'lemma unused: "True" sorry'})
        self.assertEqual(count, 1)
        self.assertIn('forbidden Isabelle trust token: sorry', issues[0])

    def test_standalone_ml_is_checked(self):
        path = self.ROOT / 'theories/core_audit/Virtual.ML'
        _, issues = self.check_virtual({path: 'val result = Thm.add_axiom x;'})
        self.assertTrue(issues)

    def test_references_outside_repository_and_missing_paths_are_rejected(self):
        path = self.ROOT / 'theories/core_audit/Virtual.thy'
        for name in ('/not-in-this-repository/a.ML', '../../../escape.ML', 'missing.ML', '$ISABELLE_HOME/a.ML'):
            _, issues = self.check_virtual({path: f'ML_file "{name}"'})
            self.assertTrue(issues, name)

    def test_referenced_local_ml_outside_theories_is_checked(self):
        theory = self.ROOT / 'theories/core_audit/Virtual.thy'
        ml = self.ROOT / 'tools/Virtual.ML'
        sources = {theory: 'ML_file "../../tools/Virtual.ML"', ml: 'val bad = Thm.add_oracle;'}
        with patch.object(trust, 'source_files', return_value=[theory]), \
             patch.object(Path, 'read_text', lambda path, **kwargs: sources[path]), \
             patch.object(Path, 'is_file', lambda path: path in sources):
            count, issues = trust.check_repository(self.ROOT)
        self.assertEqual(count, 2)
        self.assertTrue(any('add_oracle' in issue for issue in issues))


if __name__ == '__main__':
    unittest.main()
