theory Bacon_H_BBK_Audit
  imports Bacon_H_BBK_Countable_Completeness Bacon_H_BBK_Countable_Arbitrary_Model
    Bacon_H_BBK_Countable_Model
    Bacon_H_BBK_Canonical_Development.Bacon_H_BBK_Completeness
    Bacon_H_BBK_Strong_Completeness_Development.Bacon_H_Arbitrary_Henkin
    Bacon_H_BBK_Strong_Completeness_Development.Bacon_H_Arbitrary_Model
    Bacon_H_BBK_Strong_Completeness_Development.Bacon_H_Signature_Renaming
    Bacon_BBK_Semantics_Development.Bacon_BBK_H_Soundness_Quantifiers
    Bacon_H_Henkin_Substitution_Development.Bacon_H_Henkin_Substitution
begin

ML_file "../../core_audit/Bacon_Core_Audit_Check.ML"

text \<open>
  Theorem-object audit of the older represented H--BBK development: exact
  H soundness at the universal signature, canonical closed-term BBK
  completeness, arbitrary-theory Henkinization and model existence, the
  natural-number transport, and the Henkin substitution congruences. These
  endpoints are distinct from the parametric pH_BBK_* and paper_named_*
  targets of the core catalog; the sessions are retained as checked
  results, not as dependencies of the parametric development.
\<close>

ML \<open>
local
  val targets =
   [("exact H derivations at the universal signature are valid in context in every BBK model", "bbk_model.H_BBK_soundness_universal_signature"),
    ("exact H theorems are closed-valid in every BBK model on every carrier", "H_BBK_closed_soundness"),
    ("closed non-theorems of H have a BBK countermodel on the canonical closed-term carrier", "H_BBK_closed_countermodel"),
    ("closed BBK validity on the canonical carrier is exactly H theoremhood", "H_BBK_closed_valid_iff_proves"),
    ("closed validity on the canonical carrier gives closed validity on every carrier", "H_BBK_closed_valid_every_carrier"),
    ("every consistent typed theory has a Henkin extension containing its renamed premises", "H_arbitrary_Henkin_extension_exists"),
    ("every consistent closed-context typed theory has a BBK model on the canonical carrier", "H_arbitrary_BBK_model_exists"),
    ("renaming the original constants preserves and reflects H consistency", "H_original_theory_consistent_iff"),
    ("the natural-number transport of the closed Henkin canonical structure is a BBK model", "H_closed_Henkin.H_BBK_nat_model"),
    ("closed non-theorems of H have a BBK countermodel on subsets of the natural numbers", "H_BBK_nat_closed_countermodel"),
    ("closed BBK validity on the natural numbers is exactly H theoremhood", "H_BBK_nat_closed_valid_iff_proves"),
    ("closed validity on the natural numbers gives closed validity on every carrier", "H_BBK_nat_closed_valid_every_carrier"),
    ("every consistent closed-context typed theory has a BBK model on subsets of the natural numbers", "H_arbitrary_nat_BBK_model_exists"),
    ("simultaneous substitution is a congruence for H term equality", "H_closed_Henkin.H_term_eq_subst_cong"),
    ("simultaneous substitution is a congruence for H term classes", "H_closed_Henkin.H_term_class_subst_cong")]
  val checked = Bacon_Core_Audit_Check.run @{context} "h-bbk"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL\n"
    ^ "SCOPE: the older represented H--BBK development (exact H, the represented BBK model class with universal signature, canonical closed-term carrier h_bbk_value and its natural-number transport, closed theoremhood and closed-context theories); distinct from the parametric pH_BBK_* and paper_named_* endpoints of the core catalog; no Classicism or modal claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "h-bbk-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
