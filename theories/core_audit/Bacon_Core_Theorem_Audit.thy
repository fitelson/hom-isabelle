theory Bacon_Core_Theorem_Audit
  imports Bacon_Core_Audit_First.Bacon_Core_Audit_First
begin

section \<open>Principal core results: complete theorem-object checks\<close>

text \<open>
  The parent catalog retains the complete ordered list of selected H, C,
  source-translation and book endpoints. Its first slice was checked in
  the immediate parent session; this session checks the remaining slice.
  Exact index, label and fact-name coverage is required before exporting
  the unchanged combined principal-audit report.

  Every endpoint must have no oracle dependencies, residual logical kernel
  hypotheses or unresolved flex-flex constraints. Implication premises and
  sort hypotheses are reported, not silently discharged. Passing this
  audit does not remove mathematical premises or establish source fidelity.
  Each session retains its 60-second timeout and theory exports.
\<close>

ML \<open>
local
  val second_checked = Bacon_Core_Audit_Check.run @{context} "second"
    Bacon_Core_Audit_Catalog.second_targets
  val all_checked = Bacon_Core_Audit_First.checked @ second_checked
  val report = Bacon_Core_Audit_Check.timed "aggregate" "coverage/report"
    (Bacon_Core_Audit_Check.aggregate Bacon_Core_Audit_Catalog.targets) all_checked
  val _ = Bacon_Core_Audit_Check.timed "aggregate" "export"
    (fn () => Export.export @{theory}
      (Path.binding0 (Path.basic "core-audit.txt")) [XML.Text report]) ()
in
  val _ = writeln report
end
\<close>

end
