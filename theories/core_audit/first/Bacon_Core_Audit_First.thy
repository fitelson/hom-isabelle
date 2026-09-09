theory Bacon_Core_Audit_First
  imports Bacon_Core_Audit_Catalog.Bacon_Core_Audit_Catalog
begin

section \<open>The first disjoint slice of principal theorem objects\<close>

text \<open>
  Resolve the first catalog slice in the completed parent import context.
  A single oracle-union traversal certifies that slice; residual hypotheses
  and flex-flex constraints are checked individually. The verified records
  are inherited by the final session, not read from an external report.
\<close>

ML \<open>
structure Bacon_Core_Audit_First =
struct
  val checked = Bacon_Core_Audit_Check.run @{context} "first"
    Bacon_Core_Audit_Catalog.first_targets
  val report = "CORE-AUDIT-FIRST-KERNEL-CLEAN: "
    ^ string_of_int (length checked) ^ " checked endpoints\n"
    ^ cat_lines (map Bacon_Core_Audit_Check.checked_report checked) ^ "\n"
  val _ = Bacon_Core_Audit_Check.timed "first" "export"
    (fn () => Export.export @{theory}
      (Path.binding0 (Path.basic "core-audit-part-1.txt")) [XML.Text report]) ()
end
\<close>

end
