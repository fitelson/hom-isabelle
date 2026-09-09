theory Bacon_Book_Combinator_Syntax_Audit
  imports Bacon_Book_Canonical_Combinator_Syntax
begin

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the canonical k lambda term is closed and has every required full type", "book_canonical_K_closed_terms"),
    ("the canonical s lambda term is closed and has every required full type", "book_canonical_S_closed_terms")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-combinator-syntax"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL; no HOL-ZF import\n"
    ^ "SCOPE: typed closed canonical k/s syntax; no modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-combinator-syntax-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  These checks concern the actual canonical witnesses. Implication
  retains its explicitly documented future restriction; no equality
  with the raw printed W-complement is asserted. The complete
  independent modal-model certificate and C soundness/completeness
  remain separate. No oracle or residual kernel obligation is accepted.
\<close>

end
