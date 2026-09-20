theory Goodman_General_M1_Native_Semantics_Audit
  imports Goodman_General_M1_Native_Semantics
begin

ML \<open>
local
  val names = [
    "gi_M1_book_model.gi_book_Pure_constant",
    "gi_M1_book_model.gi_book_Fun_constant",
    "gi_M1_book_model.gi_book_pure_truth",
    "gi_M1_book_model.gi_book_fun_truth",
    "gi_M1_book_model.gi_book_unary_application",
    "gi_M1_book_model.gi_book_fn59_liar_clause",
    "gi_M1_book_model.gi_book_QSS_clause",
    "gi_M1_book_model.gi_book_unique_fundamental_clause",
    "gi_M1_book_model.gi_book_fn59_liar_member",
    "gi_M1_book_model.gi_book_fn59_diagonal_contradiction",
    "gi_M1_book_model.gi_book_native_fn59_contradiction",
    "gi_M1_book_model.gi_book_fn59_from_native_extension_soundness"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 12 then () else error "general-M1: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "general-M1: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("general-M1: residual obligations in " ^ name)
  val report = "GENERAL-M1-NATIVE-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Arbitrary-carrier full minimal book models, rich variable stock and typed named assignment. Actual native liar, QSS and unique-fundamentality evaluation; Leibniz congruence and proposition truth agreement derived from the independent model interface. No exact-tree restriction or assumed semantic diagonal. C+[T] soundness is explicitly retained only in the final corollary; Pure(Fun) remains in its native purity stock. No PP-alone contradiction.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "general-M1-native-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "general-M1-native-statements.txt")) [XML.Text statements]
in end
\<close>

end
