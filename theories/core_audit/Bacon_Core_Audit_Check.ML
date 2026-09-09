(* Shared theorem-object checks for the serialized principal audit.
   Catalogs contain names only; each child resolves and checks its own slice. *)
structure Bacon_Core_Audit_Check =
struct
  type target = int * string * string
  type checked = {index: int, label: string, fact: string, report: string}

  fun timed stage phase f x =
    let
      val (timing, result) = Timing.timing f x
      val _ = writeln ("CORE-AUDIT-STAGE-TIMING: " ^ stage ^ "/" ^ phase
        ^ ": " ^ Timing.message timing)
    in result end

  fun run ctxt stage (targets: target list): checked list =
    let
      fun resolve (index, label, fact) =
        (index, label, fact, Proof_Context.get_thm ctxt fact)
      val resolved = timed stage "resolve" (map resolve) targets
      val collective_oracles = timed stage "oracles"
        (fn entries => Thm_Deps.all_oracles
          (map (fn (_, _, _, theorem) => theorem) entries)) resolved
      val _ =
        if null collective_oracles then ()
        else error ("CORE-THEOREM-AUDIT-FAILED: " ^ stage ^ ": "
          ^ string_of_int (length collective_oracles)
          ^ " oracle dependencies across selected endpoints")

      fun check (index, name, fact, theorem) =
        let
          val oracles = collective_oracles
          val hypotheses = Thm.hyps_of theorem
          val constraints = Thm.tpairs_of theorem
          val report = name ^ ": oracles=" ^ string_of_int (length oracles)
            ^ " residual_hyps=" ^ string_of_int (length hypotheses)
            ^ " flex_flex=" ^ string_of_int (length constraints)
            ^ " statement_premises=" ^ string_of_int (Thm.nprems_of theorem)
            ^ " sort_hyps=" ^ string_of_int (length (Thm.shyps_of theorem))
        in
          if null oracles andalso null hypotheses andalso null constraints
          then {index = index, label = name, fact = fact, report = report}
          else error ("CORE-THEOREM-AUDIT-FAILED: " ^ report)
        end
      val checked = timed stage "kernel-fields" (map check) resolved
      val _ = writeln ("CORE-AUDIT-STAGE-CLEAN: " ^ stage ^ ": "
        ^ string_of_int (length checked) ^ " checked endpoints")
    in checked end

  fun checked_key ({index, label, fact, ...}: checked) = (index, label, fact)
  fun checked_report ({report, ...}: checked) = report

  fun aggregate (targets: (string * string) list) (checked: checked list) =
    let
      val expected = map_index (fn (index, (label, fact)) => (index, label, fact)) targets
      val actual = map checked_key checked
      val _ =
        if not (null targets) andalso actual = expected then ()
        else error ("CORE-THEOREM-AUDIT-FAILED: aggregate index/label/fact coverage mismatch")
    in
      "CORE-PRINCIPAL-THEOREMS-KERNEL-CLEAN: "
        ^ string_of_int (length targets) ^ " checked endpoints\n"
        ^ cat_lines (map checked_report checked) ^ "\n"
    end
end
