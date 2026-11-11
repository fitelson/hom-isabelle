theory Goodman_PP_Refutation_Audit
  imports Goodman_PP_Refutation_Packaging
begin

text \<open>
  Audit of the formalization of the note "Purity of Pure and Recombination"
  (\<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>).

  1. ENDPOINTS, in the order of the note (objects, Lemmas 1-6, Theorem 1),
     followed by the packaging endpoints, which are beyond the note.  The
     build fails if any endpoint depends on an oracle (this includes skipped
     proofs) or has residual hypotheses or flex-flex pairs.

  2. PROVENANCE.  The proof dependencies of the endpoints are traversed
     through all project theories (Bacon*, Goodman*), down to the theorems
     of the Isabelle/HOL library.  Call a theorem EXPLOSIVE if its conclusion
     is a refutation (a derivation of \<open>ObjFalse\<close> in one of the object
     calculi, or of \<open>book_bottom\<close> in the native calculus) and none of its
     premises is itself a derivation judgement: that is, it refutes a stock
     outright, as the T6 and M5 endpoints of this application do.  The build
     fails if
       (a) any endpoint of the note (Lemmas 1-6, Theorem 1) depends on an
           explosive theorem, or
       (b) a packaging endpoint depends on an explosive theorem other than
           the packaging refutations proved in
           \<open>Goodman_PP_Refutation_Packaging\<close> itself.
     So the refutation comes from the note's argument and not from an
     imported refutation of some auxiliary stock.

  3. STOCK USE.  The build also fails unless: the endpoints of Lemmas 1-3 do
     not depend on the rule \<open>CEV_axiom_proves.Axiom\<close> (no added axiom is
     used); the endpoints of Lemmas 4-5 do not depend on \<open>gr_Th_PP\<close>; the
     first two assertions of Theorem 1 depend on \<open>gr_Th_PP\<close> and on
     \<open>CEV_axiom_necessitation\<close> but not on unary Recombination.

  Exports: \<open>pp-refutation-audit.txt\<close> and \<open>pp-refutation-statements.txt\<close>.
\<close>

ML \<open>
local
  val thy = @{theory}
  val ctxt = @{context}
  fun get name = Proof_Context.get_thm ctxt name

  val note_groups = [
    ("OBJECTS (1)-(3), g: closed logical terms",
      ["gr_Sigma_logical", "gr_L_logical", "gr_g_logical"]),
    ("LEMMA 1: (4), (5), (6), (7)",
      ["gr_Lemma1_4", "gr_Lemma1_5", "gr_Lemma1_6", "gr_Lemma1_7", "gr_Lemma1_7_closure"]),
    ("LEMMA 2: (8), (9), (10), (11); Pre(L), Pre(Sigma L)",
      ["gr_Lemma2_8", "gr_Lemma2_9", "gr_Lemma2_10", "gr_Lemma2_11", "gr_Lemma2_inst",
       "gr_Lemma2_SigmaL_sub_L", "gr_Lemma2_Pre_L", "gr_Lemma2_Pre_SigmaL",
       "gr_Lemma2_L_sub_SigmaL"]),
    ("LEMMA 3: closure of q -> Lq; Lq; g(~q) = ~q; g r = q",
      ["gr_Lemma3_closure", "gr_Lemma3_Lq", "gr_Lemma3_Lnq", "gr_Lemma3_Lnq_top",
       "gr_Lemma3_g_neg_q", "gr_Lemma3_g_r"]),
    ("STAGE OBJECTS: M closed and logical; the stock",
      ["gr_M_logical", "gr_T0_purity", "gr_T0_application", "gr_Th_PP"]),
    ("LEMMA 4: Stage is closed; induction",
      ["gr_Lemma4_Stage_Kbot", "gr_Lemma4_Stage_Sigma", "gr_Lemma4_Stage_union",
       "gr_Lemma4_Stage_closed", "gr_Lemma4_Cl_W", "gr_Lemma4_induction",
       "gr_Lemma4_induction_forall"]),
    ("LEMMA 5: (14), (15)",
      ["gr_Lemma5_14", "gr_Lemma5_14_at", "gr_Lemma5_15"]),
    ("LEMMA 6: M(Pure) = P; Pure(P); Stage(P); (16); box (16); L sub P",
      ["gr_Lemma6_M_Pure_eq_P", "gr_Lemma6_Pure_M", "gr_Lemma6_Pure_P",
       "gr_Lemma6_Stage_sub_P", "gr_Lemma6_SCov_P", "gr_Lemma6_Stage_P",
       "gr_Lemma6_Stage_SigmaP", "gr_Lemma6_16", "gr_Lemma6_box_16", "gr_Lemma6_Pre_P",
       "gr_Lemma6_L_sub_P", "gr_Lemma6_L_in_P"]),
    ("THEOREM 1, objects: D+, D- closed and logical; instances of fun' and of unary Recombination",
      ["gr_Dplus_logical", "gr_Dminus_logical", "gr_fun_prime_inst",
       "gr_unary_recombination_inst"]),
    ("THEOREM 1: purity of X+, X-; the two cases; no r satisfies (R)",
      ["gr_Theorem1_Pure_Xplus", "gr_Theorem1_Pure_Xminus", "gr_Theorem1_case1",
       "gr_Theorem1_case2", "gr_Theorem1_cases", "gr_Theorem1_R_at", "gr_Theorem1_R"]),
    ("THEOREM 1, first consequence: no fun' proposition",
      ["gr_Theorem1_funp_R", "gr_Theorem1_funp_at", "gr_Theorem1_funp"]),
    ("THEOREM 1, second consequence: with unary Recombination, no fundamental proposition",
      ["gr_Theorem1_Fun_R", "gr_Theorem1_Fun_at", "gr_Theorem1_Fun"])]

  val packaging_groups = [
    ("PACKAGING (BEYOND THE NOTE): stocks",
      ["gr_Th_eq_T6_core", "gr_Th_sub_recombination"]),
    ("PACKAGING (BEYOND THE NOTE): constructor calculus",
      ["gr_T6_core_no_fun_prime", "gr_recombination_PP_refutation",
       "gr_full_QLN_PP_refutation", "gr_recombination_question_negative",
       "gr_full_QLN_question_negative"]),
    ("PACKAGING (BEYOND THE NOTE): native Goodman book calculus",
      ["gr_native_recombination_PP_refutation", "gr_native_recombination_PP_inconsistent",
       "gr_native_QLN_PP_refutation", "gr_native_QLN_PP_inconsistent",
       "gr_native_T6_core_no_fun_prime"])]

  val note_names = maps snd note_groups
  val packaging_names = maps snd packaging_groups
  val all_names = note_names @ packaging_names
  val all_facts = map get all_names

  (* 1. kernel fields *)
  val _ = if null (Thm_Deps.all_oracles all_facts) then ()
    else error "pp-refutation audit: oracle dependency"
  fun check name =
    let val thm = get name in
      if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
      then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
        string_of_int (Thm.nprems_of thm)
      else error ("pp-refutation audit: residual obligations in " ^ name)
    end
  fun statement name =
    name ^ ":\n" ^ XML.content_of (YXML.parse_body
      (Syntax.string_of_term ctxt (Thm.prop_of (get name))))
  fun rows (title, ns) = "== " ^ title ^ "\n" ^ cat_lines (map check ns) ^ "\n"
  fun statements (title, ns) = "== " ^ title ^ "\n" ^ cat_lines (map statement ns) ^ "\n"

  (* 2. provenance: traversal of proof dependencies *)
  fun node_name (i, node) =
    (case Global_Theory.lookup_thm_id thy (Proofterm.thm_id (i, node)) of
      SOME ((name, _), _) => SOME name
    | NONE => NONE)
  (* Theorems of the Isabelle/HOL library cannot depend on project theorems, so the
     traversal does not descend below a named theorem of a non-project theory. *)
  fun project name =
    let val q = Long_Name.qualifier name in
      String.isPrefix "Bacon" q orelse String.isPrefix "Goodman" q
    end
  fun visit f (i, node) (seen, acc) =
    if Inttab.defined seen i then (seen, acc)
    else
      let
        val seen' = Inttab.update (i, ()) seen
        val acc' = f (i, node) acc
        val descend = (case node_name (i, node) of SOME name => project name | NONE => true)
      in
        if descend then fold (visit f) (Proofterm.thm_node_thms node) (seen', acc')
        else (seen', acc')
      end
  fun deps_fold f thms acc =
    fold (fold (visit f) o Thm.thm_deps) thms (Inttab.empty, acc)

  fun strip_alls (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t)) = strip_alls t
    | strip_alls t = t
  val judgements = ["CEV_axiom_proves", "CEV_axiom_from", "CEV_proves", "CEV_from",
    "CEV_set_derivable", "CE_proves", "C_proves", "H_proves", "H_derivable",
    "goodman_book_proves"]
  fun judgement t =
    (case t of
      Const (\<^const_name>\<open>Trueprop\<close>, _) $ u =>
        (case strip_comb u of
          (Const (c, _), args) =>
            if member (op =) judgements (Long_Name.base_name c) andalso not (null args)
            then SOME (List.last args) else NONE
        | _ => NONE)
    | _ => NONE)
  fun is_false (Const (d, _)) = Long_Name.base_name d = "ObjFalse"
    | is_false (Const (d, _) $ _) = Long_Name.base_name d = "book_bottom"
    | is_false _ = false
  fun explosive prop =
    let
      val t = strip_alls prop
      val concl = Logic.strip_imp_concl t
      val prems = map (Logic.strip_imp_concl o strip_alls) (Logic.strip_imp_prems t)
    in
      (case judgement concl of
        SOME a => is_false a andalso not (exists (is_some o judgement) prems)
      | NONE => false)
    end

  fun collect (i, node) (names, expl) =
    (case node_name (i, node) of
      SOME name =>
        (name :: names,
         if explosive (Proofterm.thm_node_prop node) then name :: expl else expl)
    | NONE => (names, expl))
  fun analyse names =
    let val (seen, (ns, expl)) = deps_fold collect (map get names) ([], [])
    in (Inttab.size seen, sort_distinct string_ord ns, sort_distinct string_ord expl) end

  val (n_note, deps_note, expl_note) = analyse note_names
  val (n_pack, deps_pack, expl_pack) = analyse packaging_names

  val _ = if null expl_note then ()
    else error ("pp-refutation audit: an endpoint of the note depends on an explosive theorem: " ^
      commas expl_note)
  val own = ["gr_recombination_PP_refutation", "gr_full_QLN_PP_refutation",
    "gr_native_recombination_PP_refutation", "gr_native_QLN_PP_refutation"]
  val foreign = filter_out (fn n => member (op =) own (Long_Name.base_name n)) expl_pack
  val _ = if null foreign then ()
    else error ("pp-refutation audit: packaging depends on a foreign explosive theorem: " ^
      commas foreign)

  (* 3. stock use *)
  fun reaches names target =
    let val (_, deps, _) = analyse names
    in exists (fn n => n = target orelse String.isSuffix ("." ^ target) n) deps end
  fun expect b names target =
    if reaches names target = b then
      (if b then "depends on " else "does not depend on ") ^ target
    else error ("pp-refutation audit: stock-use check failed for " ^ target ^
      " (expected " ^ (if b then "a dependency" else "no dependency") ^ ")")
  val l123 = maps snd (take 4 note_groups)
  val l45 = maps snd (take 2 (drop 5 note_groups))
  val thm1 = ["gr_Theorem1_R", "gr_Theorem1_funp"]
  val stock_report = cat_lines [
    "STOCK-USE: Lemmas 1-3 (and objects): " ^ expect false l123 "CEV_axiom_proves.Axiom",
    "STOCK-USE: Lemmas 4-5: " ^ expect false l45 "gr_Th_PP",
    "STOCK-USE: Lemmas 4-5: " ^ expect true l45 "CEV_axiom_proves.Axiom",
    "STOCK-USE: gr_Theorem1_R, gr_Theorem1_funp: " ^ expect true thm1 "gr_Th_PP",
    "STOCK-USE: gr_Theorem1_R, gr_Theorem1_funp: " ^ expect true thm1 "CEV_axiom_necessitation",
    "STOCK-USE: gr_Theorem1_R, gr_Theorem1_funp: " ^
      expect false thm1 "gr_unary_recombination_inst",
    "STOCK-USE: gr_Theorem1_Fun: " ^ expect true ["gr_Theorem1_Fun"] "gr_unary_recombination_inst",
    "STOCK-USE: gr_native_recombination_PP_refutation: " ^
      expect true ["gr_native_recombination_PP_refutation"] "gr_Theorem1_Fun"]

  fun imported n =
    let val q = Long_Name.qualifier n in
      not (String.isPrefix "Goodman_PP_Refutation" q) andalso
      (String.isPrefix "Bacon_PP" q orelse String.isPrefix "Goodman" q orelse
       String.isPrefix "Bacon_CEV_Axiom" q)
    end
  val imported_note = filter imported deps_note

  val report =
    "PP-REFUTATION-AUDIT: " ^ string_of_int (length all_facts) ^ " clean endpoints\n" ^
    "SCOPE: formalization of the note Purity of Pure and Recombination (11 November 2026), in the note's order: " ^
      string_of_int (length note_names) ^ " endpoints for its objects, Lemmas 1-6 and Theorem 1 " ^
      "(stock T0 = purity schema + application closure; T = T0 + PP at type Prop->Prop; " ^
      "Lemmas 1-3 use no added axiom), then " ^ string_of_int (length packaging_names) ^
      " packaging endpoints BEYOND THE NOTE (refutation of pp_recombination_PP_axioms and " ^
      "pp_full_QLN_PP_axioms in the constructor calculus; native transfer to " ^
      "gb_recombination_PP_axioms and gb_zeroary_unary_QLN_PP_axioms under sg_rich; " ^
      "native fun-prime statement over gb_T6_core).\n" ^
    "DIRECT-PROVENANCE: note endpoints: " ^ string_of_int n_note ^ " proof nodes traversed, " ^
      string_of_int (length deps_note) ^ " named theorems; stock-refuting (explosive) theorems reached: " ^
      (if null expl_note then "NONE" else commas expl_note) ^ ".\n" ^
    "DIRECT-PROVENANCE: packaging endpoints: " ^ string_of_int n_pack ^ " proof nodes traversed, " ^
      string_of_int (length deps_pack) ^ " named theorems; stock-refuting (explosive) theorems reached: " ^
      commas (map Long_Name.base_name expl_pack) ^
      " (all proved in Goodman_PP_Refutation_Packaging; no imported one).\n" ^
    stock_report ^ "\n" ^
    cat_lines (map rows note_groups) ^ "\n" ^
    cat_lines (map rows packaging_groups) ^ "\n" ^
    "== IMPORTED APPLICATION-LEVEL THEOREMS USED BY THE NOTE ENDPOINTS (theories Bacon_PP*, Bacon_CEV_Axiom*, Goodman*)\n" ^
    cat_lines imported_note ^ "\n"
  val _ = Export.export thy (Path.binding0 (Path.basic "pp-refutation-audit.txt"))
    [XML.Text report]
  val _ = writeln report
  val statement_report =
    cat_lines (map statements note_groups) ^ "\n" ^ cat_lines (map statements packaging_groups)
  val _ = Export.export thy (Path.binding0 (Path.basic "pp-refutation-statements.txt"))
    [XML.Text statement_report]
in end
\<close>

end
