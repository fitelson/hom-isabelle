theory Typed_Paper_Primitives_Complete
  imports Typed_Paper_Primitives_Binary_Bridge
begin

theorem pc_primitive_identification:
  assumes ww: "Elem w raw_W"
  shows "pc_enc (paper_logical_type l) w (raw_primitive l w) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
  by (cases l; simp only: paper_logical_type.simps;
      rule pc_primitive_Not
        pc_primitive_And[simplified paper_logical_type.simps]
        pc_primitive_Or[simplified paper_logical_type.simps]
        pc_primitive_All pc_primitive_Ex
        pc_primitive_Eq[simplified paper_logical_type.simps];
      rule ww)

theorem paper_primitive_identification:
  assumes ww: "Elem w raw_W"
  shows "paper_enc (paper_logical_type l) w
      (src_T (paper_logical_type l) raw_root w (src_primitive l)) =
    paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
  by (simp only: src_primitive_future[OF ww] pc_enc_def[symmetric]
      pc_primitive_identification[OF ww])

theorem paper_primitive_member:
  assumes ww: "Elem w raw_W"
  shows "Elem (paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l)
    (paper_D (paper_logical_type l) w)"
  using pc_enc_type[OF raw_primitive_type[where l=l and w=w]]
  by (simp only: pc_primitive_identification[OF ww])

text \<open>Each of the six values here is the literal function graph of
  paper Definition 3.19, including its own outgoing-arrow guards and
  own-domain quantifiers. Membership follows from concrete typed objects
  constructed before the recoding. No primitive-stock or modelhood premise
  is introduced by these endpoints. Totality for arbitrary paper terms
  remains the separate Definition 3.20 interpretation theorem.\<close>

ML \<open>
  val facts = [@{thm raw_primitive_type}, @{thm raw_primitive_natural},
    @{thm src_primitive_type}, @{thm pc_primitive_identification},
    @{thm paper_primitive_identification}, @{thm paper_primitive_member}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "PAPER-PRIMITIVES: six literal Definition 3.19 operators; no stock assumptions";
\<close>

end
