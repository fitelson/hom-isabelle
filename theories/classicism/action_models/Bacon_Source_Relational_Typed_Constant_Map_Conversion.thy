theory Bacon_Source_Relational_Typed_Constant_Map_Conversion
  imports Bacon_Source_Relational_Typed_Constant_Map_Binding
begin

section \<open>Forward transport through every native R conversion constructor\<close>

theorem paper_R_typed_constant_map_raw_conversion:
  assumes conversion: "paper_R_raw_beta_eta G \<tau> A B"
  shows "paper_R_raw_beta_eta G \<tau> (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  using conversion
proof (induction rule: paper_R_raw_beta_eta.induct)
  case Refl
  show ?case by (rule paper_R_raw_beta_eta.Refl[OF paper_R_typed_constant_map_type[OF Refl.hyps]])
next
  case Beta
  show ?case by (rule paper_R_raw_beta_eta.Beta[
    OF paper_R_typed_constant_map_type[OF Beta.hyps(1)]
      paper_R_typed_constant_map_type[OF Beta.hyps(2)] paper_R_typed_constant_map_beta_step[OF Beta.hyps(3)]])
next
  case Eta
  show ?case by (rule paper_R_raw_beta_eta.Eta[
    OF paper_R_typed_constant_map_type[OF Eta.hyps(1)]
      paper_R_typed_constant_map_type[OF Eta.hyps(2)] paper_R_typed_constant_map_eta_step[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule paper_R_raw_beta_eta.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule paper_R_raw_beta_eta.Trans[OF Trans.IH])
qed

text \<open>
  Every intermediate node remains R-typed, and every β or η
  edge is the literal transported compatible step. Since this is
  raw conversion, no signature premise is required. Admitted
  endpoints can separately use the declared-signature map theorem.
  This supplies syntax for a future finite-formula compression
  argument; it asserts no H/C proof transport or completeness.
\<close>

end
