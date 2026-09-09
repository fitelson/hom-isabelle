theory Bacon_Source_Named_Eta_Representation
  imports Bacon_Source_Named_Alpha_Representation
begin

section \<open>The literal named η contraction preserves its freshness proviso\<close>

text \<open>
  λx.Fx contracts to F when x is not free in F (Bacon–Dorr Figure 2,
  p.8). Closing x in the representation of F then only shifts its free
  slots, giving exactly the existing source η pattern.

  Status: preservation of one raw syntactic contraction with its actual
  freshness condition. No α rule, proof judgment, or semantic conversion
  assumption is introduced. Typed and signature-guarded conversion chains
  remain a separate stage.
\<close>

theorem named_eta_encoding:
  assumes fresh: "x \<notin> named_fv F"
  shows "seta_contract
    (named_to_source G [] (NLam x (NApp F (NVar x))))
    (named_to_source G [] F)"
proof -
  have source_fresh: "x \<notin> sfv (named_to_source G [] F)"
    by (simp only: named_to_source_empty_fv; rule fresh)
  have shifted: "named_to_source G [x] F = sshift (named_to_source G [] F)"
    by (simp only: named_to_source_close; rule sclose_fresh_eq_sshift[OF source_fresh])
  have contraction: "seta_contract
    (SLam (G x) (SApp (sshift (named_to_source G [] F)) (SVar 0)))
    (named_to_source G [] F)"
    by (rule seta_contract.eta)
  show ?thesis using contraction by (simp add: shifted)
qed

end
