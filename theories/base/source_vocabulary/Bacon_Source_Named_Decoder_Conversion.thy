theory Bacon_Source_Named_Decoder_Conversion
  imports Bacon_Source_Named_Decoder_Contexts
begin

section \<open>A guarded source βη chain decodes to named conversion\<close>

text \<open>
  If Γ ⊢ A ≡βη B:τ in ℒ(Σ), a chart of Γ in a rich stock G
  gives dec(A) ≡βη dec(B):τ in the named language. Reflexivity,
  symmetry, and transitivity preserve the common chart. The two step
  cases use contextual reflection with both source endpoint guards.
  Source: Bacon–Dorr Figure 2 and Definition 3.1(ii.d), pp.8,44.

  Status. Together with forward prefix transport, this provides a
  syntactic reverse conversion direction. It is not a named H proof
  correspondence or a semantic context-erasure result. No α rule is
  introduced: the root reflections use the previously derived α→βη
  consequence of literal β and η.
\<close>

theorem source_to_named_conversion:
  assumes conversion: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> A B"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
  using conversion chart
proof (induction arbitrary: ns rule: sbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> A \<tau>)
  have language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Refl.hyps])
  have decoded: "named_in_language L \<Sigma> G (source_to_named G ns A) \<tau>"
    by (rule source_to_named_language[OF language Refl.prems rich])
  show ?case by (rule named_beta_eta_in_language.Refl[OF decoded])
next
  case (Beta \<Gamma> A \<tau> B)
  have left: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Beta.hyps(1,3)])
  have right: "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Beta.hyps(2,4)])
  show ?case by (rule source_to_named_beta_step_conversion[OF Beta.hyps(5) left right Beta.prems rich])
next
  case (Eta \<Gamma> A \<tau> B)
  have left: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Eta.hyps(1,3)])
  have right: "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Eta.hyps(2,4)])
  show ?case by (rule source_to_named_eta_step_conversion[OF Eta.hyps(5) left right Eta.prems rich])
next
  case (Sym \<Gamma> \<tau> A B)
  have inner: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
    by (rule Sym.IH[where ns=ns, OF Sym.prems])
  show ?case by (rule named_beta_eta_in_language.Sym[OF inner])
next
  case (Trans \<Gamma> \<tau> A B C)
  have first: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
    by (rule Trans.IH(1)[where ns=ns, OF Trans.prems])
  have second: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns B) (source_to_named G ns C)"
    by (rule Trans.IH(2)[where ns=ns, OF Trans.prems])
  show ?case by (rule named_beta_eta_in_language.Trans[OF first second])
qed

end
