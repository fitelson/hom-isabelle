theory PoP_G100_W_Not_PP
  imports PoP_Main.PoP_G100_Kernel
begin

text \<open>Purity of Pure: W Refutes PP_u
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory holds a kernel theorem, by Loupe on the main theory, with Jacob, 2026-11-08; none of this text is Branden Fitelson's. u_S says U proves rcS -> not ExUni, where
  rcS holds the nine claims and PP_u. Here the one propositional step: U proves that W's ten claims imply not PP_u. The antecedents are curried, in the order of the Metamath theorem
  w-not-pp: LP at P, P' and W; Application at (u -> t, u), (u -> t, u -> u), (u, t) and (u, u); Exhaustion_0 at Pure_u(P) and Pure_u(P'); and ExUni, some proposition is universal.\<close>

theorem w_not_pp: "[] \<turnstile>\<^sub>U Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp)
  (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) (Imp (pp_application_closure rc_c rc_u)
  (Imp (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) (Imp (pp_application_closure rc_u Prop)
  (Imp (pp_application_closure rc_u rc_u) (Imp (zI (App rc_p rcP)) (Imp (zI (App rc_p rcPp))
  (Imp rcExUni (Neg (pp_pure rc_c rc_p)))))))))))"
proof -
  have tS: "[] \<turnstile> rcS : Prop" using U_formula[OF u_S] by (auto elim: has_type.cases[of _ "Imp _ _"])
  have tE: "[] \<turnstile> rcExUni : Prop" by (rule k_ExUni_ty)
  have t: "[] \<turnstile> Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp)
    (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) (Imp (pp_application_closure rc_c rc_u)
    (Imp (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) (Imp (pp_application_closure rc_u Prop)
    (Imp (pp_application_closure rc_u rc_u) (Imp (zI (App rc_p rcP)) (Imp (zI (App rc_p rcPp))
    (Imp rcExUni (Neg (pp_pure rc_c rc_p))))))))))) : Prop"
    using tS tE unfolding rcS_def rcHU_def by (auto elim!: has_type.cases[of _ "Conj _ _"] intro!: has_type.Imp has_type.Neg)
  show ?thesis by (rule u_rc_pc1[OF u_S t]) (unfold rcS_def rcHU_def prop_eval.simps, blast)
qed

corollary w_not_pp_C: "[] \<turnstile>\<^sub>CEV Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp)
  (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) (Imp (pp_application_closure rc_c rc_u)
  (Imp (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) (Imp (pp_application_closure rc_u Prop)
  (Imp (pp_application_closure rc_u rc_u) (Imp (zI (App rc_p rcP)) (Imp (zI (App rc_p rcPp))
  (Imp rcExUni (Neg (pp_pure rc_c rc_p)))))))))))"
  by (rule U_sub_CEV[OF w_not_pp])

end
