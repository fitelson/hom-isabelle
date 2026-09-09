theory Bacon_Source_ZF_Model_Substitution
  imports Bacon_Source_ZF_Substitution_Abstraction
begin

section \<open>C.3 for literal capture-free substitution\<close>

text \<open>
  If ⟦C⟧ᵍh=c, then ⟦B[C/x]⟧ᵍh=⟦B⟧ᵍ[x↦c]h.
  Source: Appendix C.3, p.71, with the no-capture proviso of Figure 2.

  Both terms belong to the independent R language. The partial
  assignment covers FV(C) and FV(B)−{x}; it need not already assign x.
  The theorem compares the actual partial-interpreter outputs. Its
  abstraction case uses C.1 in an action MODEL, not an unqualified
  premodel assertion. No BBK interpretation or semantic conversion
  axiom is used to establish substitution.
\<close>

lemma paper_ZF_action_model_typed_substitution:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and body: "paper_R_has_type G B \<rho>" and names: "named_in_signature \<Sigma> B"
    and payload: "paper_R_in_language \<Sigma> G C (G x)"
    and free_for: "named_free_for C x B"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and body_adequate: "named_adequate g (NLam x B)" and payload_adequate: "named_adequate g C"
    and returned: "paper_ZF_action_eval Ar source target compose identity D T I G C h g = Some c"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h (g(x := Some c))"
  using body names free_for arrow origin typed body_adequate payload_adequate returned
proof (induction arbitrary: h g c rule: paper_R_has_type.induct)
  case (Var n)
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis using Var.prems(8) True
      by (simp add: named_subst.simps paper_ZF_action_eval.simps)
  next
    case False
    show ?thesis by (simp add: named_subst.simps paper_ZF_action_eval.simps False)
  qed
next
  case Const
  show ?case by (simp only: named_subst.simps paper_ZF_action_eval.simps)
next
  case Logical
  show ?case by (simp only: named_subst.simps paper_ZF_action_eval.simps)
next
  case (App F \<sigma> \<tau> B)
  have fn: "named_in_signature \<Sigma> F" and bn: "named_in_signature \<Sigma> B"
    using App.prems(1) by simp_all
  have ff: "named_free_for C x F" and bf: "named_free_for C x B"
    using App.prems(2) by simp_all
  have fa: "named_adequate g (NLam x F)" and ba: "named_adequate g (NLam x B)"
    using App.prems(6) by (auto simp: named_adequate_def)
  have head:
    "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C F) h g =
      paper_ZF_action_eval Ar source target compose identity D T I G F h (g(x := Some c))"
    by (rule App.IH(1)[where h=h and g=g and c=c,
      OF fn ff App.prems(3,4,5) fa App.prems(7,8)])
  have argument:
    "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) h g =
      paper_ZF_action_eval Ar source target compose identity D T I G B h (g(x := Some c))"
    by (rule App.IH(2)[where h=h and g=g and c=c,
      OF bn bf App.prems(3,4,5) ba App.prems(7,8)])
  show ?case by (simp only: named_subst.simps paper_ZF_action_eval.simps head argument)
next
  case (Lam B \<tau> n)
  show ?case
  proof (cases "x \<in> named_fv (NLam n B)")
    case False
    have unchanged: "named_subst x C (NLam n B) = NLam n B"
      by (rule named_subst_fresh[OF False])
    show ?thesis by (simp only: unchanged paper_ZF_action_eval_update_fresh[OF False])
  next
    case True
    have different: "n \<noteq> x" and occurs: "x \<in> named_fv B" using True by auto
    have free: "named_free_for C x B" and fresh: "n \<notin> named_fv C"
      using Lam.prems(2) different occurs by auto
    have bn: "named_in_signature \<Sigma> B" using Lam.prems(1) by simp
    have abstraction:
      "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n (named_subst x C B)) h g =
        paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h (g(x := Some c))"
    proof (rule paper_ZF_action_model_eval_subst_Lam[
        OF model payload Lam.hyps(2) different fresh Lam.prems(3,4,5,6,7,8)])
      fix k u b
      assume ka: "k \<in> explode Ar" and ko: "source k = root"
        and ut: "paper_ZF_action_env_typed D G (target k) u"
        and ua: "named_adequate u (NLam x B)" and uc: "named_adequate u C"
        and ce: "paper_ZF_action_eval Ar source target compose identity D T I G C k u = Some b"
      show "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) k u =
        paper_ZF_action_eval Ar source target compose identity D T I G B k (u(x := Some b))"
        by (rule Lam.IH[where h=k and g=u and c=b, OF bn free ka ko ut ua uc ce])
    qed
    show ?thesis by (simp only: named_subst.simps different if_False; rule abstraction)
  qed
qed

theorem paper_ZF_action_model_substitution:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and body: "paper_R_in_language \<Sigma> G B \<rho>"
    and payload: "paper_R_in_language \<Sigma> G C (G x)"
    and free_for: "named_free_for C x B"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and body_adequate: "named_adequate g (NLam x B)" and payload_adequate: "named_adequate g C"
    and returned: "paper_ZF_action_eval Ar source target compose identity D T I G C h g = Some c"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h (g(x := Some c))"
proof -
  have bt: "paper_R_has_type G B \<rho>" and bn: "named_in_signature \<Sigma> B"
    using body unfolding paper_R_in_language_def by blast+
  show ?thesis by (rule paper_ZF_action_model_typed_substitution[
    OF model bt bn payload free_for arrow origin typed body_adequate payload_adequate returned])
qed

end
