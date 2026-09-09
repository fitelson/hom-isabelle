theory Bacon_Source_Named_Conversion_Steps
  imports Bacon_Source_Named_Substitution_Representation
    Bacon_Source_Named_Eta_Representation
begin

section \<open>Literal named β and η contractions in contexts\<close>

text \<open>
  (λx.A)B →β A[B/x] when B is free for x in A;
  λx.Fx →η F when x ∉ FV(F). A step may occur inside an application
  or beneath a λ binder. Source: Bacon–Dorr Figure 2, p.8, using the
  named syntax and fixed variable types of §1.1, p.5.

  Isabelle representation. The β root uses literal named_subst with its
  explicit named_free_for guard; no binder is silently renamed during
  substitution. named_compatible_step has only root, application, and
  abstraction constructors. In particular, it has no α constructor.

  Status. These are raw contraction and one-step context relations.
  The results below preserve them under the forward binding encoding.
  They do not assert conversion reflection, an H rule, or a semantic
  axiom. A language-relative equivalence closure must separately guard
  every node by the common type and declared signature.
\<close>

inductive named_beta_contract ::
  "('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool" where
  beta: "named_free_for B x A \<Longrightarrow>
    named_beta_contract (NApp (NLam x A) B) (named_subst x B A)"

inductive named_eta_contract ::
  "('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool" where
  eta: "x \<notin> named_fv F \<Longrightarrow>
    named_eta_contract (NLam x (NApp F (NVar x))) F"

inductive named_compatible_step ::
  "(('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool) \<Rightarrow>
    ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool"
  for R :: "('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool" where
  root: "R M N \<Longrightarrow> named_compatible_step R M N"
| App_left: "named_compatible_step R M M' \<Longrightarrow>
    named_compatible_step R (NApp M N) (NApp M' N)"
| App_right: "named_compatible_step R N N' \<Longrightarrow>
    named_compatible_step R (NApp M N) (NApp M N')"
| Lam_body: "named_compatible_step R M M' \<Longrightarrow>
    named_compatible_step R (NLam n M) (NLam n M')"

lemma named_beta_contract_encoding:
  assumes step: "named_beta_contract A B"
  shows "sbeta_contract (named_to_source G [] A) (named_to_source G [] B)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  show ?case by (rule named_beta_encoding[OF beta.hyps])
qed

lemma named_eta_contract_encoding:
  assumes step: "named_eta_contract A B"
  shows "seta_contract (named_to_source G [] A) (named_to_source G [] B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  show ?case by (rule named_eta_encoding[OF eta.hyps])
qed

subsection \<open>Transport through the three compound contexts\<close>

text \<open>
  Encoding beneath λn closes the name n: enc₍ₙ₎(A) = closeₙ(enc(A)).
  A source contextual step remains a step after that closing renaming.
  Thus the binder case uses a proved capture-avoiding source renaming
  law, rather than treating free named identifiers as bound slots.
\<close>

lemma named_compatible_encoding:
  fixes R :: "('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool"
    and Q :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool"
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow>
      Q (named_to_source G [] X) (named_to_source G [] Y)"
    and renamed: "\<And>r X Y. scompatible_step Q X Y \<Longrightarrow>
      scompatible_step Q (srename r X) (srename r Y)"
  shows "scompatible_step Q (named_to_source G [] A) (named_to_source G [] B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  have root_step: "Q (named_to_source G [] M) (named_to_source G [] N)"
    by (rule roots[where X=M and Y=N, OF root.hyps])
  show ?case by (rule scompatible_step.root[where R=Q
    and M="named_to_source G [] M" and N="named_to_source G [] N", OF root_step])
next
  case (App_left M M' N)
  show ?case by (simp only: named_to_source.simps)
    (rule scompatible_step.App_left[where R=Q and M="named_to_source G [] M"
      and M'="named_to_source G [] M'" and N="named_to_source G [] N", OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: named_to_source.simps)
    (rule scompatible_step.App_right[where R=Q and N="named_to_source G [] N"
      and N'="named_to_source G [] N'" and M="named_to_source G [] M", OF App_right.IH])
next
  case (Lam_body M M' n)
  have closed_step: "scompatible_step Q (sclose n (named_to_source G [] M))
    (sclose n (named_to_source G [] M'))"
    unfolding sclose_def
    by (rule renamed[where r="\<lambda>k. if k = n then 0 else Suc k"
      and X="named_to_source G [] M" and Y="named_to_source G [] M'", OF Lam_body.IH])
  have body_step: "scompatible_step Q (named_to_source G [n] M) (named_to_source G [n] M')"
    by (simp only: named_to_source_close; rule closed_step)
  show ?case by (simp only: named_to_source.simps)
    (rule scompatible_step.Lam_body[where R=Q and \<sigma>="G n"
      and M="named_to_source G [n] M" and M'="named_to_source G [n] M'", OF body_step])
qed

theorem named_beta_step_encoding:
  fixes A B :: "('c, 'l) named_term"
  assumes step: "named_compatible_step named_beta_contract A B"
  shows "scompatible_step sbeta_contract (named_to_source G [] A) (named_to_source G [] B)"
proof (rule named_compatible_encoding[where R=named_beta_contract and Q=sbeta_contract, OF step])
  fix X Y :: "('c, 'l) named_term"
  assume root_step: "named_beta_contract X Y"
  show "sbeta_contract (named_to_source G [] X) (named_to_source G [] Y)"
    by (rule named_beta_contract_encoding[OF root_step])
next
  fix r X Y
  assume source_step: "scompatible_step sbeta_contract X Y"
  show "scompatible_step sbeta_contract (srename r X) (srename r Y)"
    by (rule srename_beta_step[where r=r, OF source_step])
qed

theorem named_eta_step_encoding:
  fixes A B :: "('c, 'l) named_term"
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "scompatible_step seta_contract (named_to_source G [] A) (named_to_source G [] B)"
proof (rule named_compatible_encoding[where R=named_eta_contract and Q=seta_contract, OF step])
  fix X Y :: "('c, 'l) named_term"
  assume root_step: "named_eta_contract X Y"
  show "seta_contract (named_to_source G [] X) (named_to_source G [] Y)"
    by (rule named_eta_contract_encoding[OF root_step])
next
  fix r X Y
  assume source_step: "scompatible_step seta_contract X Y"
  show "scompatible_step seta_contract (srename r X) (srename r Y)"
    by (rule srename_eta_step[where r=r, OF source_step])
qed

end
