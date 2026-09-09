theory Bacon_Source_Named_Substitution_Representation
  imports Bacon_Source_Named_Substitution Bacon_Source_Named_Alpha_Representation
begin

section \<open>Free-for replacement commutes with the binding representation\<close>

text \<open>
  ⟦A[B/x]⟧ = ⟦A⟧[⟦B⟧/x] when B is free for x in A.
  Source: the literal replacement and no-capture proviso for β in
  Bacon–Dorr Figure 2, p.8.

  Isabelle representation. The bracket notation here means named_to_source
  G [] at an empty binder stack. Its free slots retain the named variable
  identifiers. Closing a name y before substitution agrees with lifting
  the substitution beneath the new binder, provided y ≠ x and y ∉ FV(B).
  When x is absent, substitution is the identity on the term's free slots.

  Status. This is syntactic commutation under the explicit named_free_for
  hypothesis, followed by preservation of one root β contraction. It does
  not perform α-renaming, remove the source no-capture proviso, or assert
  proof or model correspondence. No α theorem is used in the argument;
  the imported representation leaf supplies the binder-closing equation.
\<close>

subsection \<open>Substitutions fixing the free slots have no effect\<close>

lemma ssubst_fv_identity:
  assumes fixes_free: "\<And>n. n \<in> sfv A \<Longrightarrow> s n = SVar n"
  shows "ssubst s A = A"
  using fixes_free
proof (induction A arbitrary: s)
  case (SVar n)
  have fixed: "s n = SVar n" by (rule SVar.prems) simp
  show ?case by (simp only: ssubst.simps fixed)
next
  case (SConst c \<sigma>)
  show ?case by (simp only: ssubst.simps)
next
  case (SLogical l)
  show ?case by (simp only: ssubst.simps)
next
  case (SApp F A)
  have left: "s n = SVar n" if "n \<in> sfv F" for n
    by (rule SApp.prems) (simp only: sfv.simps; rule UnI1[OF that])
  have right: "s n = SVar n" if "n \<in> sfv A" for n
    by (rule SApp.prems) (simp only: sfv.simps; rule UnI2[OF that])
  show ?case by (simp only: ssubst.simps
    SApp.IH(1)[where s=s, OF left] SApp.IH(2)[where s=s, OF right])
next
  case (SLam \<sigma> A)
  have lifted: "slift_subst s n = SVar n" if member: "n \<in> sfv A" for n
  proof (cases n)
    case 0
    show ?thesis by (simp only: 0 slift_subst.simps)
  next
    case (Suc k)
    have free: "k \<in> sfv (SLam \<sigma> A)"
      using member by (simp only: Suc sfv.simps mem_Collect_eq)
    have fixed: "s k = SVar k" by (rule SLam.prems[OF free])
    show ?thesis by (simp only: Suc slift_subst.simps fixed srename.simps)
  qed
  show ?case by (simp only: ssubst.simps
    SLam.IH[where s="slift_subst s", OF lifted])
qed

lemma ssubst_replace_fresh:
  assumes fresh: "x \<notin> sfv A"
  shows "ssubst (\<lambda>n. if n = x then B else SVar n) A = A"
proof (rule ssubst_fv_identity)
  fix n
  assume member: "n \<in> sfv A"
  have distinct: "n \<noteq> x" using member fresh by blast
  show "(if n = x then B else SVar n) = SVar n"
    by (simp only: distinct if_False)
qed

subsection \<open>Closing and literal free-slot replacement\<close>

lemma sclose_replace_commute:
  assumes distinct: "y \<noteq> x" and fresh: "y \<notin> sfv B"
  shows "sclose y (ssubst (\<lambda>n. if n = x then B else SVar n) A) =
    ssubst (slift_subst (\<lambda>n. if n = x then B else SVar n)) (sclose y A)"
proof -
  let ?r = "\<lambda>n. if n = y then 0 else Suc n"
  let ?s = "\<lambda>n. if n = x then B else SVar n"
  have closed_B: "srename ?r B = srename Suc B"
    using sclose_fresh_eq_sshift[OF fresh]
    by (simp only: sclose_def sshift_def)
  have maps: "(\<lambda>n. srename ?r (?s n)) = slift_subst ?s \<circ> ?r"
  proof (rule ext)
    fix n
    show "srename ?r (?s n) = (slift_subst ?s \<circ> ?r) n"
    proof (cases "n = y")
      case True
      show ?thesis by (simp add: True distinct comp_def)
    next
      case False
      note not_y = False
      show ?thesis
      proof (cases "n = x")
        case True
        have xy: "x \<noteq> y" using distinct by auto
        show ?thesis using xy by (simp add: True comp_def closed_B)
      next
        case False
        show ?thesis by (simp add: not_y False comp_def)
      qed
    qed
  qed
  show ?thesis by (simp only: sclose_def srename_ssubst ssubst_srename maps)
qed

lemma ssubst0_sclose_replace:
  "ssubst0 B (sclose x A) =
    ssubst (\<lambda>n. if n = x then B else SVar n) A"
proof -
  have maps: "case_nat B SVar \<circ> (\<lambda>n. if n = x then 0 else Suc n) =
    (\<lambda>n. if n = x then B else SVar n)"
    by (rule ext, rename_tac n, cases "n = x") (simp_all add: comp_def)
  show ?thesis by (simp only: ssubst0_def sclose_def ssubst_srename maps)
qed

subsection \<open>The named structural induction and its β consequence\<close>

theorem named_subst_encoding_empty:
  assumes free_for: "named_free_for B x A"
  shows "named_to_source G [] (named_subst x B A) =
    ssubst (\<lambda>n. if n = x then named_to_source G [] B else SVar n)
      (named_to_source G [] A)"
  using free_for
proof (induction A)
  case (NVar y)
  show ?case by (cases "y = x") (simp_all add: named_index.simps)
next
  case (NConst c \<sigma>)
  show ?case by (simp only: named_subst.simps named_to_source.simps ssubst.simps)
next
  case (NLogical l)
  show ?case by (simp only: named_subst.simps named_to_source.simps ssubst.simps)
next
  case (NApp F A)
  have ff: "named_free_for B x F" and af: "named_free_for B x A"
    using NApp.prems by (simp only: named_free_for.simps; blast)+
  show ?case by (simp only: named_subst.simps named_to_source.simps ssubst.simps
    NApp.IH(1)[OF ff] NApp.IH(2)[OF af])
next
  case (NLam y A)
  let ?enc = "named_to_source G []"
  let ?s = "\<lambda>n. if n = x then ?enc B else SVar n"
  show ?case
  proof (cases "x \<in> named_fv (NLam y A)")
    case False
    have unchanged: "named_subst x B (NLam y A) = NLam y A"
      by (rule named_subst_fresh[OF False])
    have fresh_enc: "x \<notin> sfv (?enc (NLam y A))"
      by (simp only: named_to_source_empty_fv; rule False)
    have fixed: "ssubst ?s (?enc (NLam y A)) = ?enc (NLam y A)"
      by (rule ssubst_replace_fresh[OF fresh_enc])
    show ?thesis by (simp only: unchanged fixed)
  next
    case True
    have distinct: "y \<noteq> x" and occurs: "x \<in> named_fv A"
      using True by (simp only: named_fv.simps; blast)+
    have ff: "named_free_for B x A" and fresh: "y \<notin> named_fv B"
      using NLam.prems distinct occurs by (simp only: named_free_for.simps; blast)+
    have fresh_enc: "y \<notin> sfv (?enc B)"
      by (simp only: named_to_source_empty_fv; rule fresh)
    have ih: "?enc (named_subst x B A) = ssubst ?s (?enc A)"
      by (rule NLam.IH[OF ff])
    have body_eq: "sclose y (?enc (named_subst x B A)) =
      ssubst (slift_subst ?s) (sclose y (?enc A))"
      by (simp only: ih; rule sclose_replace_commute[OF distinct fresh_enc])
    show ?thesis by (simp only: named_subst.simps distinct if_False
      named_to_source.simps named_to_source_close ssubst.simps body_eq)
  qed
qed

corollary named_subst_encoding_beta_body:
  assumes free_for: "named_free_for B x A"
  shows "ssubst0 (named_to_source G [] B) (named_to_source G [x] A) =
    named_to_source G [] (named_subst x B A)"
  by (simp only: named_to_source_close ssubst0_sclose_replace
    named_subst_encoding_empty[OF free_for])

theorem named_beta_encoding:
  assumes free_for: "named_free_for B x A"
  shows "sbeta_contract
    (named_to_source G [] (NApp (NLam x A) B))
    (named_to_source G [] (named_subst x B A))"
proof -
  have root: "sbeta_contract
    (SApp (SLam (G x) (named_to_source G [x] A)) (named_to_source G [] B))
    (ssubst0 (named_to_source G [] B) (named_to_source G [x] A))"
    by (rule sbeta_contract.beta)
  show ?thesis using root
    by (simp only: named_to_source.simps named_subst_encoding_beta_body[OF free_for])
qed

end
