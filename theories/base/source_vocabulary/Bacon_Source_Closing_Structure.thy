theory Bacon_Source_Closing_Structure
  imports Bacon_Source_Global_Typing Bacon_Source_Propositional
begin

section \<open>Closing one existing source variable in a finite frame\<close>

text \<open>
  To bind vₙ in A, send that free slot to 0 and send every other free
  slot k to k + 1.  If vₙ is absent from P, closing P is just shifting
  P beneath the new binder.  Source: Bacon–Dorr Figure 2 Gen and Inst,
  p.8, with the fixed variable stock of §1.1.

  Isabelle representation: sclose already implements this renaming.
  Agreement on sfv suffices for equality of renamed terms, including under
  existing binders.  A finite frame Γ may contain slots absent from A;
  the condition lookup Γ n = Some σ permits closing into σ # Γ without
  deleting the original slot from the available stock.  Nonlogical
  signature membership is unchanged.

  Status: structural syntax and typing, for arbitrary constant and logical
  symbol carriers.  No semantic argument, source inference rule, or
  named-variable/α-equivalence correspondence is assumed.
\<close>

lemma slift_ren_fv_agreement:
  assumes agrees: "\<And>k. k \<in> sfv (SLam \<sigma> A) \<Longrightarrow> r k = s k"
    and member: "i \<in> sfv A"
  shows "lift_ren r i = lift_ren s i"
proof (cases i)
  case 0
  show ?thesis by (simp only: 0 lift_ren.simps)
next
  case (Suc k)
  have free: "k \<in> sfv (SLam \<sigma> A)" using member by (simp only: Suc sfv.simps mem_Collect_eq)
  show ?thesis by (simp only: Suc lift_ren.simps agrees[OF free])
qed

lemma srename_fv_agreement:
  assumes agrees: "\<And>n. n \<in> sfv A \<Longrightarrow> r n = s n"
  shows "srename r A = srename s A"
  using agrees
proof (induction A arbitrary: r s)
  case (SVar n)
  have eq: "r n = s n" by (rule SVar.prems) simp
  show ?case by (simp only: srename.simps eq)
next
  case (SConst c \<sigma>)
  show ?case by (simp only: srename.simps)
next
  case (SLogical l)
  show ?case by (simp only: srename.simps)
next
  case (SApp M N)
  have left: "r n = s n" if "n \<in> sfv M" for n
    by (rule SApp.prems) (simp only: sfv.simps; rule UnI1[OF that])
  have right: "r n = s n" if "n \<in> sfv N" for n
    by (rule SApp.prems) (simp only: sfv.simps; rule UnI2[OF that])
  show ?case by (simp only: srename.simps SApp.IH(1)[where r=r and s=s, OF left]
    SApp.IH(2)[where r=r and s=s, OF right])
next
  case (SLam \<sigma> A)
  have lifted: "lift_ren r n = lift_ren s n" if "n \<in> sfv A" for n
    by (rule slift_ren_fv_agreement[where \<sigma>=\<sigma> and A=A and r=r and s=s and i=n,
      OF SLam.prems that])
  show ?case by (simp only: srename.simps SLam.IH[where r="lift_ren r" and s="lift_ren s", OF lifted])
qed

lemma sclose_fresh_eq_sshift:
  assumes fresh: "n \<notin> sfv A"
  shows "sclose n A = sshift A"
  unfolding sclose_def sshift_def
proof (rule srename_fv_agreement)
  fix k
  assume member: "k \<in> sfv A"
  have distinct: "k \<noteq> n" using fresh member by blast
  show "(if k = n then 0 else Suc k) = Suc k" by (simp only: distinct if_False)
qed

lemma srename_signature:
  "sterm_in_signature \<Sigma> (srename r A) \<longleftrightarrow> sterm_in_signature \<Sigma> A"
  by (induction A arbitrary: r) simp_all

lemma sclose_signature:
  "sterm_in_signature \<Sigma> (sclose n A) \<longleftrightarrow> sterm_in_signature \<Sigma> A"
  by (simp only: sclose_def srename_signature)

lemma sclose_lookup:
  assumes variable: "lookup \<Gamma> n = Some \<sigma>" and index: "lookup \<Gamma> k = Some \<rho>"
  shows "lookup (\<sigma> # \<Gamma>) (if k = n then 0 else Suc k) = Some \<rho>"
proof (cases "k = n")
  case True
  have at_n: "lookup \<Gamma> n = Some \<rho>" using index by (simp only: True)
  have options: "Some \<sigma> = Some \<rho>" by (rule trans[OF sym[OF variable] at_n])
  have same_type: "\<sigma> = \<rho>" using options by (simp only: option.inject)
  show ?thesis by (simp add: True same_type)
next
  case False
  show ?thesis by (simp only: False if_False lookup_Cons_Suc index)
qed

lemma sclose_finite_type:
  assumes typed: "has_stype L \<Gamma> A \<tau>" and variable: "lookup \<Gamma> n = Some \<sigma>"
  shows "has_stype L (\<sigma> # \<Gamma>) (sclose n A) \<tau>"
  unfolding sclose_def
  by (rule srename_preserves_typing[OF typed], rule sclose_lookup[OF variable], assumption)

lemma sclose_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>" and variable: "lookup \<Gamma> n = Some \<sigma>"
  shows "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) (sclose n A) \<tau>"
proof -
  have typed: "has_stype L \<Gamma> A \<tau>" using language unfolding sterm_in_language_def by (rule conjunct1)
  have sig: "sterm_in_signature \<Sigma> A" using language unfolding sterm_in_language_def by (rule conjunct2)
  have closed_sig: "sterm_in_signature \<Sigma> (sclose n A)" by (rule iffD2[OF sclose_signature sig])
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF sclose_finite_type[OF typed variable] closed_sig])
qed

lemma sclose_abstraction_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>" and variable: "lookup \<Gamma> n = Some \<sigma>"
  shows "sterm_in_language L \<Sigma> \<Gamma> (SLam \<sigma> (sclose n A)) (Arr \<sigma> \<tau>)"
proof -
  have closed: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) (sclose n A) \<tau>" by (rule sclose_language[OF language variable])
  have typed: "has_stype L (\<sigma> # \<Gamma>) (sclose n A) \<tau>"
    using closed unfolding sterm_in_language_def by (rule conjunct1)
  have sig: "sterm_in_signature \<Sigma> (SLam \<sigma> (sclose n A))"
    using closed unfolding sterm_in_language_def by simp
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF has_stype.Lam[OF typed] sig])
qed

subsection \<open>The literal Figure 1 implication is retained\<close>

lemma srename_paper_imp:
  "srename r (paper_imp P Q) = paper_imp (srename r P) (srename r Q)"
  by (simp add: paper_imp_def paper_imp_const_def paper_or_def paper_not_def)

lemma sclose_paper_imp:
  "sclose n (paper_imp P Q) = paper_imp (sclose n P) (sclose n Q)"
  by (simp only: sclose_def srename_paper_imp)

end
