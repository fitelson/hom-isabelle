theory Bacon_Source_Finite_Typing
  imports Bacon_Source_Global_Typing Bacon_Source_Conversion
begin

section \<open>Finite support for typing in the source variable stock\<close>

text \<open>
  Every term uses only finitely many free variables, although the stock of
  available variables is infinite (Bacon–Dorr §1.1 and Figure 2). A finite
  list recording all its free-variable types therefore suffices to type it.

  Isabelle representation: has_sgtype uses the total stock G; has_stype uses
  a finite list Γ. The forward lemma requires Γ to agree with G only on
  sfv A. The converse below uses agreement on all declared slots of Γ.
  These are typing correspondences, not proof transformations. A derivation
  may need additional variables that are absent from its conclusion.
\<close>

lemma source_global_to_finite_typing:
  assumes typed: "has_sgtype L G A \<tau>"
    and agrees: "\<And>n. n \<in> sfv A \<Longrightarrow> lookup \<Gamma> n = Some (G n)"
  shows "has_stype L \<Gamma> A \<tau>"
  using typed agrees
proof (induction arbitrary: \<Gamma> rule: has_sgtype.induct)
  case (Var G n)
  have index: "lookup \<Gamma> n = Some (G n)" by (rule Var.prems) simp
  show ?case by (rule has_stype.Var[OF index])
next
  case Const
  show ?case by (rule has_stype.Const)
next
  case Logical
  show ?case by (rule has_stype.Logical)
next
  case (App G M \<sigma> \<tau> N)
  have left: "has_stype L \<Gamma> M (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)) (auto intro: App.prems)
  have right: "has_stype L \<Gamma> N \<sigma>"
    by (rule App.IH(2)) (auto intro: App.prems)
  show ?case by (rule has_stype.App[OF left right])
next
  case (Lam \<sigma> G M \<tau>)
  have agrees: "lookup (\<sigma> # \<Gamma>) n = Some (sgextend \<sigma> G n)"
    if member: "n \<in> sfv M" for n
  proof (cases n)
    case 0
    show ?thesis by (simp only: 0 lookup_Cons_0 sgextend_zero)
  next
    case (Suc k)
    have free: "k \<in> sfv (SLam \<sigma> M)" using member by (simp only: Suc sfv.simps mem_Collect_eq)
    show ?thesis using Lam.prems[OF free] by (simp only: Suc lookup_Cons_Suc sgextend_Suc)
  qed
  have body: "has_stype L (\<sigma> # \<Gamma>) M \<tau>"
    by (rule Lam.IH[OF agrees])
  show ?case by (rule has_stype.Lam[OF body])
qed

lemma source_finite_to_global_typing:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and agrees: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G n = \<rho>"
  shows "has_sgtype L G A \<tau>"
  using typed agrees
proof (induction arbitrary: G rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  have eq: "G n = \<tau>" by (rule Var.prems[OF Var.hyps])
  show ?case using has_sgtype.Var[where L=L and G=G and n=n] by (simp only: eq)
next
  case Const
  show ?case by (rule has_sgtype.Const)
next
  case Logical
  show ?case by (rule has_sgtype.Logical)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have left: "has_sgtype L G M (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[where G=G, OF App.prems])
  have right: "has_sgtype L G N \<sigma>"
    by (rule App.IH(2)[where G=G, OF App.prems])
  show ?case by (rule has_sgtype.App[OF left right])
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have agrees: "sgextend \<sigma> G n = \<rho>"
    if index: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    using index by (cases n) (auto intro: Lam.prems)
  have body: "has_sgtype L (sgextend \<sigma> G) M \<tau>"
    by (rule Lam.IH[where G="sgextend \<sigma> G", OF agrees])
  show ?case by (rule has_sgtype.Lam[OF body])
qed

subsection \<open>An explicit finite list for each source term\<close>

fun source_free_bound :: "('c, 'l) sterm \<Rightarrow> nat" where
  "source_free_bound (SVar n) = Suc n"
| "source_free_bound (SConst c \<sigma>) = 0"
| "source_free_bound (SLogical l) = 0"
| "source_free_bound (SApp M N) = max (source_free_bound M) (source_free_bound N)"
| "source_free_bound (SLam \<sigma> M) = source_free_bound M - 1"

lemma source_free_bound_covers:
  "n \<in> sfv A \<Longrightarrow> n < source_free_bound A"
proof (induction A arbitrary: n)
  case (SApp M N)
  have either: "n < source_free_bound M \<or> n < source_free_bound N"
    using SApp.prems SApp.IH by auto
  show ?case using either by auto
next
  case (SLam \<sigma> M)
  have member: "Suc n \<in> sfv M" using SLam.prems by simp
  have bound: "Suc n < source_free_bound M" by (rule SLam.IH[OF member])
  show ?case using bound by simp
qed simp_all

theorem source_global_typing_finite_support:
  assumes "has_sgtype L G A \<tau>"
  shows "has_stype L (map G [0..<source_free_bound A]) A \<tau>"
proof (rule source_global_to_finite_typing[OF assms])
  fix n
  assume "n \<in> sfv A"
  then have bound: "n < source_free_bound A" by (rule source_free_bound_covers)
  show "lookup (map G [0..<source_free_bound A]) n = Some (G n)"
    using bound by (simp add: lookup_def)
qed

end
