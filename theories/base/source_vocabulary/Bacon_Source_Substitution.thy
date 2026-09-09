theory Bacon_Source_Substitution
  imports Bacon_Source_Translation
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Substitution
begin

section \<open>Renaming and capture-avoiding substitution in the source grammar\<close>

text \<open>
  A[B/v] replaces free occurrences of v without capturing variables of B
  (Bacon–Dorr Figure 2, p. 8; Bacon Chapter 5).  Simultaneous substitution
  A[s] replaces the free variables together.  Under λv.A the new v is fixed.

  Isabelle representation: srename acts on de Bruijn slots; sshift inserts
  slot zero.  slift_subst fixes zero and shifts every older replacement.
  The logical-symbol carrier remains arbitrary, so the paper and book
  primitive bases share the operations without identifying their symbols.

  Status: binding operations only.  No βη relation or H proof rule is
  defined.  The substitution below is a syntactic operation, not a semantic
  substitution theorem or an asserted identity of denotations.
\<close>

fun srename :: "(nat \<Rightarrow> nat) \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "srename r (SVar n) = SVar (r n)"
| "srename r (SConst c \<sigma>) = SConst c \<sigma>"
| "srename r (SLogical l) = SLogical l"
| "srename r (SApp M N) = SApp (srename r M) (srename r N)"
| "srename r (SLam \<sigma> M) = SLam \<sigma> (srename (lift_ren r) M)"

definition sshift :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "sshift M = srename Suc M"

fun slift_subst :: "(nat \<Rightarrow> ('c, 'l) sterm) \<Rightarrow> nat \<Rightarrow> ('c, 'l) sterm" where
  "slift_subst s 0 = SVar 0"
| "slift_subst s (Suc n) = srename Suc (s n)"

fun ssubst :: "(nat \<Rightarrow> ('c, 'l) sterm) \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm"
  where
  "ssubst s (SVar n) = s n"
| "ssubst s (SConst c \<sigma>) = SConst c \<sigma>"
| "ssubst s (SLogical l) = SLogical l"
| "ssubst s (SApp M N) = SApp (ssubst s M) (ssubst s N)"
| "ssubst s (SLam \<sigma> M) = SLam \<sigma> (ssubst (slift_subst s) M)"

definition ssubst0 :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm"
  where "ssubst0 T A = ssubst (case_nat T SVar) A"

subsection \<open>Type-respecting maps preserve typing\<close>

text \<open>
  If Γ ⊢ A:τ and s assigns a Δ-term of the declared type to each Γ-variable,
  then Δ ⊢ A[s]:τ.  This is the typing side condition of substitution in
  Bacon–Dorr Figure 2 and Bacon Chapter 5.

  Isabelle representation: the map hypotheses quantify only over successful
  context lookups.  At a binder they are transported to σ # Γ and σ # Δ.

  Status: typing preservation for the raw source syntax; arbitrary untyped
  replacements are not asserted to preserve typing.
\<close>

lemma srename_preserves_typing:
  assumes typed: "has_stype logical_type \<Gamma> A \<tau>"
    and ren: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> lookup \<Delta> (r n) = Some \<rho>"
  shows "has_stype logical_type \<Delta> (srename r A) \<tau>"
  using typed ren
proof (induction arbitrary: \<Delta> r rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  have look: "lookup \<Delta> (r n) = Some \<tau>" by (rule Var.prems[OF Var.hyps])
  show ?case unfolding srename.simps by (rule has_stype.Var[OF look])
next
  case Const
  show ?case unfolding srename.simps by (rule has_stype.Const)
next
  case Logical
  show ?case unfolding srename.simps by (rule has_stype.Logical)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have M_type: "has_stype logical_type \<Delta> (srename r M) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[OF App.prems])
  have N_type: "has_stype logical_type \<Delta> (srename r N) \<sigma>"
    by (rule App.IH(2)[OF App.prems])
  show ?case unfolding srename.simps by (rule has_stype.App[OF M_type N_type])
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
    lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<rho>"
    by (rule lookup_lift_ren[OF Lam.prems])
  have body: "has_stype logical_type (\<sigma> # \<Delta>) (srename (lift_ren r) M) \<tau>"
    by (rule Lam.IH[OF lifted])
  show ?case unfolding srename.simps by (rule has_stype.Lam[OF body])
qed

lemma sshift_preserves_typing:
  assumes "has_stype logical_type \<Gamma> A \<tau>"
  shows "has_stype logical_type (\<sigma> # \<Gamma>) (sshift A) \<tau>"
  unfolding sshift_def
proof (rule srename_preserves_typing[OF assms])
  fix n \<rho>
  assume "lookup \<Gamma> n = Some \<rho>"
  then show "lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<rho>" by (simp only: lookup_Cons_Suc)
qed

lemma slift_subst_preserves_typing:
  assumes sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow>
      has_stype logical_type \<Delta> (s n) \<rho>"
    and look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
  shows "has_stype logical_type (\<sigma> # \<Delta>) (slift_subst s n) \<rho>"
proof (cases n)
  case 0
  have rho: "\<rho> = \<sigma>" using look by (simp add: 0)
  show ?thesis unfolding 0 slift_subst.simps rho
    by (rule has_stype.Var[OF lookup_Cons_0])
next
  case (Suc m)
  have old: "lookup \<Gamma> m = Some \<rho>" using look by (simp only: Suc lookup_Cons_Suc)
  have term_type: "has_stype logical_type \<Delta> (s m) \<rho>" by (rule sub[OF old])
  have shifted: "has_stype logical_type (\<sigma> # \<Delta>) (sshift (s m)) \<rho>"
    by (rule sshift_preserves_typing[OF term_type])
  show ?thesis using shifted by (simp only: Suc slift_subst.simps sshift_def)
qed

lemma ssubst_preserves_typing:
  assumes typed: "has_stype logical_type \<Gamma> A \<tau>"
    and sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow>
      has_stype logical_type \<Delta> (s n) \<rho>"
  shows "has_stype logical_type \<Delta> (ssubst s A) \<tau>"
  using typed sub
proof (induction arbitrary: \<Delta> s rule: has_stype.induct)
  case Var
  show ?case unfolding ssubst.simps by (rule Var.prems[OF Var.hyps])
next
  case Const
  show ?case unfolding ssubst.simps by (rule has_stype.Const)
next
  case Logical
  show ?case unfolding ssubst.simps by (rule has_stype.Logical)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have M_type: "has_stype logical_type \<Delta> (ssubst s M) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[OF App.prems])
  have N_type: "has_stype logical_type \<Delta> (ssubst s N) \<sigma>"
    by (rule App.IH(2)[OF App.prems])
  show ?case unfolding ssubst.simps by (rule has_stype.App[OF M_type N_type])
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
    has_stype logical_type (\<sigma> # \<Delta>) (slift_subst s n) \<rho>"
    by (rule slift_subst_preserves_typing[OF Lam.prems])
  have body: "has_stype logical_type (\<sigma> # \<Delta>) (ssubst (slift_subst s) M) \<tau>"
    by (rule Lam.IH[OF lifted])
  show ?case unfolding ssubst.simps by (rule has_stype.Lam[OF body])
qed

lemma ssubst0_preserves_typing:
  assumes body: "has_stype logical_type (\<sigma> # \<Gamma>) A \<tau>"
    and arg: "has_stype logical_type \<Gamma> T \<sigma>"
  shows "has_stype logical_type \<Gamma> (ssubst0 T A) \<tau>"
  unfolding ssubst0_def
proof (rule ssubst_preserves_typing[OF body])
  fix n \<rho>
  assume look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
  show "has_stype logical_type \<Gamma> (case_nat T SVar n) \<rho>"
  proof (cases n)
    case 0
    have rho: "\<rho> = \<sigma>" using look by (simp add: 0)
    show ?thesis using arg by (simp add: 0 rho)
  next
    case (Suc m)
    have old: "lookup \<Gamma> m = Some \<rho>" using look by (simp only: Suc lookup_Cons_Suc)
    have variable: "has_stype logical_type \<Gamma> (SVar m) \<rho>"
      by (rule has_stype.Var[OF old])
    show ?thesis using variable by (simp add: Suc)
  qed
qed

section \<open>Translation commutes literally with the binding operations\<close>

text \<open>
  ⟦A[r]⟧ = ⟦A⟧[r] and ⟦A[s]⟧ = ⟦A⟧[⟦s⟧].
  These are representation equations for the substitutions in Bacon–Dorr
  Figure 2 and Bacon Chapter 5, not uses of an object-language β axiom.

  Isabelle representation: the generic lemmas require the wrapper map W to
  be unchanged by renaming/substitution.  Direct constructor calculations
  discharge both requirements separately for the paper and book wrappers.

  Status: exact syntactic commutation, including lifting and substitution
  at slot zero.  Free-variable-set correspondence and βη/proof transport
  remain outside this leaf.
\<close>

lemma paper_logical_translation_rename:
  "prename r (paper_logical_translation l) = paper_logical_translation l"
  by (cases l) (simp_all add: lift_ren.simps)

lemma book_minimal_logical_translation_rename:
  "prename r (book_minimal_logical_translation l) = book_minimal_logical_translation l"
  by (cases l) (simp_all add: lift_ren.simps)

lemma paper_logical_translation_subst:
  "psubst s (paper_logical_translation l) = paper_logical_translation l"
  by (cases l) (simp_all add: plift_subst.simps)

lemma book_minimal_logical_translation_subst:
  "psubst s (book_minimal_logical_translation l) = book_minimal_logical_translation l"
  by (cases l) (simp_all add: plift_subst.simps)

lemma sterm_translation_rename:
  assumes closed: "\<And>r l. prename r (W l) = W l"
  shows "sterm_translation W (srename r A) = prename r (sterm_translation W A)"
  by (induction A arbitrary: r)
    (simp_all only: srename.simps sterm_translation.simps prename.simps closed)

lemma sterm_translation_shift:
  assumes closed: "\<And>r l. prename r (W l) = W l"
  shows "sterm_translation W (sshift A) = pshift (sterm_translation W A)"
  unfolding sshift_def pshift_def by (rule sterm_translation_rename[OF closed])

lemma sterm_translation_lift:
  assumes closed: "\<And>r l. prename r (W l) = W l"
  shows "(\<lambda>n. sterm_translation W (slift_subst s n)) =
    plift_subst (\<lambda>n. sterm_translation W (s n))"
proof (rule ext)
  fix n :: nat
  show "sterm_translation W (slift_subst s n) =
    plift_subst (\<lambda>n. sterm_translation W (s n)) n"
    by (cases n)
      (simp_all only: slift_subst.simps plift_subst.simps sterm_translation.simps
        sterm_translation_rename[OF closed])
qed

lemma sterm_translation_subst:
  assumes rename_closed: "\<And>r l. prename r (W l) = W l"
    and subst_closed: "\<And>s l. psubst s (W l) = W l"
  shows "sterm_translation W (ssubst s A) =
    psubst (\<lambda>n. sterm_translation W (s n)) (sterm_translation W A)"
  by (induction A arbitrary: s)
    (simp_all only: ssubst.simps sterm_translation.simps psubst.simps subst_closed
      sterm_translation_lift[OF rename_closed])

lemma sterm_translation_subst0:
  assumes rename_closed: "\<And>r l. prename r (W l) = W l"
    and subst_closed: "\<And>s l. psubst s (W l) = W l"
  shows "sterm_translation W (ssubst0 T A) =
    psubst0 (sterm_translation W T) (sterm_translation W A)"
proof -
  have maps_eq: "(\<lambda>n. sterm_translation W (case_nat T SVar n)) =
    case_nat (sterm_translation W T) PVar"
  proof (rule ext)
    fix n :: nat
    show "sterm_translation W (case_nat T SVar n) =
      case_nat (sterm_translation W T) PVar n"
      by (cases n) simp_all
  qed
  show ?thesis unfolding ssubst0_def psubst0_def
    by (simp only: sterm_translation_subst[OF rename_closed subst_closed] maps_eq)
qed

lemma paper_to_pterm_rename:
  "paper_to_pterm (srename r A) = prename r (paper_to_pterm A)"
  by (rule sterm_translation_rename[OF paper_logical_translation_rename])

lemma book_minimal_to_pterm_rename:
  "book_minimal_to_pterm (srename r A) = prename r (book_minimal_to_pterm A)"
  by (rule sterm_translation_rename[OF book_minimal_logical_translation_rename])

lemma paper_to_pterm_shift:
  "paper_to_pterm (sshift A) = pshift (paper_to_pterm A)"
  by (rule sterm_translation_shift[OF paper_logical_translation_rename])

lemma book_minimal_to_pterm_shift:
  "book_minimal_to_pterm (sshift A) = pshift (book_minimal_to_pterm A)"
  by (rule sterm_translation_shift[OF book_minimal_logical_translation_rename])

lemma paper_to_pterm_lift:
  "(\<lambda>n. paper_to_pterm (slift_subst s n)) = plift_subst (\<lambda>n. paper_to_pterm (s n))"
  by (rule sterm_translation_lift[OF paper_logical_translation_rename])

lemma book_minimal_to_pterm_lift:
  "(\<lambda>n. book_minimal_to_pterm (slift_subst s n)) =
    plift_subst (\<lambda>n. book_minimal_to_pterm (s n))"
  by (rule sterm_translation_lift[OF book_minimal_logical_translation_rename])

lemma paper_to_pterm_subst:
  "paper_to_pterm (ssubst s A) = psubst (\<lambda>n. paper_to_pterm (s n)) (paper_to_pterm A)"
  by (rule sterm_translation_subst[OF paper_logical_translation_rename
      paper_logical_translation_subst])

lemma book_minimal_to_pterm_subst:
  "book_minimal_to_pterm (ssubst s A) =
    psubst (\<lambda>n. book_minimal_to_pterm (s n)) (book_minimal_to_pterm A)"
  by (rule sterm_translation_subst[OF book_minimal_logical_translation_rename
      book_minimal_logical_translation_subst])

lemma paper_to_pterm_subst0:
  "paper_to_pterm (ssubst0 T A) = psubst0 (paper_to_pterm T) (paper_to_pterm A)"
  by (rule sterm_translation_subst0[OF paper_logical_translation_rename
      paper_logical_translation_subst])

lemma book_minimal_to_pterm_subst0:
  "book_minimal_to_pterm (ssubst0 T A) =
    psubst0 (book_minimal_to_pterm T) (book_minimal_to_pterm A)"
  by (rule sterm_translation_subst0[OF book_minimal_logical_translation_rename
      book_minimal_logical_translation_subst])

end
