theory Bacon_Source_Named_Alpha_Representation
  imports Bacon_Source_Named_Alpha Bacon_Source_Named_Representation
    Bacon_Source_Closing_Structure Bacon_Source_Renaming_Conversion
begin

section \<open>Fresh-binder α changes preserve the binding representation\<close>

text \<open>
  If A ≡α B by the independently generated fresh-binder relation, their
  de Bruijn representations are equal.  Source role: named λ binding in
  Bacon–Dorr §1.1, p.5, and the no-capture proviso in Figure 2, p.8.

  Isabelle representation.  We first transport a binder stack by its
  variable-index map.  We then show that a type-preserving swap commutes
  with representation.  In the fresh-binder case, the two closing maps
  agree on the free names of the body.  Equality follows from this
  agreement, not from a definition of α in terms of representation.

  Status.  This proves only the forward implication for named_alpha.
  Neither its converse nor a characterization by conventional α is
  asserted.  In particular, this does not add an α rule to H, identify α
  with source βη conversion, or establish named substitution or semantics.
\<close>

subsection \<open>Changing a binder stack by its index map\<close>

lemma named_stack_map_lift:
  assumes maps: "\<And>k. r (named_index ns k) = named_index ms k"
  shows "lift_ren r (named_index (n # ns) k) = named_index (n # ms) k"
  by (cases "k = n") (simp_all add: maps)

lemma named_to_source_stack_map:
  assumes maps: "\<And>n. r (named_index ns n) = named_index ms n"
  shows "srename r (named_to_source G ns A) = named_to_source G ms A"
  using maps
proof (induction A arbitrary: ns ms r)
  case (NVar n)
  show ?case by (simp only: named_to_source.simps srename.simps NVar.prems)
next
  case (NConst c \<sigma>)
  show ?case by (simp only: named_to_source.simps srename.simps)
next
  case (NLogical l)
  show ?case by (simp only: named_to_source.simps srename.simps)
next
  case (NApp F A)
  have ft: "srename r (named_to_source G ns F) = named_to_source G ms F"
    by (rule NApp.IH(1)[where ns=ns and ms=ms and r=r, OF NApp.prems])
  have at: "srename r (named_to_source G ns A) = named_to_source G ms A"
    by (rule NApp.IH(2)[where ns=ns and ms=ms and r=r, OF NApp.prems])
  show ?case by (simp only: named_to_source.simps srename.simps ft at)
next
  case (NLam n A)
  have lifted: "\<And>k. lift_ren r (named_index (n # ns) k) = named_index (n # ms) k"
    by (rule named_stack_map_lift[where r=r and ns=ns and ms=ms, OF NLam.prems])
  have body_eq: "srename (lift_ren r) (named_to_source G (n # ns) A) =
    named_to_source G (n # ms) A"
    by (rule NLam.IH[where ns="n # ns" and ms="n # ms" and r="lift_ren r", OF lifted])
  show ?case by (simp only: named_to_source.simps srename.simps body_eq)
qed

lemma named_to_source_stack_from_empty:
  "srename (named_index ns) (named_to_source G [] A) = named_to_source G ns A"
proof (rule named_to_source_stack_map)
  fix n
  show "named_index ns (named_index [] n) = named_index ns n" by simp
qed

lemma named_to_source_close:
  "named_to_source G [n] A = sclose n (named_to_source G [] A)"
proof -
  have maps: "\<And>k. (if named_index [] k = n then 0 else Suc (named_index [] k)) =
    named_index [n] k" by simp
  have enc: "srename (\<lambda>k. if k = n then 0 else Suc k) (named_to_source G [] A) =
    named_to_source G [n] A"
    by (rule named_to_source_stack_map[where ns="[]" and ms="[n]"
      and r="\<lambda>k. if k = n then 0 else Suc k", OF maps])
  show ?thesis unfolding sclose_def by (rule sym[OF enc])
qed

subsection \<open>Type-preserving swaps commute with representation\<close>

lemma named_swap_index_equal:
  "named_swap_index x y k = named_swap_index x y n \<longleftrightarrow> k = n"
  by (rule inj_eq[OF named_swap_index_inj])

lemma named_swap_stack_map_lift:
  assumes maps: "\<And>k. r (named_index ns k) = named_index ms (named_swap_index x y k)"
  shows "lift_ren r (named_index (n # ns) k) =
    named_index (named_swap_index x y n # ms) (named_swap_index x y k)"
  by (cases "k = n") (simp_all add: maps named_swap_index_equal)

lemma named_swap_stack_map:
  assumes same_type: "G x = G y"
    and maps: "\<And>k. r (named_index ns k) = named_index ms (named_swap_index x y k)"
  shows "srename r (named_to_source G ns A) = named_to_source G ms (named_swap x y A)"
  using maps
proof (induction A arbitrary: ns ms r)
  case (NVar n)
  show ?case by (simp only: named_to_source.simps named_swap.simps srename.simps NVar.prems)
next
  case (NConst c \<sigma>)
  show ?case by (simp only: named_to_source.simps named_swap.simps srename.simps)
next
  case (NLogical l)
  show ?case by (simp only: named_to_source.simps named_swap.simps srename.simps)
next
  case (NApp F A)
  have ft: "srename r (named_to_source G ns F) = named_to_source G ms (named_swap x y F)"
    by (rule NApp.IH(1)[where ns=ns and ms=ms and r=r, OF NApp.prems])
  have at: "srename r (named_to_source G ns A) = named_to_source G ms (named_swap x y A)"
    by (rule NApp.IH(2)[where ns=ns and ms=ms and r=r, OF NApp.prems])
  show ?case by (simp only: named_swap.simps named_to_source.simps srename.simps ft at)
next
  case (NLam n A)
  have lifted: "\<And>k. lift_ren r (named_index (n # ns) k) =
    named_index (named_swap_index x y n # ms) (named_swap_index x y k)"
    by (rule named_swap_stack_map_lift[where r=r and ns=ns and ms=ms and x=x and y=y,
      OF NLam.prems])
  have body_eq: "srename (lift_ren r) (named_to_source G (n # ns) A) =
    named_to_source G (named_swap_index x y n # ms) (named_swap x y A)"
    by (rule NLam.IH[where ns="n # ns" and ms="named_swap_index x y n # ms"
      and r="lift_ren r", OF lifted])
  have binder_type: "G (named_swap_index x y n) = G n"
    by (rule named_swap_index_type[OF same_type])
  show ?case by (simp only: named_swap.simps named_to_source.simps srename.simps body_eq binder_type)
qed

lemma named_swap_encoding_empty:
  assumes same_type: "G x = G y"
  shows "srename (named_swap_index x y) (named_to_source G [] A) =
    named_to_source G [] (named_swap x y A)"
proof (rule named_swap_stack_map[OF same_type])
  fix k
  show "named_swap_index x y (named_index [] k) = named_index [] (named_swap_index x y k)"
    by simp
qed

subsection \<open>The fresh-binder generator and equivalence closure\<close>

text \<open>
  When y ∉ FV(A), closing x in A agrees with closing y after swapping
  x and y.  At a free occurrence of x both maps select slot 0; at every
  other free occurrence they select its successor slot.  The forbidden
  free occurrence of y is exactly the remaining possible discrepancy.
\<close>

lemma sclose_swap_fresh:
  assumes fresh: "y \<notin> sfv A"
  shows "sclose x A = sclose y (srename (named_swap_index x y) A)"
  unfolding sclose_def srename_comp
proof (rule srename_fv_agreement)
  fix k
  assume member: "k \<in> sfv A"
  have not_y: "k \<noteq> y" using member fresh by auto
  show "(if k = x then 0 else Suc k) =
    ((\<lambda>j. if j = y then 0 else Suc j) \<circ> named_swap_index x y) k"
    using not_y by (cases "k = x") (simp_all add: comp_def named_swap_index_def)
qed

lemma named_fresh_binder_encoding:
  assumes same_type: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "named_to_source G [] (NLam x A) =
    named_to_source G [] (NLam y (named_swap x y A))"
proof -
  have not_free: "y \<notin> named_fv A"
    using fresh named_fv_subset_vars[where A=A] by blast
  have fresh_enc: "y \<notin> sfv (named_to_source G [] A)"
    by (simp only: named_to_source_empty_fv; rule not_free)
  have swapped: "named_to_source G [] (named_swap x y A) =
    srename (named_swap_index x y) (named_to_source G [] A)"
    by (rule sym[OF named_swap_encoding_empty[OF same_type]])
  have body_eq: "sclose x (named_to_source G [] A) =
    sclose y (named_to_source G [] (named_swap x y A))"
    using sclose_swap_fresh[where x=x, OF fresh_enc] by (simp only: swapped)
  show ?thesis by (simp only: named_to_source.simps named_to_source_close body_eq same_type)
qed

theorem named_alpha_encoding_empty:
  assumes alpha: "named_alpha G A B"
  shows "named_to_source G [] A = named_to_source G [] B"
  using alpha
proof (induction rule: named_alpha.induct)
  case Refl
  show ?case by (rule refl)
next
  case (Fresh_Binder x y A)
  show ?case by (rule named_fresh_binder_encoding[OF Fresh_Binder.hyps])
next
  case App
  show ?case by (simp only: named_to_source.simps App.IH)
next
  case Lam
  show ?case by (simp only: named_to_source.simps named_to_source_close Lam.IH)
next
  case Sym
  show ?case by (rule sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule trans[OF Trans.IH])
qed

theorem named_alpha_encoding:
  assumes alpha: "named_alpha G A B"
  shows "named_to_source G ns A = named_to_source G ns B"
proof -
  have empty_eq: "named_to_source G [] A = named_to_source G [] B"
    by (rule named_alpha_encoding_empty[OF alpha])
  have renamed_eq: "srename (named_index ns) (named_to_source G [] A) =
    srename (named_index ns) (named_to_source G [] B)"
    by (rule arg_cong[where f="srename (named_index ns)", OF empty_eq])
  show ?thesis using renamed_eq by (simp only: named_to_source_stack_from_empty)
qed

end
