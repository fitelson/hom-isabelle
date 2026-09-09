theory Bacon_Source_Global_Typing
  imports Bacon_Source_Substitution
begin

section \<open>A fixed infinite stock of typed free variables\<close>

text \<open>
  Each variable has a fixed type, and there are infinitely many variables
  of every type (Bacon–Dorr §1.1, p. 5).  A proof can use variables absent
  from its conclusion: the derivation of ∃x:σ.x =σ x on p. 7 does so.
  Restricting available variables instead leads to H⁻ (pp. 7–9, notes 8–9).

  Isabelle representation: a total G:nat → otype assigns a type to every
  free slot.  sg_rich G requires infinitely many slots at each F type.
  The raw sterm grammar is unchanged.  Beneath a binder, slot zero has the
  bound type and the old slots move to their successors.

  Status: global typing only.  No H relation, logical existence axiom,
  rich-stock construction, or named-variable/α-equivalence theorem is
  supplied here.
\<close>

type_synonym sgcontext = "nat \<Rightarrow> otype"

definition sg_rich :: "sgcontext \<Rightarrow> bool" where
  "sg_rich G \<longleftrightarrow> (\<forall>\<sigma>. infinite {n. G n = \<sigma>})"

definition sgextend :: "otype \<Rightarrow> sgcontext \<Rightarrow> sgcontext" where
  "sgextend \<sigma> G = case_nat \<sigma> G"

lemma sgextend_zero[simp]: "sgextend \<sigma> G 0 = \<sigma>"
  by (simp add: sgextend_def)
lemma sgextend_Suc[simp]: "sgextend \<sigma> G (Suc n) = G n"
  by (simp add: sgextend_def)

lemma sg_rich_type_fiber:
  assumes "sg_rich G"
  shows "infinite {n. G n = \<sigma>}"
  by (rule spec[where x=\<sigma>, OF assms[unfolded sg_rich_def]])

lemma sg_rich_variable:
  assumes "sg_rich G"
  obtains n where "G n = \<sigma>"
proof -
  have nonempty: "{n. G n = \<sigma>} \<noteq> {}"
    by (rule infinite_imp_nonempty[OF sg_rich_type_fiber[OF assms]])
  obtain n where member: "n \<in> {n. G n = \<sigma>}" using nonempty by auto
  have typed: "G n = \<sigma>" using member by (rule CollectD)
  show thesis by (rule that[OF typed])
qed

lemma sgextend_rich:
  assumes rich: "sg_rich G"
  shows "sg_rich (sgextend \<sigma> G)"
proof (unfold sg_rich_def, rule allI)
  fix \<tau>
  let ?S = "{n. G n = \<tau>}"
  let ?T = "{n. sgextend \<sigma> G n = \<tau>}"
  have old: "infinite ?S" by (rule sg_rich_type_fiber[OF rich])
  have injective: "inj_on Suc ?S" by (rule inj_onI) simp
  have shifted: "infinite (image Suc ?S)"
  proof
    assume finite_image: "finite (image Suc ?S)"
    have finite_old: "finite ?S" by (rule finite_imageD[OF finite_image injective])
    show False by (rule notE[OF old finite_old])
  qed
  have contained: "image Suc ?S \<subseteq> ?T"
  proof (rule subsetI)
    fix m
    assume "m \<in> image Suc ?S"
    then obtain n where member: "n \<in> ?S" and eq: "m = Suc n" by (elim imageE)
    show "m \<in> ?T" using member by (simp only: eq sgextend_Suc mem_Collect_eq)
  qed
  show "infinite ?T" by (rule infinite_super[OF contained shifted])
qed

section \<open>Global source typing and renaming\<close>

text \<open>
  G ⊢ A:τ uses the total free-variable stock, rather than a minimal finite
  list (Bacon–Dorr §1.1).  The logical-type function still selects the
  paper or book basis without mixing them.

  Isabelle representation: has_sgtype uses G n directly at SVar n;
  SLam σ checks its body under sgextend σ G.  Renaming may change the
  total stock when every renamed variable retains its type.

  Status: typing preservation, not a source inference rule.  Richness is
  unnecessary for these structural lemmas and is not assumed.
\<close>

inductive has_sgtype ::
  "('l \<Rightarrow> otype) \<Rightarrow> sgcontext \<Rightarrow> ('c, 'l) sterm \<Rightarrow> otype \<Rightarrow> bool"
  for L :: "'l \<Rightarrow> otype" where
  Var: "has_sgtype L G (SVar n) (G n)"
| Const: "has_sgtype L G (SConst c \<sigma>) \<sigma>"
| Logical: "has_sgtype L G (SLogical l) (L l)"
| App: "has_sgtype L G M (Arr \<sigma> \<tau>) \<Longrightarrow> has_sgtype L G N \<sigma> \<Longrightarrow>
    has_sgtype L G (SApp M N) \<tau>"
| Lam: "has_sgtype L (sgextend \<sigma> G) M \<tau> \<Longrightarrow>
    has_sgtype L G (SLam \<sigma> M) (Arr \<sigma> \<tau>)"

definition sgterm_in_language ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    ('c, 'l) sterm \<Rightarrow> otype \<Rightarrow> bool" where
  "sgterm_in_language L \<Sigma> G A \<tau> \<longleftrightarrow>
    has_sgtype L G A \<tau> \<and> sterm_in_signature \<Sigma> A"

lemma sgextend_rename:
  assumes map: "\<And>n. H (r n) = G n"
  shows "sgextend \<sigma> H (lift_ren r n) = sgextend \<sigma> G n"
  by (cases n) (simp_all add: map)

lemma srename_preserves_global_typing:
  assumes typed: "has_sgtype L G A \<tau>"
    and map: "\<And>n. H (r n) = G n"
  shows "has_sgtype L H (srename r A) \<tau>"
  using typed map
proof (induction arbitrary: H r rule: has_sgtype.induct)
  case (Var G n)
  have target: "has_sgtype L H (SVar (r n)) (H (r n))" by (rule has_sgtype.Var)
  show ?case using target by (simp only: srename.simps Var.prems)
next
  case Const
  show ?case unfolding srename.simps by (rule has_sgtype.Const)
next
  case Logical
  show ?case unfolding srename.simps by (rule has_sgtype.Logical)
next
  case (App G M \<sigma> \<tau> N)
  have mt: "has_sgtype L H (srename r M) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[where H=H and r=r, OF App.prems])
  have nt: "has_sgtype L H (srename r N) \<sigma>"
    by (rule App.IH(2)[where H=H and r=r, OF App.prems])
  show ?case unfolding srename.simps by (rule has_sgtype.App[OF mt nt])
next
  case (Lam \<sigma> G M \<tau>)
  have lifted: "\<And>n. sgextend \<sigma> H (lift_ren r n) = sgextend \<sigma> G n"
    by (rule sgextend_rename[where H=H and r=r, OF Lam.prems])
  have body: "has_sgtype L (sgextend \<sigma> H) (srename (lift_ren r) M) \<tau>"
    by (rule Lam.IH[where H="sgextend \<sigma> H" and r="lift_ren r", OF lifted])
  show ?case unfolding srename.simps by (rule has_sgtype.Lam[OF body])
qed

section \<open>Abstracting an existing free variable\<close>

text \<open>
  Gen binds a chosen v:σ in Q when v is not free in the antecedent;
  Inst has the dual freshness condition (Bacon–Dorr Figure 2).

  Isabelle representation: sclose n A maps free slot n to the new bound
  slot zero and shifts every other free slot.  Lifting inside srename
  preserves existing bound variables.  A subsequent SLam forms λv.A.

  Status: the abstraction body is globally well-typed.  Freshness, named
  capture-avoiding abstraction, α-equivalence, and the ten-rule H relation
  still require separate proofs/definitions.
\<close>

definition sclose :: "nat \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "sclose n A = srename (\<lambda>k. if k = n then 0 else Suc k) A"

lemma sclose_global_type:
  assumes body: "has_sgtype L G A \<tau>" and variable: "G n = \<sigma>"
  shows "has_sgtype L (sgextend \<sigma> G) (sclose n A) \<tau>"
  unfolding sclose_def
proof (rule srename_preserves_global_typing[OF body])
  fix k
  show "sgextend \<sigma> G (if k = n then 0 else Suc k) = G k"
    by (cases "k = n") (simp_all add: variable)
qed

lemma sclose_abstraction_global_type:
  assumes "has_sgtype L G A \<tau>" and "G n = \<sigma>"
  shows "has_sgtype L G (SLam \<sigma> (sclose n A)) (Arr \<sigma> \<tau>)"
  by (rule has_sgtype.Lam[OF sclose_global_type[OF assms]])

end
