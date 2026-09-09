theory Bacon_Source_Named_Representation
  imports Bacon_Source_Named_Syntax Bacon_Source_Finite_Typing
begin

section \<open>Forward representation of named binding by de Bruijn slots\<close>

text \<open>
  Represent a named variable by the nearest enclosing binder with that
  name, when present; otherwise retain its global identifier after the
  binder-stack offset.  Source: named application and λ abstraction in
  Bacon–Dorr §1.1, p.5.

  Isabelle representation.  The list ns records binder names from nearest
  to outermost.  It may repeat names: named_index selects the first match,
  implementing shadowing.  NLam n receives the source binder type G n.
  The target stock is the original G prefixed by the types of ns.

  Status.  These theorems establish one well-typed forward representation,
  exact signature preservation, and a free-variable calculation.  They do
  not assert injectivity on raw named terms, an α quotient or round trip,
  capture-avoiding named substitution, proof correspondence, or named-model
  equivalence.  The finite typing corollary is a term-support theorem only.
\<close>

fun named_index :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "named_index [] n = n"
| "named_index (m # ns) n = (if n = m then 0 else Suc (named_index ns n))"

fun named_stack_stock :: "sgcontext \<Rightarrow> nat list \<Rightarrow> sgcontext" where
  "named_stack_stock G [] = G"
| "named_stack_stock G (n # ns) = sgextend (G n) (named_stack_stock G ns)"

fun named_to_source :: "sgcontext \<Rightarrow> nat list \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) sterm" where
  "named_to_source G ns (NVar n) = SVar (named_index ns n)"
| "named_to_source G ns (NConst c \<sigma>) = SConst c \<sigma>"
| "named_to_source G ns (NLogical l) = SLogical l"
| "named_to_source G ns (NApp F A) = SApp (named_to_source G ns F) (named_to_source G ns A)"
| "named_to_source G ns (NLam n A) = SLam (G n) (named_to_source G (n # ns) A)"

lemma named_index_free:
  "n \<notin> set ns \<Longrightarrow> named_index ns n = length ns + n"
  by (induction ns) simp_all

lemma named_stack_index_type:
  "named_stack_stock G ns (named_index ns n) = G n"
proof (induction ns)
  case Nil
  show ?case by simp
next
  case (Cons m ns)
  show ?case by (cases "n = m") (simp_all add: Cons.IH)
qed

lemma named_to_source_signature:
  "sterm_in_signature \<Sigma> (named_to_source G ns A) = named_in_signature \<Sigma> A"
  by (induction A arbitrary: ns) simp_all

theorem named_to_source_global_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_sgtype L (named_stack_stock G ns) (named_to_source G ns A) \<tau>"
  using typed
proof (induction arbitrary: ns rule: has_ntype.induct)
  case (Var n)
  have variable: "has_sgtype L (named_stack_stock G ns) (SVar (named_index ns n))
    (named_stack_stock G ns (named_index ns n))" by (rule has_sgtype.Var)
  show ?case using variable by (simp only: named_to_source.simps named_stack_index_type)
next
  case (Const c \<sigma>)
  show ?case by (simp only: named_to_source.simps) (rule has_sgtype.Const)
next
  case (Logical l)
  show ?case by (simp only: named_to_source.simps) (rule has_sgtype.Logical)
next
  case (App F \<sigma> \<tau> A)
  have ft: "has_sgtype L (named_stack_stock G ns) (named_to_source G ns F) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[where ns=ns])
  have at: "has_sgtype L (named_stack_stock G ns) (named_to_source G ns A) \<sigma>"
    by (rule App.IH(2)[where ns=ns])
  show ?case by (simp only: named_to_source.simps) (rule has_sgtype.App[OF ft at])
next
  case (Lam A \<tau> n)
  have body: "has_sgtype L (sgextend (G n) (named_stack_stock G ns)) (named_to_source G (n # ns) A) \<tau>"
    using Lam.IH[where ns="n # ns"] by (simp only: named_stack_stock.simps)
  show ?case by (simp only: named_to_source.simps) (rule has_sgtype.Lam[OF body])
qed

theorem named_to_source_global_language:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
  shows "sgterm_in_language L \<Sigma> (named_stack_stock G ns) (named_to_source G ns A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" and sig: "named_in_signature \<Sigma> A"
    using language unfolding named_in_language_def by blast+
  have names: "sterm_in_signature \<Sigma> (named_to_source G ns A)" by (simp only: named_to_source_signature sig)
  show ?thesis unfolding sgterm_in_language_def by (rule conjI[OF named_to_source_global_type[OF typed] names])
qed

subsection \<open>Exact free-variable accounting, including shadowing\<close>

lemma named_index_binder_image:
  "{k. Suc k \<in> named_index (n # ns) ` X} = named_index ns ` (X - {n})"
  by (auto simp: image_iff named_index.simps split: if_splits)

theorem named_to_source_fv:
  "sfv (named_to_source G ns A) = named_index ns ` named_fv A"
  by (induction A arbitrary: ns)
    (simp_all only: named_to_source.simps sfv.simps named_fv.simps
      image_Un image_insert image_empty named_index_binder_image)

corollary named_to_source_empty_fv:
  "sfv (named_to_source G [] A) = named_fv A"
  by (simp add: named_to_source_fv image_def)

corollary named_to_source_empty_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_sgtype L G (named_to_source G [] A) \<tau>"
  using named_to_source_global_type[where ns="[]", OF typed] by (simp only: named_stack_stock.simps)

corollary named_to_source_finite_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_stype L (map G [0..<source_free_bound (named_to_source G [] A)]) (named_to_source G [] A) \<tau>"
  by (rule source_global_typing_finite_support[OF named_to_source_empty_type[OF typed]])

text \<open>
  At an empty binder stack, translated free slots are exactly the original
  free names.  In particular, a closed named term translates to a closed
  source term.  This establishes the forward binding convention; it does
  not yet identify two named terms differing only in their bound names.
\<close>

corollary named_to_source_closed:
  "named_fv A = {} \<Longrightarrow> sfv (named_to_source G [] A) = {}"
  by (simp only: named_to_source_empty_fv)

end
