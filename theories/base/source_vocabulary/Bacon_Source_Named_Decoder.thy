theory Bacon_Source_Named_Decoder
  imports Bacon_Source_Named_Charts
begin

section \<open>Decoding finite source slots with fresh typed named binders\<close>

text \<open>
  A chart assigns a distinct typed name to every free slot. Decode a
  λ binder by choosing a fresh name of its type and extending the chart.
  Encoding the result relative to that chart recovers the original term.
  Source role: named application and λ abstraction in Bacon–Dorr §1.1,
  p.5. All primitive logical symbols remain first-class and unchanged.

  Isabelle representation. source_to_named is total, but nth is used only
  within its bounds in the theorems below. Their source-typing and chart
  guards discharge those bounds. The binder choice requires rich G.
  The round trip is relative to the chart, not an equality of empty-stack
  encodings with unrelated free slots. No assignment, denotation, model
  correspondence, or Γ-erasure is defined here.
\<close>

fun source_to_named ::
  "sgcontext \<Rightarrow> nat list \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) named_term" where
  "source_to_named G ns (SVar i) = NVar (ns ! i)"
| "source_to_named G ns (SConst c \<sigma>) = NConst c \<sigma>"
| "source_to_named G ns (SLogical l) = NLogical l"
| "source_to_named G ns (SApp F A) = NApp (source_to_named G ns F) (source_to_named G ns A)"
| "source_to_named G ns (SLam \<sigma> A) =
    NLam (named_chart_fresh G ns \<sigma>) (source_to_named G (named_chart_fresh G ns \<sigma> # ns) A)"

lemma source_to_named_signature:
  "named_in_signature \<Sigma> (source_to_named G ns A) = sterm_in_signature \<Sigma> A"
  by (induction A arbitrary: ns) simp_all

theorem source_to_named_type:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "has_ntype L G (source_to_named G ns A) \<tau>"
  using typed chart
proof (induction arbitrary: ns rule: has_stype.induct)
  case (Var \<Gamma> i \<tau>)
  have name_type: "G (ns ! i) = \<tau>" by (rule named_chart_lookup[OF Var.prems Var.hyps])
  have variable: "has_ntype L G (NVar (ns ! i)) (G (ns ! i))" by (rule has_ntype.Var)
  show ?case using variable by (simp only: source_to_named.simps name_type)
next
  case (Const \<Gamma> c \<tau>)
  show ?case by (simp only: source_to_named.simps; rule has_ntype.Const)
next
  case (Logical \<Gamma> l)
  show ?case by (simp only: source_to_named.simps; rule has_ntype.Logical)
next
  case (App \<Gamma> F \<sigma> \<tau> A)
  have ft: "has_ntype L G (source_to_named G ns F) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[OF App.prems])
  have at: "has_ntype L G (source_to_named G ns A) \<sigma>"
    by (rule App.IH(2)[OF App.prems])
  show ?case by (simp only: source_to_named.simps; rule has_ntype.App[OF ft at])
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF Lam.prems rich])
  have body: "has_ntype L G (source_to_named G (?n # ns) A) \<tau>"
    by (rule Lam.IH[where ns="?n # ns", OF extended])
  have abstraction: "has_ntype L G (NLam ?n (source_to_named G (?n # ns) A)) (Arr (G ?n) \<tau>)"
    by (rule has_ntype.Lam[OF body])
  show ?case using abstraction by (simp only: source_to_named.simps named_chart_fresh_type[OF rich])
qed

corollary source_to_named_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_in_language L \<Sigma> G (source_to_named G ns A) \<tau>"
proof -
  have typed: "has_stype L \<Gamma> A \<tau>" and sig: "sterm_in_signature \<Sigma> A"
    using language unfolding sterm_in_language_def by auto
  have named_type: "has_ntype L G (source_to_named G ns A) \<tau>"
    by (rule source_to_named_type[OF typed chart rich])
  have names: "named_in_signature \<Sigma> (source_to_named G ns A)"
    by (simp only: source_to_named_signature; rule sig)
  show ?thesis unfolding named_in_language_def by (rule conjI[OF named_type names])
qed

theorem source_to_named_fv_bound:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_fv (source_to_named G ns A) \<subseteq> set ns"
  using typed chart
proof (induction arbitrary: ns rule: has_stype.induct)
  case (Var \<Gamma> i \<tau>)
  have bound: "i < length ns" by (rule named_chart_lookup_bound[OF Var.prems Var.hyps])
  have member: "ns ! i \<in> set ns" by (rule nth_mem[OF bound])
  show ?case using member by simp
next
  case Const
  show ?case by simp
next
  case Logical
  show ?case by simp
next
  case (App \<Gamma> F \<sigma> \<tau> A)
  have ff: "named_fv (source_to_named G ns F) \<subseteq> set ns"
    by (rule App.IH(1)[OF App.prems])
  have af: "named_fv (source_to_named G ns A) \<subseteq> set ns"
    by (rule App.IH(2)[OF App.prems])
  show ?case using ff af by simp
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF Lam.prems rich])
  have body: "named_fv (source_to_named G (?n # ns) A) \<subseteq> set (?n # ns)"
    by (rule Lam.IH[where ns="?n # ns", OF extended])
  show ?case using body by auto
qed

theorem source_to_named_relative_roundtrip:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_to_source G ns (source_to_named G ns A) = A"
  using typed chart
proof (induction arbitrary: ns rule: has_stype.induct)
  case (Var \<Gamma> i \<tau>)
  have index: "named_index ns (ns ! i) = i"
    by (rule named_chart_index_lookup[OF Var.prems Var.hyps])
  show ?case by (simp only: source_to_named.simps named_to_source.simps index)
next
  case Const
  show ?case by (simp only: source_to_named.simps named_to_source.simps)
next
  case Logical
  show ?case by (simp only: source_to_named.simps named_to_source.simps)
next
  case (App \<Gamma> F \<sigma> \<tau> A)
  have ft: "named_to_source G ns (source_to_named G ns F) = F"
    by (rule App.IH(1)[OF App.prems])
  have at: "named_to_source G ns (source_to_named G ns A) = A"
    by (rule App.IH(2)[OF App.prems])
  show ?case by (simp only: source_to_named.simps named_to_source.simps ft at)
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF Lam.prems rich])
  have body: "named_to_source G (?n # ns) (source_to_named G (?n # ns) A) = A"
    by (rule Lam.IH[where ns="?n # ns", OF extended])
  show ?case by (simp only: source_to_named.simps named_to_source.simps body named_chart_fresh_type[OF rich])
qed

end
