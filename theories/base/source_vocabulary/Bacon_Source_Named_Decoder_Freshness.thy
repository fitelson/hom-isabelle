theory Bacon_Source_Named_Decoder_Freshness
  imports Bacon_Source_Named_Decoder_Roundtrip Bacon_Source_Named_Substitution
begin

section \<open>Decoded bound names avoid every name in the input chart\<close>

text \<open>
  No binder introduced while decoding A uses a name from its input chart.
  Consequently, the free names of an argument decoded in that chart cannot
  be captured by binders in a body decoded under an extended chart.
  Source: the literal free-for proviso for β in Bacon–Dorr Figure 2, p.8.

  Isabelle representation. named_bound_names records binder declarations,
  not free occurrences. Its decoder freshness theorem applies to raw
  source terms; argument typing is needed separately for the free-name
  bound. These facts justify literal substitution without α-renaming.
\<close>

fun named_bound_names :: "('c, 'l) named_term \<Rightarrow> nat set" where
  "named_bound_names (NVar n) = {}"
| "named_bound_names (NConst c \<sigma>) = {}"
| "named_bound_names (NLogical l) = {}"
| "named_bound_names (NApp F A) = named_bound_names F \<union> named_bound_names A"
| "named_bound_names (NLam n A) = insert n (named_bound_names A)"

lemma source_to_named_bound_names_fresh:
  assumes rich: "sg_rich G"
  shows "named_bound_names (source_to_named G ns A) \<inter> set ns = {}"
proof (induction A arbitrary: ns)
  case SVar
  show ?case by simp
next
  case SConst
  show ?case by simp
next
  case SLogical
  show ?case by simp
next
  case (SApp F A)
  show ?case using SApp.IH[where ns=ns] by auto
next
  case (SLam \<sigma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have body: "named_bound_names (source_to_named G (?n # ns) A) \<inter> set (?n # ns) = {}"
    by (rule SLam.IH)
  show ?case using fresh body by auto
qed

lemma named_free_for_of_bound_names:
  assumes disjoint: "named_fv B \<inter> named_bound_names A = {}"
  shows "named_free_for B x A"
  using disjoint by (induction A) auto

theorem source_to_named_free_for:
  assumes argument: "has_stype L \<Gamma> N \<sigma>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_free_for (source_to_named G ns N) n (source_to_named G (n # ns) M)"
proof -
  have fv: "named_fv (source_to_named G ns N) \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF argument chart rich])
  have binders: "named_bound_names (source_to_named G (n # ns) M) \<inter> set (n # ns) = {}"
    by (rule source_to_named_bound_names_fresh[OF rich])
  have disjoint: "named_fv (source_to_named G ns N) \<inter>
    named_bound_names (source_to_named G (n # ns) M) = {}"
    using fv binders by auto
  show ?thesis by (rule named_free_for_of_bound_names[OF disjoint])
qed

end
