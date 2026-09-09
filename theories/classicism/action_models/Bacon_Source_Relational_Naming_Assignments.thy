theory Bacon_Source_Relational_Naming_Assignments
  imports Bacon_Source_Relational_Naming_Replacement
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>Overriding only the finite chart image\<close>

text \<open>
  At a chart variable x(σ,a), the overriding assignment supplies a.
  Elsewhere it retains g. The inverse is consulted only on x ` K;
  its cancellation law is used only for an injective chart on K.
  In intended applications K is a finite term support, although the
  raw assignment facts below need no finiteness assumption.

  An existing value at a marker may be replaced: freshness is from the
  term's variable names, not from the possibly infinite domain of g.
  Consequently original free-variable values are preserved. No semantic
  model, total completion, or closed denotability is assumed.
\<close>

definition paper_R_naming_override ::
  "(otype \<times> 'v) set \<Rightarrow> ((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow>
    'v named_assignment \<Rightarrow> 'v named_assignment" where
  "paper_R_naming_override K x g n =
    (if n \<in> x ` K then Some (snd (inv_into K x n)) else g n)"

lemma paper_R_naming_override_outside:
  "n \<notin> x ` K \<Longrightarrow> paper_R_naming_override K x g n = g n"
  by (simp add: paper_R_naming_override_def)

lemma paper_R_naming_override_empty:
  "paper_R_naming_override {} x g = g"
  by (rule ext) (simp add: paper_R_naming_override_def)

lemma paper_R_naming_override_lookup:
  assumes injective: "inj_on x K" and member: "k \<in> K"
  shows "paper_R_naming_override K x g (x k) = Some (snd k)"
  using member by (simp add: paper_R_naming_override_def inv_into_f_f[OF injective member])

lemma paper_R_naming_override_domain:
  "dom (paper_R_naming_override K x g) = dom g \<union> x ` K"
  by (auto simp: paper_R_naming_override_def dom_def)

lemma paper_R_naming_override_update:
  assumes outside: "n \<notin> x ` K"
  shows "paper_R_naming_override K x (g(n := v)) = (paper_R_naming_override K x g)(n := v)"
  by (rule ext; use outside in \<open>auto simp: paper_R_naming_override_def\<close>)

theorem paper_R_naming_override_typed:
  assumes typed: "named_env_typed D G g" and chart: "paper_R_naming_chart G K N x"
    and payloads: "\<forall>k\<in>K. snd k \<in> D (fst k)"
  shows "named_env_typed D G (paper_R_naming_override K x g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "paper_R_naming_override K x g n = Some a"
  show "a \<in> D (G n)"
  proof (cases "n \<in> x ` K")
    case True
    have key: "inv_into K x n \<in> K" by (rule inv_into_into[OF True])
    have at_n: "x (inv_into K x n) = n" by (rule f_inv_into_f[OF True])
    have key_type: "G n = fst (inv_into K x n)"
      using paper_R_naming_chart_type[OF chart key] by (simp only: at_n)
    have payload_member: "snd (inv_into K x n) \<in> D (fst (inv_into K x n))" using payloads key by blast
    have equal: "a = snd (inv_into K x n)"
      using assigned True by (simp add: paper_R_naming_override_def)
    show ?thesis by (simp only: equal key_type; rule payload_member)
  next
    case False
    have old: "g n = Some a" using assigned by (simp only: paper_R_naming_override_outside[OF False])
    show ?thesis by (rule named_env_value[OF typed old])
  qed
qed

theorem paper_R_naming_override_agrees:
  assumes chart: "paper_R_naming_chart G K N x" and avoid: "named_vars A \<subseteq> N"
    and free: "n \<in> named_fv A"
  shows "paper_R_naming_override K x g n = g n"
proof (rule paper_R_naming_override_outside)
  have original: "n \<in> N" using named_fv_subset_vars avoid free by blast
  show "n \<notin> x ` K" using chart original unfolding paper_R_naming_chart_def by blast
qed

theorem paper_R_naming_override_adequate:
  assumes adequate: "named_adequate g A" and support: "paper_R_naming_support A \<subseteq> K"
  shows "named_adequate (paper_R_naming_override K x g) (paper_R_naming_replace x A)"
  using paper_R_naming_replace_fv_bound[where x=x and A=A] adequate support
  unfolding named_adequate_def paper_R_naming_override_domain by blast

corollary paper_R_naming_term_override_typed:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    and chart: "paper_R_naming_chart G (paper_R_naming_support A) N x"
    and typed: "named_env_typed D G g"
  shows "named_env_typed D G (paper_R_naming_override (paper_R_naming_support A) x g)"
proof -
  have names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
    using language unfolding paper_R_in_language_def by blast
  show ?thesis by (rule paper_R_naming_override_typed[
    OF typed chart paper_R_naming_support_values[OF names]])
qed

end
