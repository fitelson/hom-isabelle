theory Bacon_Source_Named_Model_Tag_Assignments
  imports Bacon_Source_Named_Type_Tags
begin

section \<open>Typed partial assignments and their tagged copies\<close>

text \<open>
  Send g(x) = a to g′(x) = ⟨G(x),a⟩, leaving undefined values
  undefined. Removing tags recovers g. Conversely, a typed assignment
  into D′σ = {⟨σ,a⟩ | a ∈ Dσ} is recovered by removing and restoring
  tags. Source role: the typed partial assignments of Definition 3.1,
  Bacon–Dorr pp.43–44.

  Representation: named_tag_assignment uses map_option, so its domain of
  definition, and hence adequacy for each named term, are unchanged.
  Status: generic assignment facts; neither a named nor a finite-frame
  model is assumed. No disjointness of the original Dσ is required.
\<close>

definition named_tag_assignment ::
  "sgcontext \<Rightarrow> 'v named_assignment \<Rightarrow> (otype \<times> 'v) named_assignment" where
  "named_tag_assignment G g n = map_option (\<lambda>a. (G n, a)) (g n)"

lemma named_tag_assignment_value:
  "g n = Some a \<Longrightarrow> named_tag_assignment G g n = Some (G n, a)"
  by (simp add: named_tag_assignment_def)

lemma named_untag_tag_assignment:
  "named_untag_assignment (named_tag_assignment G g) = g"
  by (rule ext, rename_tac n, case_tac "g n")
    (simp_all add: named_tag_assignment_def named_untag_assignment_def)

lemma named_tag_assignment_domain:
  "dom (named_tag_assignment G g) = dom g"
  by (auto simp: dom_def named_tag_assignment_def split: option.splits)

lemma named_tag_assignment_adequate:
  "named_adequate (named_tag_assignment G g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def named_tag_assignment_domain)

lemma named_tag_assignment_typed:
  assumes typed: "named_env_typed D G g"
  shows "named_env_typed (named_tag_domain D) G (named_tag_assignment G g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n v
  assume assigned: "named_tag_assignment G g n = Some v"
  obtain a where original: "g n = Some a" and tag: "v = (G n, a)"
    using assigned unfolding named_tag_assignment_def by (cases "g n") auto
  have member: "a \<in> D (G n)" by (rule named_env_value[OF typed original])
  show "v \<in> named_tag_domain D (G n)"
    by (simp only: tag named_tag_domain_pair_iff; rule conjI[OF refl member])
qed

lemma named_tag_assignment_typed_iff:
  "named_env_typed (named_tag_domain D) G (named_tag_assignment G g) \<longleftrightarrow>
    named_env_typed D G g"
proof
  assume tagged: "named_env_typed (named_tag_domain D) G (named_tag_assignment G g)"
  show "named_env_typed D G g"
    using named_untag_assignment_typed[OF tagged] by (simp only: named_untag_tag_assignment)
next
  assume original: "named_env_typed D G g"
  show "named_env_typed (named_tag_domain D) G (named_tag_assignment G g)"
    by (rule named_tag_assignment_typed[OF original])
qed

lemma named_tag_untag_assignment:
  assumes typed: "named_env_typed (named_tag_domain D) G g"
  shows "named_tag_assignment G (named_untag_assignment g) = g"
proof (rule ext)
  fix n
  show "named_tag_assignment G (named_untag_assignment g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp add: named_tag_assignment_def named_untag_assignment_def None)
  next
    case (Some v)
    have member: "v \<in> named_tag_domain D (G n)" by (rule named_env_value[OF typed Some])
    have tag: "fst v = G n" by (rule named_tag_domain_fst[OF member])
    have pair_eq: "(G n, snd v) = v" using tag by (cases v) simp
    show ?thesis by (simp add: named_tag_assignment_def named_untag_assignment_def Some pair_eq)
  qed
qed

lemma named_tag_assignment_update:
  "named_tag_assignment G (g(n := Some a)) =
    (named_tag_assignment G g)(n := Some (G n, a))"
  by (rule ext, rename_tac k, case_tac "k = n")
    (simp_all add: named_tag_assignment_def)

end
