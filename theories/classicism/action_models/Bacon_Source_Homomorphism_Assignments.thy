theory Bacon_Source_Homomorphism_Assignments
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>Typed transport of adequate partial assignments\<close>

text \<open>
  For a typed family hσ:Mσ→Nσ and a partial assignment g, define
  (h·g)(xσ)=hσ(g(xσ)) wherever g(xσ) is defined. Undefined
  assignments remain undefined. Source: the homomorphism definition in
  Bacon–Dorr §3.3, p.49, immediately before Definition 3.10.

  The assignment domain is unchanged, so adequacy for each term is
  preserved in both directions. Typedness uses only the displayed
  domain-mapping hypothesis. The source and target may have different
  ambient HOL carrier types. No model, interpretation, valuation,
  injectivity, surjectivity or nonempty-domain assumption is introduced.
\<close>

definition paper_hom_assignment ::
  "sgcontext \<Rightarrow> (otype \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow>
    'a named_assignment \<Rightarrow> 'b named_assignment" where
  "paper_hom_assignment G h g n = map_option (h (G n)) (g n)"

lemma paper_hom_assignment_None:
  "paper_hom_assignment G h g n = None \<longleftrightarrow> g n = None"
  by (cases "g n") (simp_all add: paper_hom_assignment_def)

lemma paper_hom_assignment_Some:
  assumes assigned: "g n = Some a"
  shows "paper_hom_assignment G h g n = Some (h (G n) a)"
  by (simp add: paper_hom_assignment_def assigned)

lemma paper_hom_assignment_domain:
  "dom (paper_hom_assignment G h g) = dom g"
  by (auto simp: dom_def paper_hom_assignment_None)

theorem paper_hom_assignment_adequate_iff:
  "named_adequate (paper_hom_assignment G h g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_hom_assignment_domain)

theorem paper_hom_assignment_typed:
  assumes maps: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a \<in> E \<sigma>"
    and typed: "named_env_typed D G g"
  shows "named_env_typed E G (paper_hom_assignment G h g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n b
  assume assigned: "paper_hom_assignment G h g n = Some b"
  obtain a where ga: "g n = Some a" and image: "b = h (G n) a"
    using assigned unfolding paper_hom_assignment_def by (cases "g n") auto
  have member: "a \<in> D (G n)" by (rule named_env_value[OF typed ga])
  show "b \<in> E (G n)" by (simp only: image; rule maps[OF member])
qed

lemma paper_hom_assignment_identity:
  "paper_hom_assignment G (\<lambda>\<sigma> a. a) g = g"
proof (rule ext)
  fix n
  show "paper_hom_assignment G (\<lambda>\<sigma> a. a) g n = g n"
    by (cases "g n") (simp_all add: paper_hom_assignment_def)
qed

lemma paper_hom_assignment_compose:
  "paper_hom_assignment G k (paper_hom_assignment G h g) =
    paper_hom_assignment G (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a)) g"
proof (rule ext)
  fix n
  show "paper_hom_assignment G k (paper_hom_assignment G h g) n =
    paper_hom_assignment G (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a)) g n"
    by (cases "g n") (simp_all add: paper_hom_assignment_def)
qed

lemma paper_hom_assignment_update:
  "paper_hom_assignment G h (g(n := Some a)) =
    (paper_hom_assignment G h g)(n := Some (h (G n) a))"
proof (rule ext)
  fix m
  show "paper_hom_assignment G h (g(n := Some a)) m =
    ((paper_hom_assignment G h g)(n := Some (h (G n) a))) m"
    by (cases "m = n") (simp_all add: paper_hom_assignment_def)
qed

lemma paper_hom_assignment_cong:
  assumes typed: "named_env_typed D G g"
    and agree: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a = k \<sigma> a"
  shows "paper_hom_assignment G h g = paper_hom_assignment G k g"
proof (rule ext)
  fix n
  show "paper_hom_assignment G h g n = paper_hom_assignment G k g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp add: paper_hom_assignment_def None)
  next
    case (Some a)
    have member: "a \<in> D (G n)" by (rule named_env_value[OF typed Some])
    show ?thesis by (simp add: paper_hom_assignment_def Some agree[OF member])
  qed
qed

end
