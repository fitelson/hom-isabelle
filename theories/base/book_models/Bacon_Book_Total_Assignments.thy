theory Bacon_Book_Total_Assignments
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Global_Typing
begin

section \<open>Total typed assignments in the book's environment model condition\<close>

text \<open>
  An assignment is a family gσ:Varσ → Dσ. Updating x:σ with a ∈ Dσ
  leaves every other value unchanged (Bacon, Definition 14.11, p.296).
  The environment condition of Definition 14.13, p.302, compares g and h
  on FV(M) ∩ FV(N), not their union. Pasting assignments along one
  free-name set supplies a total assignment agreeing with each on its
  respective set whenever they agree on the intersection.

  Isabelle representation. Names are nat with their fixed types G; g is
  total, not option-valued. book_env_typed is defined independently of
  the paper's assignment predicates. No domain nonemptiness is assumed
  here. Under rich G, the existence of a typed total assignment is proved
  equivalent to nonemptiness at every type, keeping that issue explicit
  rather than placing it inside a raw applicative-structure definition.
\<close>

definition book_env_typed :: "(otype \<Rightarrow> 'v set) \<Rightarrow> sgcontext \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> bool" where
  "book_env_typed D G g \<longleftrightarrow> (\<forall>n. g n \<in> D (G n))"

lemma book_env_at:
  assumes typed: "book_env_typed D G g"
  shows "g n \<in> D (G n)"
  by (rule spec[where x=n, OF typed[unfolded book_env_typed_def]])

lemma book_env_update:
  assumes typed: "book_env_typed D G g" and member: "a \<in> D (G n)"
  shows "book_env_typed D G (g(n := a))"
proof (unfold book_env_typed_def, rule allI)
  fix m
  show "(g(n := a)) m \<in> D (G m)"
  proof (cases "m = n")
    case True
    show ?thesis using member by (simp add: True)
  next
    case False
    show ?thesis using book_env_at[where n=m, OF typed] by (simp add: False)
  qed
qed

definition book_paste_assignment :: "nat set \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> nat \<Rightarrow> 'v" where
  "book_paste_assignment X g h n = (if n \<in> X then g n else h n)"

lemma book_paste_typed:
  assumes first: "book_env_typed D G g" and second: "book_env_typed D G h"
  shows "book_env_typed D G (book_paste_assignment X g h)"
proof (unfold book_env_typed_def, rule allI)
  fix n
  show "book_paste_assignment X g h n \<in> D (G n)"
    using book_env_at[where n=n, OF first] book_env_at[where n=n, OF second]
    by (cases "n \<in> X") (simp_all add: book_paste_assignment_def)
qed

lemma book_paste_agrees_left:
  "n \<in> X \<Longrightarrow> book_paste_assignment X g h n = g n"
  by (simp add: book_paste_assignment_def)

lemma book_paste_outside:
  "n \<notin> X \<Longrightarrow> book_paste_assignment X g h n = h n"
  by (simp add: book_paste_assignment_def)

lemma book_paste_agrees_right:
  assumes overlap: "\<And>n. n \<in> X \<inter> Y \<Longrightarrow> g n = h n" and member: "n \<in> Y"
  shows "book_paste_assignment X g h n = h n"
proof (cases "n \<in> X")
  case True
  have shared: "n \<in> X \<inter> Y" by (rule IntI[OF True member])
  have equal: "g n = h n" by (rule overlap[OF shared])
  show ?thesis by (rule trans[OF book_paste_agrees_left[where X=X and g=g and h=h and n=n, OF True] equal])
next
  case False
  show ?thesis by (rule book_paste_outside[OF False])
qed

theorem book_assignment_pasting:
  assumes first: "book_env_typed D G g" and second: "book_env_typed D G h"
    and overlap: "\<And>n. n \<in> X \<inter> Y \<Longrightarrow> g n = h n"
  shows "\<exists>k. book_env_typed D G k \<and> (\<forall>n \<in> X. k n = g n) \<and> (\<forall>n \<in> Y. k n = h n)"
proof -
  have typed: "book_env_typed D G (book_paste_assignment X g h)" by (rule book_paste_typed[OF first second])
  have left: "\<forall>n \<in> X. book_paste_assignment X g h n = g n"
    by (intro ballI, rule book_paste_agrees_left, assumption)
  have right: "\<forall>n \<in> Y. book_paste_assignment X g h n = h n"
    by (intro ballI, rule book_paste_agrees_right[OF overlap], assumption)
  show ?thesis by (rule exI[where x="book_paste_assignment X g h"], rule conjI[OF typed conjI[OF left right]])
qed

subsection \<open>Assignment existence and nonempty typed domains\<close>

lemma book_domain_choice:
  assumes nonempty: "D \<sigma> \<noteq> {}"
  shows "(SOME a. a \<in> D \<sigma>) \<in> D \<sigma>"
proof (rule someI_ex)
  show "\<exists>a. a \<in> D \<sigma>" using nonempty by blast
qed

theorem book_total_assignment_exists:
  assumes domains: "\<And>\<sigma>. D \<sigma> \<noteq> {}"
  shows "\<exists>g. book_env_typed D G g"
proof -
  have typed: "book_env_typed D G (\<lambda>n. SOME a. a \<in> D (G n))"
    unfolding book_env_typed_def by (rule allI, rule book_domain_choice, rule domains)
  show ?thesis by (rule exI[where x="\<lambda>n. SOME a. a \<in> D (G n)"], rule typed)
qed

lemma book_env_domains_nonempty:
  assumes rich: "sg_rich G" and typed: "book_env_typed D G g"
  shows "D \<sigma> \<noteq> {}"
proof -
  obtain n where variable: "G n = \<sigma>"
    by (rule sg_rich_variable[where \<sigma>=\<sigma>, OF rich]; rule that; assumption)
  have member: "g n \<in> D \<sigma>" using book_env_at[where n=n, OF typed] by (simp only: variable)
  show ?thesis using member by blast
qed

theorem book_total_assignment_exists_iff:
  assumes rich: "sg_rich G"
  shows "(\<exists>g. book_env_typed D G g) \<longleftrightarrow> (\<forall>\<sigma>. D \<sigma> \<noteq> {})"
proof
  assume existence: "\<exists>g. book_env_typed D G g"
  obtain g where typed: "book_env_typed D G g" using existence by (elim exE)
  show "\<forall>\<sigma>. D \<sigma> \<noteq> {}" by (rule allI, rule book_env_domains_nonempty[OF rich typed])
next
  assume domains: "\<forall>\<sigma>. D \<sigma> \<noteq> {}"
  show "\<exists>g. book_env_typed D G g"
    by (rule book_total_assignment_exists, rule spec[OF domains])
qed

end
