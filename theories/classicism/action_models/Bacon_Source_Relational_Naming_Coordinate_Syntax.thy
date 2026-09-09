theory Bacon_Source_Relational_Naming_Coordinate_Syntax
  imports Bacon_Source_Relational_Naming_Replacement
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Changing one chart variable is literal capture-free substitution\<close>

lemma paper_R_naming_replace_variable_free_for:
  assumes fresh: "m \<notin> named_vars A"
  shows "named_free_for (NVar m) n (paper_R_naming_replace x A)"
  using fresh by (induction A) (auto split: sum.splits)

theorem paper_R_naming_replace_coordinate:
  assumes support: "paper_R_naming_support A \<subseteq> K"
    and injective: "inj_on x K" and key: "k \<in> K"
    and fresh: "x k \<notin> named_vars A"
    and agree: "\<And>j. j \<in> K \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
  shows "paper_R_naming_replace y A =
    named_subst (x k) (NVar (y k)) (paper_R_naming_replace x A)"
  using support fresh
proof (induction A)
  case (NVar n)
  then show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases c)
    case (Inl b)
    then show ?thesis by simp
  next
    case (Inr a)
    have member: "(\<sigma>,a) \<in> K" using NConst.prems(1) by (simp add: Inr)
    show ?thesis
    proof (cases "(\<sigma>,a) = k")
      case True
      show ?thesis by (simp add: Inr True)
    next
      case False
      have different: "x (\<sigma>,a) \<noteq> x k"
        using injective member key False unfolding inj_on_def by blast
      have same: "y (\<sigma>,a) = x (\<sigma>,a)" by (rule agree[OF member False])
      show ?thesis by (simp add: Inr different same)
    qed
  qed
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fs: "paper_R_naming_support F \<subseteq> K" and argument_support: "paper_R_naming_support A \<subseteq> K"
    and ff: "x k \<notin> named_vars F" and af: "x k \<notin> named_vars A"
    using NApp.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps named_subst.simps
    NApp.IH(1)[OF fs ff] NApp.IH(2)[OF argument_support af])
next
  case (NLam n A)
  have support_body: "paper_R_naming_support A \<subseteq> K" and fresh_body: "x k \<notin> named_vars A"
    and binder_fresh: "n \<noteq> x k" using NLam.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps named_subst.simps
    binder_fresh if_False NLam.IH[OF support_body fresh_body])
qed

text \<open>
  The equation uses only freshness of the old marker. Freshness of the
  new marker from named_vars(A) supplies the separate free-for theorem.
  No disjointness between the two chart images is required.
\<close>

end
