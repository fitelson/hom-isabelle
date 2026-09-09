theory Bacon_Book_Substitution_Freshness
  imports Bacon_Book_Simultaneous_Substitution_Language Bacon_Book_Finite_Fresh_Variables
begin

section \<open>Finite name support of a substitution table\<close>

text \<open>
  The support contains every variable key and every variable name in a
  payload, including bound names. It deliberately includes shadowed entries:
  this is a finite forbidden set, not the exact semantic support of lookup.
  A fresh variable is therefore neither replaced by the table nor introduced
  freely by any of its payloads. No freshness of the nonlogical signature is
  required. These are the name guards for finite simultaneous substitution.
\<close>

fun book_subst_key_variables :: "'c book_subst_key \<Rightarrow> nat set" where
  "book_subst_key_variables (BSVar n \<sigma>) = {n}"
| "book_subst_key_variables (BSConst c \<sigma>) = {}"

fun book_subst_table_variables :: "('c,'l) book_subst_table \<Rightarrow> nat set" where
  "book_subst_table_variables [] = {}"
| "book_subst_table_variables ((k,B)#\<theta>) =
    book_subst_key_variables k \<union> named_vars B \<union> book_subst_table_variables \<theta>"

lemma book_subst_key_variables_finite:
  "finite (book_subst_key_variables k)"
  by (cases k) simp_all

lemma book_subst_table_variables_finite:
  "finite (book_subst_table_variables \<theta>)"
  by (induction \<theta>)
    (auto simp: book_subst_key_variables_finite named_vars_finite split: prod.splits)

lemma book_subst_table_variables_member:
  assumes member: "(k,B) \<in> set \<theta>"
  shows "book_subst_key_variables k \<union> named_vars B \<subseteq> book_subst_table_variables \<theta>"
  using member by (induction \<theta>) (auto split: prod.splits)

lemma book_subst_fresh_payload:
  assumes fresh: "z \<notin> book_subst_table_variables \<theta>"
    and lookup: "map_of \<theta> k = Some B"
  shows "z \<notin> named_fv B"
  using book_subst_table_variables_member[OF book_subst_lookup_member[OF lookup]]
    named_fv_subset_vars[where A=B] fresh by blast

lemma book_subst_fresh_key:
  assumes fresh: "z \<notin> book_subst_table_variables \<theta>"
  shows "map_of \<theta> (BSVar z \<sigma>) = None"
proof (cases "map_of \<theta> (BSVar z \<sigma>)")
  case None
  show ?thesis by (rule None)
next
  case (Some B)
  have member: "(BSVar z \<sigma>, B) \<in> set \<theta>"
    by (rule book_subst_lookup_member[OF Some])
  have inclusion: "book_subst_key_variables (BSVar z \<sigma>) \<union> named_vars B
      \<subseteq> book_subst_table_variables \<theta>"
    using book_subst_table_variables_member[OF member] by simp
  have False using inclusion fresh by simp
  then show ?thesis by (rule FalseE)
qed

lemma book_subst_table_language_disable:
  assumes table: "book_subst_table_language L \<Lambda> \<Sigma> G \<theta>"
  shows "book_subst_table_language L \<Lambda> \<Sigma> G (book_subst_disable k \<theta>)"
  unfolding book_subst_table_language_def
  by (intro allI impI; rule book_subst_table_language_lookup[OF table];
      rule book_subst_disabled_lookup; assumption)

lemma book_subst_table_language_tail_without_head:
  assumes table: "book_subst_table_language L \<Lambda> \<Sigma> G ((k,B)#\<theta>)"
  shows "book_subst_table_language L \<Lambda> \<Sigma> G (book_subst_disable k \<theta>)"
proof (unfold book_subst_table_language_def, intro allI impI)
  fix j C
  assume lookup: "map_of (book_subst_disable k \<theta>) j = Some C"
  have original: "map_of ((k,B)#\<theta>) j = Some C"
    using lookup by (auto simp: book_subst_lookup_disable split: if_splits)
  show "book_in_language L \<Lambda> \<Sigma> G C (book_subst_key_type j)"
    by (rule book_subst_table_language_lookup[OF table original])
qed

lemma book_subst_marker_exists:
  assumes rich: "sg_rich G"
  shows "\<exists>z. G z = \<sigma> \<and> z \<notin> named_vars A \<union> book_subst_table_variables \<theta>"
proof -
  have finite_names: "finite (named_vars A \<union> book_subst_table_variables \<theta>)"
    by (rule finite_UnI[OF named_vars_finite book_subst_table_variables_finite])
  show ?thesis by (rule sg_rich_fresh[OF rich finite_names])
qed

lemma book_subst_disable_shorter:
  "length (book_subst_disable k \<theta>) < length ((k,B)#\<theta>)"
  by (simp add: book_subst_disable_def less_Suc_eq_le)

end
