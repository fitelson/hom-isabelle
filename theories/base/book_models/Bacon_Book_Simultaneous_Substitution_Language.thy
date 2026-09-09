theory Bacon_Book_Simultaneous_Substitution_Language
  imports Bacon_Book_Simultaneous_Substitution_Syntax
begin

section \<open>Language preservation by effective simultaneous payloads\<close>

text \<open>
  If A:τ belongs to ℒ(Λ,Σ) and every effective payload belongs to that
  language at its key's type, then A[θ]:τ belongs to the same language.
  Source: Bacon's typed replacement discipline, Definition 5.2, p.99.

  Representation. Only first-match payloads matter; shadowed list entries
  impose no language requirement. Binder restriction only removes a key,
  so it preserves every effective-payload guard. The language result also
  holds for raw capturing replacements and does not prove free-for or
  admissibility. Logical-symbol preservation concerns an arbitrary Λ.
\<close>

lemma book_subst_disabled_lookup:
  assumes found: "map_of (book_subst_disable k \<theta>) j = Some B"
  shows "map_of \<theta> j = Some B"
  using found by (auto simp only: book_subst_lookup_disable split: if_splits)

theorem book_simult_subst_signature:
  assumes body: "named_in_signature \<Sigma> A"
    and payloads: "\<And>k B. map_of \<theta> k = Some B \<Longrightarrow> named_in_signature \<Sigma> B"
  shows "named_in_signature \<Sigma> (book_simult_subst G \<theta> A)"
  using body payloads
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case
  proof (cases "map_of \<theta> (BSVar n (G n))")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps named_in_signature.simps)
  next
    case (Some B)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps; rule NVar.prems(2)[OF Some])
  qed
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases "map_of \<theta> (BSConst c \<sigma>)")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps; rule NConst.prems(1))
  next
    case (Some B)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps; rule NConst.prems(2)[OF Some])
  qed
next
  case (NLogical l)
  show ?case by (simp only: book_simult_subst.simps named_in_signature.simps)
next
  case (NApp F A)
  have fn: "named_in_signature \<Sigma> F" and an: "named_in_signature \<Sigma> A"
    using NApp.prems(1) by simp_all
  have fs: "named_in_signature \<Sigma> (book_simult_subst G \<theta> F)"
    by (rule NApp.IH(1)[OF fn NApp.prems(2)])
  have asub: "named_in_signature \<Sigma> (book_simult_subst G \<theta> A)"
    by (rule NApp.IH(2)[OF an NApp.prems(2)])
  show ?case by (simp only: book_simult_subst.simps named_in_signature.simps; rule conjI[OF fs asub])
next
  case (NLam n A)
  have an: "named_in_signature \<Sigma> A" using NLam.prems(1) by simp
  have restricted: "\<And>k B. map_of (book_subst_disable (BSVar n (G n)) \<theta>) k = Some B \<Longrightarrow> named_in_signature \<Sigma> B"
  proof -
    fix k B
    assume found: "map_of (book_subst_disable (BSVar n (G n)) \<theta>) k = Some B"
    have original: "map_of \<theta> k = Some B" by (rule book_subst_disabled_lookup[OF found])
    show "named_in_signature \<Sigma> B" by (rule NLam.prems(2)[OF original])
  qed
  show ?case unfolding book_simult_subst.simps named_in_signature.simps
    by (rule NLam.IH[OF an restricted])
qed

theorem book_simult_subst_logical_occurrences:
  assumes body: "named_logical_occurrences A \<subseteq> \<Lambda>"
    and payloads: "\<And>k B. map_of \<theta> k = Some B \<Longrightarrow> named_logical_occurrences B \<subseteq> \<Lambda>"
  shows "named_logical_occurrences (book_simult_subst G \<theta> A) \<subseteq> \<Lambda>"
  using body payloads
proof (induction A arbitrary: \<theta>)
  case (NVar n)
  show ?case
  proof (cases "map_of \<theta> (BSVar n (G n))")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps named_logical_occurrences.simps empty_subsetI)
  next
    case (Some B)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps; rule NVar.prems(2)[OF Some])
  qed
next
  case (NConst c \<sigma>)
  show ?case
  proof (cases "map_of \<theta> (BSConst c \<sigma>)")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps named_logical_occurrences.simps empty_subsetI)
  next
    case (Some B)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps; rule NConst.prems(2)[OF Some])
  qed
next
  case (NLogical l)
  show ?case by (simp only: book_simult_subst.simps; rule NLogical.prems(1))
next
  case (NApp F A)
  have fl: "named_logical_occurrences F \<subseteq> \<Lambda>" and al: "named_logical_occurrences A \<subseteq> \<Lambda>"
    using NApp.prems(1) by simp_all
  have fs: "named_logical_occurrences (book_simult_subst G \<theta> F) \<subseteq> \<Lambda>"
    by (rule NApp.IH(1)[OF fl NApp.prems(2)])
  have asub: "named_logical_occurrences (book_simult_subst G \<theta> A) \<subseteq> \<Lambda>"
    by (rule NApp.IH(2)[OF al NApp.prems(2)])
  show ?case unfolding book_simult_subst.simps named_logical_occurrences.simps
    by (rule Un_least[OF fs asub])
next
  case (NLam n A)
  have al: "named_logical_occurrences A \<subseteq> \<Lambda>" using NLam.prems(1) by simp
  have restricted: "\<And>k B. map_of (book_subst_disable (BSVar n (G n)) \<theta>) k = Some B \<Longrightarrow> named_logical_occurrences B \<subseteq> \<Lambda>"
  proof -
    fix k B
    assume found: "map_of (book_subst_disable (BSVar n (G n)) \<theta>) k = Some B"
    have original: "map_of \<theta> k = Some B" by (rule book_subst_disabled_lookup[OF found])
    show "named_logical_occurrences B \<subseteq> \<Lambda>" by (rule NLam.prems(2)[OF original])
  qed
  show ?case unfolding book_simult_subst.simps named_logical_occurrences.simps
    by (rule NLam.IH[OF al restricted])
qed

definition book_subst_table_language ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'l set \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    ('c,'l) book_subst_table \<Rightarrow> bool" where
  "book_subst_table_language L \<Lambda> \<Sigma> G \<theta> \<longleftrightarrow>
    (\<forall>k B. map_of \<theta> k = Some B \<longrightarrow> book_in_language L \<Lambda> \<Sigma> G B (book_subst_key_type k))"

lemma book_subst_table_language_lookup:
  assumes language: "book_subst_table_language L \<Lambda> \<Sigma> G \<theta>" and found: "map_of \<theta> k = Some B"
  shows "book_in_language L \<Lambda> \<Sigma> G B (book_subst_key_type k)"
  using language found unfolding book_subst_table_language_def by blast

theorem book_simult_subst_language:
  assumes body: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and table: "book_subst_table_language L \<Lambda> \<Sigma> G \<theta>"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_simult_subst G \<theta> A) \<tau>"
proof -
  have payload_language: "\<And>k B. map_of \<theta> k = Some B \<Longrightarrow> book_in_language L \<Lambda> \<Sigma> G B (book_subst_key_type k)"
    by (rule book_subst_table_language_lookup[OF table]; assumption)
  have table_typed: "book_subst_table_typed L G \<theta>"
    unfolding book_subst_table_typed_def
    by (intro allI impI; rule book_language_type; rule payload_language; assumption)
  have typed: "has_ntype L G (book_simult_subst G \<theta> A) \<tau>"
    by (rule book_simult_subst_type[OF book_language_type[OF body] table_typed])
  have names: "named_in_signature \<Sigma> (book_simult_subst G \<theta> A)"
    by (rule book_simult_subst_signature[OF book_language_signature[OF body]];
        rule book_language_signature; rule payload_language; assumption)
  have logicals: "named_logical_occurrences (book_simult_subst G \<theta> A) \<subseteq> \<Lambda>"
    by (rule book_simult_subst_logical_occurrences[OF book_language_logical_occurrences[OF body]];
        rule book_language_logical_occurrences; rule payload_language; assumption)
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

section \<open>Independence from shadowed table entries\<close>

text \<open>
  Equal effective lookup gives the same replacement and the same free-for
  result. This is table extensionality, not a substitution-composition law.
\<close>

lemma book_subst_disable_map_eq:
  assumes maps: "map_of \<theta> = map_of \<eta>"
  shows "map_of (book_subst_disable k \<theta>) = map_of (book_subst_disable k \<eta>)"
  by (rule ext; simp only: book_subst_lookup_disable maps)

theorem book_simult_subst_map_eq:
  assumes maps: "map_of \<theta> = map_of \<eta>"
  shows "book_simult_subst G \<theta> A = book_simult_subst G \<eta> A"
  using maps
proof (induction A arbitrary: \<theta> \<eta>)
  case (NVar n)
  show ?case by (simp only: book_simult_subst.simps NVar.prems)
next
  case (NConst c \<sigma>)
  show ?case by (simp only: book_simult_subst.simps NConst.prems)
next
  case (NLogical l)
  show ?case by (simp only: book_simult_subst.simps)
next
  case (NApp F A)
  show ?case by (simp only: book_simult_subst.simps NApp.IH(1)[OF NApp.prems] NApp.IH(2)[OF NApp.prems])
next
  case (NLam n A)
  have restricted: "map_of (book_subst_disable (BSVar n (G n)) \<theta>) = map_of (book_subst_disable (BSVar n (G n)) \<eta>)"
    by (rule book_subst_disable_map_eq[OF NLam.prems])
  show ?case by (simp only: book_simult_subst.simps NLam.IH[OF restricted])
qed

theorem book_simult_free_for_map_eq:
  assumes maps: "map_of \<theta> = map_of \<eta>"
  shows "book_simult_free_for G \<theta> A = book_simult_free_for G \<eta> A"
  using maps
proof (induction A arbitrary: \<theta> \<eta>)
  case (NVar n)
  show ?case by (simp only: book_simult_free_for.simps)
next
  case (NConst c \<sigma>)
  show ?case by (simp only: book_simult_free_for.simps)
next
  case (NLogical l)
  show ?case by (simp only: book_simult_free_for.simps)
next
  case (NApp F A)
  show ?case by (simp only: book_simult_free_for.simps NApp.IH(1)[OF NApp.prems] NApp.IH(2)[OF NApp.prems])
next
  case (NLam n A)
  have restricted: "map_of (book_subst_disable (BSVar n (G n)) \<theta>) = map_of (book_subst_disable (BSVar n (G n)) \<eta>)"
    by (rule book_subst_disable_map_eq[OF NLam.prems])
  show ?case by (simp only: book_simult_free_for.simps NLam.IH[OF restricted] restricted)
qed

end
