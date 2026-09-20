theory Goodman_Translation_Support
  imports Goodman_Constructor_Translation
begin

section \<open>Free-variable containment and closed logical terms\<close>

text \<open>
  Every free name of a translated well-typed term occurs in its slot chart.
  Consequently translating an empty-context term yields a closed term.
  This syntactic inclusion is not equality of denotational stocks; neither
  semantic preservation nor the reverse translation is asserted here.
\<close>

theorem gi_to_book_fv_subset:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>" and chart: "map G ns = \<Gamma>"
  shows "named_fv (gi_to_book G ns k A) \<subseteq> set ns"
  using typed chart
proof (induction arbitrary: ns rule: has_type.induct)
  case Var
  then show ?case by (auto simp: lookup_def split: if_splits)
next
  case Const
  then show ?case by simp
next
  case App
  then show ?case by auto
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  have body: "named_fv (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k A)
    \<subseteq> set (named_chart_fresh G ns \<sigma> # ns)"
    by (rule Lam.IH[OF gi_chart_extension[OF rich Lam.prems]])
  show ?case using body by (auto simp: Let_def)
next
  case Eq
  then show ?case by (auto simp: book_leibniz_fv)
next
  case Neg
  then show ?case by (auto simp: book_not_fv)
next
  case Conj
  then show ?case by (auto simp: book_and_fv)
next
  case Disj
  then show ?case by (auto simp: book_or_fv)
next
  case Imp
  then show ?case by (auto simp: book_imp_fv)
next
  case (Forall \<sigma> \<Gamma> A)
  have body: "named_fv (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k A)
    \<subseteq> set (named_chart_fresh G ns \<sigma> # ns)"
    by (rule Forall.IH[OF gi_chart_extension[OF rich Forall.prems]])
  show ?case using body by (auto simp: Let_def book_all_fv)
next
  case (Exists \<sigma> \<Gamma> A)
  have body: "named_fv (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k A)
    \<subseteq> set (named_chart_fresh G ns \<sigma> # ns)"
    by (rule Exists.IH[OF gi_chart_extension[OF rich Exists.prems]])
  show ?case using body by (auto simp: Let_def book_exists_fv)
qed

corollary gi_closed_translation:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> A : \<tau>"
  shows "named_fv (gi_to_book G [] k A) = {}"
  using gi_to_book_fv_subset[OF rich typed, where ns="[]" and k=k] by simp

theorem gi_closed_logical_translation:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> A : \<tau>"
    and logical: "gi_constants_admitted k (\<lambda>_. {}) A"
  shows "gb_closed_logical G \<tau> (gi_to_book G [] k A)"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G (gi_to_book G [] k A) \<tau>"
    by (rule gi_to_book_language[OF rich typed _ logical]; simp)
  show ?thesis unfolding gb_closed_logical_def
    by (rule conjI[OF language gi_closed_translation[OF rich typed]])
qed

corollary gi_translated_logical_purity_instance:
  "sg_rich G \<Longrightarrow> [] \<turnstile> A : \<tau> \<Longrightarrow> gi_constants_admitted k (\<lambda>_. {}) A \<Longrightarrow>
    gb_pure \<tau> (gi_to_book G [] k A) \<in> gb_purity_schema G"
  using gi_closed_logical_translation
  unfolding gb_purity_schema_def by blast

end
