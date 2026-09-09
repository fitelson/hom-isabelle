theory Bacon_Book_Full_Classicism_Signature_Conservativity
  imports Bacon_Book_Full_Classicism_Retraction
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Signature_Monotonicity
begin

section \<open>Changing the declared signature without changing an old theorem\<close>

theorem book_full_C_foreign_constants_eliminate:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
    and old_names: "named_in_signature \<Omega> A"
  shows "book_full_C_proves \<Omega> G A"
proof -
  obtain N where support: "book_full_C_retraction_support \<Omega> G A N"
    using book_full_C_retraction_support_exists[where \<Omega>=\<Omega>, OF rich derivation] by blast
  have finite: "finite N" using support unfolding book_full_C_retraction_support_def by blast
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" and avoids: "\<And>\<tau>. ?v \<tau> \<notin> N"
    using chosen by blast+
  have retracted: "book_full_C_proves \<Omega> G (named_retract \<Omega> ?v A)"
    by (rule book_full_C_retraction_apply[OF support stock avoids])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF old_names])
qed

theorem book_full_C_signature_mono:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "book_full_C_proves \<Omega> G A"
proof -
  have maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> c \<in> \<Omega> \<tau>"
    by (rule subsetD[OF inclusion]; assumption)
  have transported: "book_full_C_proves \<Omega> G (book_typed_name_map (\<lambda>\<tau> c. c) A)"
    by (rule book_full_C_typed_name_map[where \<rho>="\<lambda>\<tau> c. c", OF rich derivation maps])
  show ?thesis using transported by (simp only: book_typed_name_map_id)
qed

theorem book_full_C_signature_conservativity:
  assumes rich: "sg_rich G" and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
    and old_names: "named_in_signature \<Sigma> A"
  shows "book_full_C_proves \<Omega> G A \<longleftrightarrow> book_full_C_proves \<Sigma> G A"
proof
  assume enlarged: "book_full_C_proves \<Omega> G A"
  show "book_full_C_proves \<Sigma> G A"
    by (rule book_full_C_foreign_constants_eliminate[where \<Sigma>=\<Omega> and \<Omega>=\<Sigma>, OF rich enlarged old_names])
next
  assume original: "book_full_C_proves \<Sigma> G A"
  show "book_full_C_proves \<Omega> G A"
    by (rule book_full_C_signature_mono[where \<Sigma>=\<Sigma> and \<Omega>=\<Omega>, OF rich original inclusion])
qed

text \<open>
  Full-C theoremhood is conservative for declared-signature extension.
  The reverse direction uses the actual five-constructor retraction proof,
  including MF; the forward direction is typed name transport with the
  identity map. No base-consistency or model assumption is substituted
  for full-C theoremhood.
\<close>

end
