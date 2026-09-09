theory Bacon_Source_Relational_Profile_Restriction
  imports Bacon_Source_Relational_Intension Bacon_Source_Relational_Application_Profile_Action
begin

section \<open>Profiles depend only on outgoing arrows at their object\<close>

text \<open>
  If two arrow collections have exactly the same arrows with source M,
  they give the same val𝒞M, app𝒞M and int𝒞M. Source: Definition
  3.10, p.50; this is the raw preservation fact needed when discarding
  unreachable objects in Proposition 3.22, p.57.

  Object records, arrow records, domains, maps, J and V are unchanged.
  Only the membership test for the arrow collection varies. No model,
  category, R-type, or semantic-domain membership premise is required
  for these defining equalities. Applicative profiles agree as total
  functions because their common off-pair-domain extension is undefined.
  Replacing model records or recoding values would need a separate bridge.
\<close>

lemma paper_R_truth_profile_outgoing_cong:
  assumes outgoing: "\<And>h. (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
    (h \<in> Arrows \<and> paper_arrow_source h = M)"
  shows "paper_bbk_truth_profile_on NewArrows M p = paper_bbk_truth_profile_on Arrows M p"
proof (rule set_eqI)
  fix h
  show "(h \<in> paper_bbk_truth_profile_on NewArrows M p) =
      (h \<in> paper_bbk_truth_profile_on Arrows M p)"
    using outgoing[of h] by (auto simp only: paper_bbk_truth_profile_on_member)
qed

lemma paper_R_app_profile_outgoing_cong:
  fixes \<Sigma> :: "'c ssignature" and d :: 'v
  assumes outgoing: "\<And>h. (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
    (h \<in> Arrows \<and> paper_arrow_source h = M)"
  shows "paper_R_app_profile_on \<Sigma> G NewArrows M \<sigma> \<tau> d =
    paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d"
proof (rule ext)
  fix z :: "('c,'v) paper_R_bbk_arrow \<times> 'v"
  obtain h a where pair: "z = (h,a)" by (cases z) auto
  have guard: "(h \<in> NewArrows \<and> paper_arrow_source h = M \<and>
      a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>) =
    (h \<in> Arrows \<and> paper_arrow_source h = M \<and>
      a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>)"
    using outgoing[of h] by blast
  show "paper_R_app_profile_on \<Sigma> G NewArrows M \<sigma> \<tau> d z =
      paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d z"
    by (simp only: pair paper_R_app_profile_on_def prod.case guard)
qed

lemma paper_R_intension_outgoing_cong:
  fixes \<Sigma> :: "'c ssignature" and d :: 'v
  assumes outgoing: "\<And>h. (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
    (h \<in> Arrows \<and> paper_arrow_source h = M)"
  shows "paper_R_intension_on \<Sigma> G NewArrows M \<sigma>s d =
    paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d"
proof (rule set_eqI)
  fix z :: "('c,'v) paper_R_bbk_arrow \<times> 'v list"
  obtain h xs where pair: "z = (h,xs)" by (cases z) auto
  show "(z \<in> paper_R_intension_on \<Sigma> G NewArrows M \<sigma>s d) =
      (z \<in> paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d)"
    using outgoing[of h] by (auto simp only: pair paper_R_intension_on_member)
qed

end
