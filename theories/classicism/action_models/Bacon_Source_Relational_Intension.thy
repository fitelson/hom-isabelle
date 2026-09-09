theory Bacon_Source_Relational_Intension
  imports Bacon_Source_Relational_Vector_Application
    Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Relation intensions for the default R language\<close>

text \<open>
  For ρ=σ₁→⋯→σₙ→t, the intension of d∈Mρ records each
  outgoing h:M→N and each tuple aᵢ∈Nσᵢ for which
  valN(appᴺ(hρd)(a₁)…(aₙ)) holds.
  Source: Bacon–Dorr Definition 3.10, p.50. The type list is
  recursively in R when used semantically. Arguments range over the
  complete target domains, not just images of source arguments.

  Representation: pairs (h,ā) replace the source's varying-length tuples.
  The arrow record and truth-profile set are shared data constructions;
  application here is reconstructed from the independent R interpretation,
  not the F model predicate. Arrows is an explicit chosen collection.
  This definition alone asserts neither category laws nor injectivity.
\<close>

definition paper_R_intension_on ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> otype list \<Rightarrow> 'v \<Rightarrow>
    (('c,'v) paper_bbk_arrow \<times> 'v list) set" where
  "paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d =
    {(h,xs). h \<in> Arrows \<and> paper_arrow_source h = M \<and>
      paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) \<sigma>s xs \<and>
      paper_bbk_valuation (paper_arrow_target h)
        (paper_R_apply_vector \<Sigma> G
          (paper_bbk_domain (paper_arrow_target h))
          (paper_bbk_denote (paper_arrow_target h)) \<sigma>s
          (paper_arrow_map h (paper_type_vector \<sigma>s Prop) d) xs)}"

lemma paper_R_intension_on_member:
  "(h,xs) \<in> paper_R_intension_on \<Sigma> G Arrows M \<sigma>s d \<longleftrightarrow>
    h \<in> Arrows \<and> paper_arrow_source h = M \<and>
    paper_R_vector_args (paper_bbk_domain (paper_arrow_target h)) \<sigma>s xs \<and>
    paper_bbk_valuation (paper_arrow_target h)
      (paper_R_apply_vector \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma>s
        (paper_arrow_map h (paper_type_vector \<sigma>s Prop) d) xs)"
  by (simp only: paper_R_intension_on_def mem_Collect_eq case_prod_conv)

theorem paper_R_intension_zeroary:
  "paper_R_intension_on \<Sigma> G Arrows M [] p =
    image (\<lambda>h. (h,[])) (paper_bbk_truth_profile_on Arrows M p)"
  by (auto simp: paper_R_intension_on_member paper_bbk_truth_profile_on_member)

theorem paper_R_intension_zeroary_eq_iff:
  "paper_R_intension_on \<Sigma> G Arrows M [] p =
      paper_R_intension_on \<Sigma> G Arrows M [] q \<longleftrightarrow>
    paper_bbk_truth_profile_on Arrows M p = paper_bbk_truth_profile_on Arrows M q"
  by (auto simp: paper_R_intension_zeroary)

definition paper_R_intensional_on ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_bbk_arrow set \<Rightarrow> bool" where
  "paper_R_intensional_on \<Sigma> G Obj Arrows \<longleftrightarrow>
    (\<forall>M\<in>Obj. \<forall>\<sigma>s. list_all paper_R_type \<sigma>s \<longrightarrow>
      inj_on (paper_R_intension_on \<Sigma> G Arrows M \<sigma>s)
        (paper_bbk_domain M (paper_type_vector \<sigma>s Prop)))"

text \<open>
  Definition 3.11 requires injectivity at every relational type, including t.
  The R type-decomposition theorem justifies the vector indexing. Hence
  intensionality entails quasi-Fregeanness by taking the empty vector.
  This implication needs no model existence or additional separation axiom.
\<close>

theorem paper_R_intensional_implies_quasi_fregean:
  assumes intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  shows "paper_bbk_quasi_fregean_on Obj Arrows"
proof (unfold paper_bbk_quasi_fregean_on_def, intro ballI)
  fix M
  assume object: "M \<in> Obj"
  have all_types: "\<forall>\<sigma>s. list_all paper_R_type \<sigma>s \<longrightarrow>
      inj_on (paper_R_intension_on \<Sigma> G Arrows M \<sigma>s)
        (paper_bbk_domain M (paper_type_vector \<sigma>s Prop))"
    using intensional object unfolding paper_R_intensional_on_def by blast
  have injective: "inj_on (paper_R_intension_on \<Sigma> G Arrows M [])
      (paper_bbk_domain M Prop)"
    using spec[OF all_types, where x="[]"] by simp
  show "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
  proof (rule inj_onI)
    fix p q
    assume pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop"
      and equal: "paper_bbk_truth_profile_on Arrows M p = paper_bbk_truth_profile_on Arrows M q"
    have profiles: "paper_R_intension_on \<Sigma> G Arrows M [] p =
      paper_R_intension_on \<Sigma> G Arrows M [] q"
      by (rule iffD2[OF paper_R_intension_zeroary_eq_iff equal])
    show "p = q" by (rule inj_onD[OF injective profiles pm qm])
  qed
qed

end
