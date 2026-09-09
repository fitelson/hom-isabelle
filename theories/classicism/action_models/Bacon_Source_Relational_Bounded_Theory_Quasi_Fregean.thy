theory Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean
  imports Bacon_Source_Relational_Bounded_Theory_Separation Bacon_Source_Relational_Truth_Profile
begin

section \<open>The actual bounded model category is quasi-Fregean\<close>

theorem paper_R_bounded_theory_quasi_fregean:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and theory_h: "paper_R_H_theory \<Sigma> G T" and pe: "paper_R_PE_closed \<Sigma> G T"
  shows "paper_bbk_quasi_fregean_on (paper_R_bounded_theory_models \<Sigma> G U T)
    (paper_R_bounded_theory_arrows \<Sigma> G U T)"
proof (unfold paper_bbk_quasi_fregean_on_def, intro ballI)
  fix M
  assume object: "M \<in> paper_R_bounded_theory_models \<Sigma> G U T"
  show "inj_on (paper_bbk_truth_profile_on (paper_R_bounded_theory_arrows \<Sigma> G U T) M) (paper_bbk_domain M Prop)"
  proof (rule inj_onI)
    fix p q
    assume pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop"
      and profiles: "paper_bbk_truth_profile_on (paper_R_bounded_theory_arrows \<Sigma> G U T) M p =
        paper_bbk_truth_profile_on (paper_R_bounded_theory_arrows \<Sigma> G U T) M q"
    show "p = q"
    proof (rule ccontr)
      assume different: "p \<noteq> q"
      obtain r where arrow: "r \<in> paper_R_bounded_theory_arrows \<Sigma> G U T" and src: "paper_arrow_source r = M"
        and separated: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
          paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
        by (rule paper_R_bounded_theory_separating_arrow[OF infinite names theory_h pe object pm qm different])
      have equality: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) =
          paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
        using iffD1[OF paper_bbk_truth_profile_on_eq_iff profiles] arrow src by blast
      show False using separated equality by contradiction
    qed
  qed
qed

text \<open>
  Profile injectivity is proved for every actual object using a separating
  arrow in the same bounded category. No object is assumed to exist:
  the theorem also covers the empty object set. Consistency and category
  inhabitation are separate questions. This is the fixed-carrier, set-sized
  quasi-Fregean conclusion, not a proper-class or quasi-functional claim.
\<close>

end
