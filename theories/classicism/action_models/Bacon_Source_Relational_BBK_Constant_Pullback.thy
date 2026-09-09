theory Bacon_Source_Relational_BBK_Constant_Pullback
  imports Bacon_Source_Relational_BBK_Interface Bacon_Source_Relational_Constant_Map_Binding
begin

section \<open>Pull back the interpretation along a nonlogical constant map\<close>

definition paper_R_constant_pullback_denote ::
  "('c \<Rightarrow> 'd) \<Rightarrow> ('v named_assignment \<Rightarrow> 'd paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v" where
  "paper_R_constant_pullback_denote f J g A = J g (paper_R_constant_map f A)"

lemma paper_R_constant_map_adequate:
  "named_adequate g (paper_R_constant_map f A) \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_R_constant_map_fv)

text \<open>
  Given an independent R-BBK model over Ω and f(Σρ)⊆Ωρ,
  keep D, V and the variable stock G and put JΣ(g,A)=JΩ(g,f(A)).
  Source role: restriction to the original signature in Theorem 3.2,
  footnote 64, p.45.

  Constant-name carriers may differ, and the value carrier is an
  arbitrary HOL type. No injectivity is needed for this forward
  pullback. The input model is supplied explicitly; no Henkin,
  canonical-model, F-model or proof-theoretic premise occurs.
  Every partial-assignment guard is preserved because f fixes all
  variable occurrences, binders, and the logical alphabet.
\<close>

theorem paper_R_bbk_constant_pullback:
  assumes model: "paper_R_bbk_model \<Omega> G D J V"
    and maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> \<Omega> \<rho>"
  shows "paper_R_bbk_model \<Sigma> G D (paper_R_constant_pullback_denote f J) V"
proof -
  interpret Original: paper_R_bbk_model \<Omega> G D J V by (rule model)
  have language: "paper_R_in_language \<Omega> G (paper_R_constant_map f A) \<rho>"
    if "paper_R_in_language \<Sigma> G A \<rho>" for A \<rho>
    by (rule paper_R_constant_map_language[OF that maps])
  have adequate: "named_adequate g (paper_R_constant_map f A)"
    if "named_adequate g A" for g A
    by (rule iffD2[OF paper_R_constant_map_adequate that])
  show ?thesis
  proof (rule paper_R_bbk_model.intro)
    show "paper_R_rich G" by (rule Original.stock_rich)
  next
    fix \<sigma>
    assume rt: "paper_R_type \<sigma>"
    show "D \<sigma> \<noteq> {}" by (rule Original.domain_nonempty[OF rt])
  next
    fix \<sigma>
    assume outside: "\<not> paper_R_type \<sigma>"
    show "D \<sigma> = {}" by (rule Original.domain_empty[OF outside])
  next
    fix A \<rho> g
    assume al: "paper_R_in_language \<Sigma> G A \<rho>"
      and gt: "named_env_typed D G g" and ga: "named_adequate g A"
    show "paper_R_constant_pullback_denote f J g A \<in> D \<rho>"
      unfolding paper_R_constant_pullback_denote_def
      by (rule Original.denote_type[OF language[OF al] gt adequate[OF ga]])
  next
    fix g n a
    assume gt: "named_env_typed D G g" and assigned: "g n = Some a"
    show "paper_R_constant_pullback_denote f J g (NVar n) = a"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.denote_var[OF gt assigned])
  next
    fix F \<sigma> \<tau> A H \<upsilon> \<rho> B g k
    assume fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and al: "paper_R_in_language \<Sigma> G A \<sigma>"
      and hl: "paper_R_in_language \<Sigma> G H (Arr \<upsilon> \<rho>)" and bl: "paper_R_in_language \<Sigma> G B \<upsilon>"
      and gt: "named_env_typed D G g" and kt: "named_env_typed D G k"
      and ga: "named_adequate g (NApp F A)" and ka: "named_adequate k (NApp H B)"
      and heads: "paper_R_constant_pullback_denote f J g F = paper_R_constant_pullback_denote f J k H"
      and arguments: "paper_R_constant_pullback_denote f J g A = paper_R_constant_pullback_denote f J k B"
    have gmap: "named_adequate g (NApp (paper_R_constant_map f F) (paper_R_constant_map f A))"
      using adequate[OF ga] by (simp only: paper_R_constant_map_simps)
    have kmap: "named_adequate k (NApp (paper_R_constant_map f H) (paper_R_constant_map f B))"
      using adequate[OF ka] by (simp only: paper_R_constant_map_simps)
    have head_eq: "J g (paper_R_constant_map f F) = J k (paper_R_constant_map f H)"
      using heads by (simp only: paper_R_constant_pullback_denote_def)
    have arg_eq: "J g (paper_R_constant_map f A) = J k (paper_R_constant_map f B)"
      using arguments by (simp only: paper_R_constant_pullback_denote_def)
    show "paper_R_constant_pullback_denote f J g (NApp F A) = paper_R_constant_pullback_denote f J k (NApp H B)"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.denote_application_cong[OF language[OF fl] language[OF al] language[OF hl]
          language[OF bl] gt kt gmap kmap head_eq arg_eq])
  next
    fix A \<rho> g k
    assume al: "paper_R_in_language \<Sigma> G A \<rho>"
      and gt: "named_env_typed D G g" and kt: "named_env_typed D G k"
      and ga: "named_adequate g A" and ka: "named_adequate k A"
      and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
    have mapped_agree: "g n = k n" if "n \<in> named_fv (paper_R_constant_map f A)" for n
      by (rule agree; use that in \<open>simp only: paper_R_constant_map_fv\<close>)
    show "paper_R_constant_pullback_denote f J g A = paper_R_constant_pullback_denote f J k A"
      unfolding paper_R_constant_pullback_denote_def
      by (rule Original.denote_locality[OF language[OF al] gt kt adequate[OF ga] adequate[OF ka] mapped_agree])
  next
    fix \<rho> A B g
    assume conversion: "paper_R_raw_beta_eta G \<rho> A B"
      and al: "paper_R_in_language \<Sigma> G A \<rho>" and bl: "paper_R_in_language \<Sigma> G B \<rho>"
      and gt: "named_env_typed D G g" and ga: "named_adequate g A" and gb: "named_adequate g B"
    show "paper_R_constant_pullback_denote f J g A = paper_R_constant_pullback_denote f J g B"
      unfolding paper_R_constant_pullback_denote_def
      by (rule Original.denote_beta_eta[OF paper_R_constant_map_raw_conversion[where f=f, OF conversion]
        language[OF al] language[OF bl] gt adequate[OF ga] adequate[OF gb]])
  next
    fix A g
    assume al: "paper_R_in_language \<Sigma> G A Prop" and gt: "named_env_typed D G g" and ga: "named_adequate g A"
    show "V (paper_R_constant_pullback_denote f J g (NApp (NLogical SNot) A)) =
      (\<not> V (paper_R_constant_pullback_denote f J g A))"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_neg[OF language[OF al] gt adequate[OF ga]])
  next
    fix A B g
    assume al: "paper_R_in_language \<Sigma> G A Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
      and gt: "named_env_typed D G g" and ga: "named_adequate g A" and gb: "named_adequate g B"
    show "V (paper_R_constant_pullback_denote f J g (NApp (NApp (NLogical SAnd) A) B)) =
      (V (paper_R_constant_pullback_denote f J g A) \<and> V (paper_R_constant_pullback_denote f J g B))"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_conj[OF language[OF al] language[OF bl] gt adequate[OF ga] adequate[OF gb]])
  next
    fix A B g
    assume al: "paper_R_in_language \<Sigma> G A Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
      and gt: "named_env_typed D G g" and ga: "named_adequate g A" and gb: "named_adequate g B"
    show "V (paper_R_constant_pullback_denote f J g (NApp (NApp (NLogical SOr) A) B)) =
      (V (paper_R_constant_pullback_denote f J g A) \<or> V (paper_R_constant_pullback_denote f J g B))"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_disj[OF language[OF al] language[OF bl] gt adequate[OF ga] adequate[OF gb]])
  next
    fix F \<sigma> g n
    assume fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
      and gt: "named_env_typed D G g" and ga: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    have mapped_fresh: "n \<notin> named_fv (paper_R_constant_map f F)"
      by (simp only: paper_R_constant_map_fv; rule fresh)
    show "V (paper_R_constant_pullback_denote f J g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>D \<sigma>. V (paper_R_constant_pullback_denote f J (g(n := Some a)) (NApp F (NVar n))))"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_forall[OF language[OF fl] gt adequate[OF ga] nt mapped_fresh])
  next
    fix F \<sigma> g n
    assume fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
      and gt: "named_env_typed D G g" and ga: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    have mapped_fresh: "n \<notin> named_fv (paper_R_constant_map f F)"
      by (simp only: paper_R_constant_map_fv; rule fresh)
    show "V (paper_R_constant_pullback_denote f J g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>D \<sigma>. V (paper_R_constant_pullback_denote f J (g(n := Some a)) (NApp F (NVar n))))"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_exists[OF language[OF fl] gt adequate[OF ga] nt mapped_fresh])
  next
    fix A \<sigma> B g
    assume al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
      and gt: "named_env_typed D G g" and ga: "named_adequate g A" and gb: "named_adequate g B"
    show "V (paper_R_constant_pullback_denote f J g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
      (paper_R_constant_pullback_denote f J g A = paper_R_constant_pullback_denote f J g B)"
      by (simp only: paper_R_constant_pullback_denote_def paper_R_constant_map_simps;
        rule Original.valuation_identity[OF language[OF al] language[OF bl] gt adequate[OF ga] adequate[OF gb]])
  qed
qed

end
