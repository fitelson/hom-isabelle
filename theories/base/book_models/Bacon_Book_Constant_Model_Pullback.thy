theory Bacon_Book_Constant_Model_Pullback
  imports Bacon_Book_Constant_Renaming_Conversion Bacon_Book_Full_Minimal_Model
begin

section \<open>Pulling back denotation while retaining the semantic carrier\<close>

text \<open>
  Given f[Σσ]⊆Ωσ, put J′g(A)=Jg(f(A)). The domains, typed
  application, variable stock, valuation, and logical values stay fixed.
  Source role: returning the expanded-language construction on Bacon
  pp.320–321 to the original signature; environment and logical clauses
  are those of Definitions 14.13 and 15.1, pp.302 and 314–315.

  This is a forward model transport. No injectivity or richness is needed.
  In particular it asserts no reflection along f. An input full minimal
  model is a genuine premise of the transport, not a model-existence seed.
\<close>

definition book_constant_pullback_denote ::
  "((nat \<Rightarrow> 'v) \<Rightarrow> ('d,'l) named_term \<Rightarrow> 'v) \<Rightarrow>
    ('c \<Rightarrow> 'd) \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v" where
  "book_constant_pullback_denote J f g A = J g (book_constant_rename f A)"

context book_full_environment
begin

lemma book_constant_pullback_type:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
    and language: "book_in_language logical_type logical_signature \<Sigma> stock A \<tau>"
    and typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g A \<in> domain \<tau>"
proof -
  have renamed: "book_in_language logical_type logical_signature signature stock (book_constant_rename f A) \<tau>"
    by (rule book_constant_rename_language[OF language maps])
  show ?thesis unfolding book_constant_pullback_denote_def
    by (rule denote_type[OF UNIV_I renamed typed])
qed

lemma book_constant_pullback_var:
  assumes typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g (NVar n) = g n"
  by (simp only: book_constant_pullback_denote_def book_constant_rename_simps;
      rule denote_var[OF UNIV_I typed])

lemma book_constant_pullback_app:
  assumes maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> signature \<rho>"
    and head: "book_in_language logical_type logical_signature \<Sigma> stock F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language logical_type logical_signature \<Sigma> stock A \<sigma>"
    and typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g (NApp F A) =
    app \<sigma> \<tau> (book_constant_pullback_denote denote f g F) (book_constant_pullback_denote denote f g A)"
proof -
  have mapped_head: "book_in_language logical_type logical_signature signature stock (book_constant_rename f F) (Arr \<sigma> \<tau>)"
    by (rule book_constant_rename_language[OF head maps])
  have mapped_argument: "book_in_language logical_type logical_signature signature stock (book_constant_rename f A) \<sigma>"
    by (rule book_constant_rename_language[OF argument maps])
  show ?thesis by (simp only: book_constant_pullback_denote_def book_constant_rename_simps;
      rule denote_app[OF UNIV_I UNIV_I UNIV_I mapped_head mapped_argument typed])
qed

lemma book_constant_pullback_environment:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
    and first: "book_in_language logical_type logical_signature \<Sigma> stock A \<tau>"
    and second: "book_in_language logical_type logical_signature \<Sigma> stock B \<tau>"
    and conversion: "named_raw_beta_eta logical_type stock \<tau> A B"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and overlap: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "book_constant_pullback_denote denote f g A = book_constant_pullback_denote denote f h B"
proof -
  have mapped_first: "book_in_language logical_type logical_signature signature stock (book_constant_rename f A) \<tau>"
    by (rule book_constant_rename_language[OF first maps])
  have mapped_second: "book_in_language logical_type logical_signature signature stock (book_constant_rename f B) \<tau>"
    by (rule book_constant_rename_language[OF second maps])
  have mapped_conversion: "named_raw_beta_eta logical_type stock \<tau> (book_constant_rename f A) (book_constant_rename f B)"
    by (rule book_constant_rename_raw_conversion[OF conversion])
  show ?thesis unfolding book_constant_pullback_denote_def
  proof (rule environment[OF UNIV_I UNIV_I mapped_first mapped_second mapped_conversion gt ht])
    fix n
    assume shared: "n \<in> named_fv (book_constant_rename f A) \<inter> named_fv (book_constant_rename f B)"
    have original_shared: "n \<in> named_fv A \<inter> named_fv B"
      using shared by (simp only: book_constant_rename_fv)
    show "g n = h n" by (rule overlap[OF original_shared])
  qed
qed

theorem book_constant_pullback_full_environment:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
  shows "book_full_environment domain app logical_type logical_signature \<Sigma> stock
    (book_constant_pullback_denote denote f)"
  by (unfold_locales;
      (rule app_type | rule book_constant_pullback_type[OF maps] |
       rule book_constant_pullback_var | rule book_constant_pullback_app[OF maps] |
       rule book_constant_pullback_environment[OF maps]); assumption)

end

section \<open>Logical values keep their actual assignment witnesses\<close>

text \<open>
  A logical symbol is unchanged by f. The input model already provides
  a typed total assignment; at that assignment J′g(l)=Jg(l)=κ(l).
  This supplies the required witnessed closed values, without choosing
  an assignment from an empty collection. The material, universal, and
  false-proposition clauses use unchanged D, App, v and κ.
  The conclusion retains the qualified full-language minimal-basis scope.
\<close>

context book_full_minimal_model
begin

theorem book_constant_pullback_full_minimal_model:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
  shows "book_full_minimal_model domain app \<Sigma> stock (book_constant_pullback_denote denote f) V \<kappa>"
proof -
  interpret Pull: book_full_environment domain app book_minimal_logical_type UNIV \<Sigma> stock
    "book_constant_pullback_denote denote f"
    by (rule book_constant_pullback_full_environment[OF maps])
  obtain g0 where typed: "book_env_typed domain stock g0"
    using book_minimal_assignment_exists by (elim exE)
  have logicals: "Pull.book_closed_value (book_minimal_logical_type l) (NLogical l) (\<kappa> l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> stock
      (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have value_eq: "book_constant_pullback_denote denote f g0 (NLogical l) = \<kappa> l"
      by (simp only: book_constant_pullback_denote_def book_constant_rename_simps;
          rule book_minimal_logical_value_at[OF typed])
    have witnessed: "Pull.book_closed_value (book_minimal_logical_type l) (NLogical l)
      (book_constant_pullback_denote denote f g0 (NLogical l))"
      by (rule Pull.book_closed_value_intro[OF UNIV_I language closed typed])
    show ?thesis using witnessed by (simp only: value_eq)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def,
      rule conjI[OF Pull.book_full_environment_axioms], unfold_locales)
    fix l
    show "Pull.book_closed_value (book_minimal_logical_type l) (NLogical l) (\<kappa> l)"
      by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> domain Prop" and qm: "q \<in> domain Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) p) q) = (V p \<longrightarrow> V q)"
      by (rule implication_truth[OF pm qm])
  next
    fix \<sigma> h
    assume hm: "h \<in> domain (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (\<kappa> (SBAll \<sigma>)) h) =
      (\<forall>a\<in>domain \<sigma>. V (app \<sigma> Prop h a))"
      by (rule forall_truth[OF hm])
  next
    show "\<exists>a\<in>domain Prop. \<not> V a" by (rule false_proposition)
  qed
qed

end

end
