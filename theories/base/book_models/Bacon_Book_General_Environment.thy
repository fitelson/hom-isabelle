theory Bacon_Book_General_Environment
  imports Bacon_Book_Full_Environment
begin

section \<open>Variable arguments need not be standalone terms of the language\<close>

text \<open>
  Definition 9.1, p.190, permits Fx∈𝒥 even when x∉𝒥. Its
  decomposition conditions ensure F∈𝒥 and ensure argument membership
  except in this variable case. Accordingly Definition 14.13, p.302,
  must give Jg(Fx)=App(Jg(F),g(x)) without requiring x∈𝒥.

  The earlier guarded environment supplies application when both operands
  are admitted. The following extension supplies precisely the missing
  variable-argument case. It does NOT assign values to unadmitted variables
  through the raw total function J, add conversion requirements outside
  𝒥, assert Functionality, or assert that a typed assignment exists.

  As before, admitted is only a term-collection parameter. Source use
  requires a separate proof of Definition 9.1's language conditions.
  This leaf does not declare every collection a general λ-language.
\<close>

locale book_general_environment_conditions = book_environment_conditions +
  assumes denote_app_variable:
    "F \<in> admitted \<Longrightarrow> NApp F (NVar n) \<in> admitted \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock F (Arr (stock n) \<tau>) \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow>
     denote g (NApp F (NVar n)) = app (stock n) \<tau> (denote g F) (g n)"

section \<open>The extra clause is redundant for admitted variables\<close>

context book_environment_conditions
begin

lemma book_admitted_variable_application:
  assumes head_member: "F \<in> admitted"
    and variable_member: "NVar n \<in> admitted"
    and application_member: "NApp F (NVar n) \<in> admitted"
    and head: "book_in_language logical_type logical_signature signature stock F (Arr (stock n) \<tau>)"
    and typed: "book_env_typed domain stock g"
  shows "denote g (NApp F (NVar n)) = app (stock n) \<tau> (denote g F) (g n)"
proof -
  have equation: "denote g (NApp F (NVar n)) =
    app (stock n) \<tau> (denote g F) (denote g (NVar n))"
    by (rule denote_app[OF head_member variable_member application_member head book_language_Var typed])
  show ?thesis by (simp only: equation denote_var[OF variable_member typed])
qed

end

section \<open>Restriction of a full interpretation\<close>

context book_full_environment
begin

theorem book_full_environment_general_restriction:
  "book_general_environment_conditions domain app logical_type logical_signature signature stock admitted denote"
proof -
  interpret Restricted: book_environment_conditions domain app logical_type logical_signature signature stock admitted denote
    by (unfold_locales;
      (rule app_type | rule denote_type[OF UNIV_I] | rule denote_var[OF UNIV_I] |
       rule denote_app[OF UNIV_I UNIV_I UNIV_I] | rule environment[OF UNIV_I UNIV_I]); assumption)
  show ?thesis
  proof (unfold book_general_environment_conditions_def,
      rule conjI[OF Restricted.book_environment_conditions_axioms], unfold_locales)
    fix F n \<tau> g
    assume head_member: "F \<in> admitted" and application_member: "NApp F (NVar n) \<in> admitted"
      and head: "book_in_language logical_type logical_signature signature stock F (Arr (stock n) \<tau>)"
      and typed: "book_env_typed domain stock g"
    show "denote g (NApp F (NVar n)) = app (stock n) \<tau> (denote g F) (g n)"
      by (rule book_admitted_variable_application[OF UNIV_I UNIV_I UNIV_I head typed])
  qed
qed

end

theorem book_general_full_environment_iff:
  "book_general_environment_conditions D app L \<Lambda> \<Sigma> G UNIV J \<longleftrightarrow>
    book_full_environment D app L \<Lambda> \<Sigma> G J"
proof
  assume general: "book_general_environment_conditions D app L \<Lambda> \<Sigma> G UNIV J"
  interpret General: book_general_environment_conditions D app L \<Lambda> \<Sigma> G UNIV J
    by (rule general)
  show "book_full_environment D app L \<Lambda> \<Sigma> G J" by unfold_locales
next
  assume full: "book_full_environment D app L \<Lambda> \<Sigma> G J"
  interpret Full: book_full_environment D app L \<Lambda> \<Sigma> G J by (rule full)
  show "book_general_environment_conditions D app L \<Lambda> \<Sigma> G UNIV J"
    by (rule Full.book_full_environment_general_restriction)
qed

end
