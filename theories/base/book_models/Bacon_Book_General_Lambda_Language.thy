theory Bacon_Book_General_Lambda_Language
  imports Bacon_Book_Source_Reduction Bacon_Book_Variable_Relettering_Syntax
begin

section \<open>The seven groups of conditions for a general λ-language\<close>

text \<open>
  𝒥τ is a collection of full-language terms of type τ. The clauses
  below transcribe Definition 9.1, p.190, using the printed free-for
  test and Definition 3.10's α-inclusive directed reduction.

  The source signature is represented by nonlogical constants Σ together
  with logical symbols Λ. Its constant-inclusion and constant-substitution
  clauses therefore each have two displayed cases. The variable and
  constant substitutions in source clause 6 are also displayed separately.
  These are subdivisions of the seven source groups, not additional
  closure requirements. Target variables in clause 7 need not belong to 𝒥.

  No unrestricted abstraction, standalone-variable membership, βη
  expansion closure, or model existence is assumed. Richness of the
  variable stock is a separate representation condition when used for
  the book's infinite stocks, not an extra language-closure clause.
\<close>

locale book_general_lambda_language =
  fixes L :: "'l \<Rightarrow> otype" and \<Lambda> :: "'l set" and \<Sigma> :: "'c ssignature"
    and G :: sgcontext and J :: "otype \<Rightarrow> ('c,'l) named_term set"
  assumes term_language: "A \<in> J \<tau> \<Longrightarrow> book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and nonlogical_constant: "c \<in> \<Sigma> \<tau> \<Longrightarrow> NConst c \<tau> \<in> J \<tau>"
    and logical_constant: "l \<in> \<Lambda> \<Longrightarrow> NLogical l \<in> J (L l)"
    and application: "F \<in> J (Arr \<sigma> \<tau>) \<Longrightarrow> A \<in> J \<sigma> \<Longrightarrow> NApp F A \<in> J \<tau>"
    and application_head: "NApp F A \<in> J \<tau> \<Longrightarrow> has_ntype L G F (Arr \<sigma> \<tau>) \<Longrightarrow> F \<in> J (Arr \<sigma> \<tau>)"
    and application_argument: "NApp F A \<in> J \<tau> \<Longrightarrow> has_ntype L G A \<sigma> \<Longrightarrow>
      \<not> (\<exists>n. A = NVar n) \<Longrightarrow> A \<in> J \<sigma>"
    and reduction: "A \<in> J \<tau> \<Longrightarrow> book_source_reduces G A B \<Longrightarrow> B \<in> J \<tau>"
    and variable_substitution: "A \<in> J \<tau> \<Longrightarrow> B \<in> J (G n) \<Longrightarrow>
      book_printed_free_for B n A \<Longrightarrow> named_subst n B A \<in> J \<tau>"
    and constant_substitution: "A \<in> J \<tau> \<Longrightarrow> c \<in> \<Sigma> \<sigma> \<Longrightarrow> B \<in> J \<sigma> \<Longrightarrow>
      book_printed_free_for B 0 A \<Longrightarrow> book_const_subst c \<sigma> B A \<in> J \<tau>"
    and logical_substitution: "A \<in> J \<tau> \<Longrightarrow> l \<in> \<Lambda> \<Longrightarrow> B \<in> J (L l) \<Longrightarrow>
      book_printed_free_for B 0 A \<Longrightarrow> book_logical_subst l B A \<in> J \<tau>"
    and relettering: "A \<in> J \<tau> \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys \<Longrightarrow>
      set xs \<subseteq> named_fv A \<Longrightarrow> list_all2 (\<lambda>x y. G x = G y) xs ys \<Longrightarrow>
      (\<And>x y. (x,y) \<in> set (zip xs ys) \<Longrightarrow> book_printed_free_for (NVar y) x A) \<Longrightarrow>
      book_variable_reletter G xs ys A \<in> J \<tau>"
begin

theorem book_general_application_parts:
  assumes member: "NApp F A \<in> J \<tau>"
  obtains \<sigma> where "F \<in> J (Arr \<sigma> \<tau>)"
    and "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    and "A \<in> J \<sigma> \<or> (\<exists>n. A = NVar n)"
proof -
  obtain \<sigma> where fl: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF term_language[OF member]]; rule that; assumption)
  have fm: "F \<in> J (Arr \<sigma> \<tau>)"
    by (rule application_head[OF member book_language_type[OF fl]])
  have am: "A \<in> J \<sigma> \<or> (\<exists>n. A = NVar n)"
    using application_argument[OF member book_language_type[OF al]] by blast
  show thesis by (rule that[OF fm al am])
qed

lemma book_general_alpha_closed:
  assumes member: "A \<in> J \<tau>" and alpha: "named_alpha G A B"
  shows "B \<in> J \<tau>"
  by (rule reduction[OF member book_source_reduces_alpha[OF alpha]])

end

end
