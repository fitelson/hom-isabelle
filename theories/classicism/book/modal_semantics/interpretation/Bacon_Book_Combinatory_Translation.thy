theory Bacon_Book_Combinatory_Translation
  imports Bacon_Book_Environment_Development.Bacon_Book_Language
begin

section \<open>Typed elimination of abstraction using K, S and their derived identity\<close>

datatype 'c book_comb =
    BCVar nat | BCConst 'c otype | BCLogical book_minimal_logical
  | BCK otype otype | BCS otype otype otype | BCId otype
  | BCApp otype otype "'c book_comb" "'c book_comb"

fun book_comb_type :: "sgcontext \<Rightarrow> 'c book_comb \<Rightarrow> otype" where
  "book_comb_type G (BCVar n) = G n"
| "book_comb_type G (BCConst c \<sigma>) = \<sigma>"
| "book_comb_type G (BCLogical l) = book_minimal_logical_type l"
| "book_comb_type G (BCK \<sigma> \<tau>) = Arr \<sigma> (Arr \<tau> \<sigma>)"
| "book_comb_type G (BCS \<sigma> \<tau> \<rho>) = Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))"
| "book_comb_type G (BCId \<sigma>) = Arr \<sigma> \<sigma>"
| "book_comb_type G (BCApp \<sigma> \<tau> F A) = \<tau>"

inductive book_comb_typed :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_comb \<Rightarrow> otype \<Rightarrow> bool"
  for \<Sigma> G where
  Var: "book_comb_typed \<Sigma> G (BCVar n) (G n)"
| Const: "c \<in> \<Sigma> \<sigma> \<Longrightarrow> book_comb_typed \<Sigma> G (BCConst c \<sigma>) \<sigma>"
| Logical: "book_comb_typed \<Sigma> G (BCLogical l) (book_minimal_logical_type l)"
| K: "book_comb_typed \<Sigma> G (BCK \<sigma> \<tau>) (Arr \<sigma> (Arr \<tau> \<sigma>))"
| S: "book_comb_typed \<Sigma> G (BCS \<sigma> \<tau> \<rho>) (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>)))"
| Id: "book_comb_typed \<Sigma> G (BCId \<sigma>) (Arr \<sigma> \<sigma>)"
| App: "book_comb_typed \<Sigma> G F (Arr \<sigma> \<tau>) \<Longrightarrow> book_comb_typed \<Sigma> G A \<sigma> \<Longrightarrow>
    book_comb_typed \<Sigma> G (BCApp \<sigma> \<tau> F A) \<tau>"

lemma book_comb_type_correct:
  "book_comb_typed \<Sigma> G A \<tau> \<Longrightarrow> book_comb_type G A = \<tau>"
  by (induction rule: book_comb_typed.induct) simp_all

fun book_comb_result :: "otype \<Rightarrow> otype" where
  "book_comb_result (Arr \<sigma> \<tau>) = \<tau>"
| "book_comb_result Ind = Prop"
| "book_comb_result Prop = Prop"

definition book_comb_apply where
  "book_comb_apply G F A =
    BCApp (book_comb_type G A) (book_comb_result (book_comb_type G F)) F A"

lemma book_comb_apply_typed:
  assumes f: "book_comb_typed \<Sigma> G F (Arr \<sigma> \<tau>)" and a: "book_comb_typed \<Sigma> G A \<sigma>"
  shows "book_comb_typed \<Sigma> G (book_comb_apply G F A) \<tau>"
  unfolding book_comb_apply_def
  by (simp only: book_comb_type_correct[OF f] book_comb_type_correct[OF a] book_comb_result.simps;
    rule book_comb_typed.App[OF f a])

fun book_comb_abstract :: "sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_comb \<Rightarrow> 'c book_comb" where
  "book_comb_abstract G n (BCVar m) =
    (if n = m then BCId (G n) else book_comb_apply G (BCK (G m) (G n)) (BCVar m))"
| "book_comb_abstract G n (BCApp \<sigma> \<tau> F A) =
    book_comb_apply G (book_comb_apply G (BCS (G n) \<sigma> \<tau>) (book_comb_abstract G n F)) (book_comb_abstract G n A)"
| "book_comb_abstract G n A = book_comb_apply G (BCK (book_comb_type G A) (G n)) A"

theorem book_comb_abstract_typed:
  assumes typed: "book_comb_typed \<Sigma> G A \<tau>"
  shows "book_comb_typed \<Sigma> G (book_comb_abstract G n A) (Arr (G n) \<tau>)"
  using typed
  by (induction rule: book_comb_typed.induct)
    (auto simp: book_comb_abstract.simps book_comb_type.simps
      intro: book_comb_typed.intros book_comb_apply_typed)

fun book_combinatory_translation :: "sgcontext \<Rightarrow> ('c,book_minimal_logical) named_term \<Rightarrow> 'c book_comb" where
  "book_combinatory_translation G (NVar n) = BCVar n"
| "book_combinatory_translation G (NConst c \<sigma>) = BCConst c \<sigma>"
| "book_combinatory_translation G (NLogical l) = BCLogical l"
| "book_combinatory_translation G (NApp F A) =
    book_comb_apply G (book_combinatory_translation G F) (book_combinatory_translation G A)"
| "book_combinatory_translation G (NLam n A) = book_comb_abstract G n (book_combinatory_translation G A)"

lemma book_combinatory_translation_typed:
  assumes typed: "has_ntype book_minimal_logical_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
  shows "book_comb_typed \<Sigma> G (book_combinatory_translation G A) \<tau>"
  using typed names
  by (induction rule: has_ntype.induct)
    (auto intro: book_comb_typed.intros book_comb_apply_typed book_comb_abstract_typed)

theorem book_combinatory_translation_language:
  "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau> \<Longrightarrow>
    book_comb_typed \<Sigma> G (book_combinatory_translation G A) \<tau>"
  by (rule book_combinatory_translation_typed; rule book_language_type book_language_signature; assumption)

text \<open>
  This auxiliary syntax records the standard typed K/S abstraction
  elimination. BCId abbreviates the derived identity S K K, not a new
  logical constant. It changes neither the book's object language nor its
  proof calculus. Application annotations are checked by book_comb_typed.
  No semantic premise or richness of the variable stock is used.
\<close>

end
