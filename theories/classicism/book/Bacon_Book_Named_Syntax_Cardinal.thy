theory Bacon_Book_Named_Syntax_Cardinal
  imports Bacon_Book_Classicism_Henkin_Reserve
    "HOL-Library.Nat_Bijection"
    "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>Finite codes for the book's minimal syntax and their cardinal bounds\<close>

text \<open>
  A book term is coded by a finite list over 'c + nat: constant names stay
  literal, everything else is coded numerically. For an infinite set U
  with at least as many elements as the declared names, the terms over
  the declared signature, each Henkin stage signature and the full Henkin
  signature all have cardinality at most |U|. No countability of the name
  carrier, consistency, richness or model is assumed. This is the
  syntactic ingredient for name reserves of arbitrary infinite cardinality.
\<close>

fun book_type_nat_code :: "otype \<Rightarrow> nat" where
  "book_type_nat_code Ind = 0"
| "book_type_nat_code Prop = 1"
| "book_type_nat_code (Arr \<sigma> \<tau>) = 2 + prod_encode (book_type_nat_code \<sigma>, book_type_nat_code \<tau>)"

lemma book_type_nat_code_eq [simp]:
  "book_type_nat_code \<sigma> = book_type_nat_code \<tau> \<longleftrightarrow> \<sigma> = \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case Ind
  show ?case by (cases \<tau>) auto
next
  case Prop
  show ?case by (cases \<tau>) auto
next
  case (Arr \<sigma> \<rho>)
  show ?case using Arr.IH by (cases \<tau>) auto
qed

fun book_logical_nat_code :: "book_minimal_logical \<Rightarrow> nat" where
  "book_logical_nat_code SImp = 0"
| "book_logical_nat_code (SBAll \<sigma>) = Suc (book_type_nat_code \<sigma>)"

lemma book_logical_nat_code_eq [simp]:
  "book_logical_nat_code l = book_logical_nat_code k \<longleftrightarrow> l = k"
  by (cases l; cases k) simp_all

fun book_finite_syntax_code :: "'c book_named_term \<Rightarrow> ('c + nat) list" where
  "book_finite_syntax_code (NVar n) = [Inr 0, Inr n]"
| "book_finite_syntax_code (NConst c \<sigma>) = [Inr 1, Inl c, Inr (book_type_nat_code \<sigma>)]"
| "book_finite_syntax_code (NLogical l) = [Inr 2, Inr (book_logical_nat_code l)]"
| "book_finite_syntax_code (NApp F A) =
    [Inr 3, Inr (length (book_finite_syntax_code F))] @
      book_finite_syntax_code F @ book_finite_syntax_code A"
| "book_finite_syntax_code (NLam n A) = [Inr 4, Inr n] @ book_finite_syntax_code A"

lemma book_finite_syntax_code_reflects:
  assumes equal: "book_finite_syntax_code A = book_finite_syntax_code B"
  shows "A = B"
  using equal
proof (induction A arbitrary: B)
  case (NVar n)
  then show ?case by (cases B) auto
next
  case (NConst c \<sigma>)
  then show ?case by (cases B) auto
next
  case (NLogical l)
  then show ?case by (cases B) auto
next
  case (NApp F A)
  note subterms = NApp.IH
  note code_equal = NApp.prems
  show ?case
  proof (cases B)
    case (NApp H C)
    have lengths: "length (book_finite_syntax_code F) = length (book_finite_syntax_code H)"
      and tails: "book_finite_syntax_code F @ book_finite_syntax_code A =
        book_finite_syntax_code H @ book_finite_syntax_code C"
      using code_equal unfolding NApp by simp_all
    have pieces: "book_finite_syntax_code F = book_finite_syntax_code H \<and>
        book_finite_syntax_code A = book_finite_syntax_code C"
      using tails lengths by simp
    have left: "book_finite_syntax_code F = book_finite_syntax_code H"
      and right: "book_finite_syntax_code A = book_finite_syntax_code C"
      using pieces by blast+
    show ?thesis using subterms(1)[OF left] subterms(2)[OF right] unfolding NApp by simp
  qed (use code_equal in auto)
next
  case (NLam n A)
  then show ?case by (cases B) auto
qed

lemma book_finite_syntax_code_injective:
  "inj book_finite_syntax_code"
  by (rule injI, rule book_finite_syntax_code_reflects)

lemma book_finite_syntax_code_labels:
  assumes names: "named_in_signature \<Sigma> A"
  shows "set (book_finite_syntax_code A) \<subseteq> (\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)"
  using names by (induction A) auto

lemma book_finite_syntax_code_lists:
  assumes names: "named_in_signature \<Sigma> A"
  shows "book_finite_syntax_code A \<in> lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))"
  using book_finite_syntax_code_labels[OF names] by (auto simp: in_lists_conv_set)

section \<open>Cardinal bounds\<close>

lemma book_admitted_syntax_lists_bound:
  "card_of {A :: 'c book_named_term. named_in_signature \<Sigma> A} \<le>o
    card_of (lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)))"
proof (rule card_of_ordLeqI[where f=book_finite_syntax_code])
  show "inj_on book_finite_syntax_code {A :: 'c book_named_term. named_in_signature \<Sigma> A}"
    using book_finite_syntax_code_injective by (rule inj_on_subset) simp
next
  fix A :: "'c book_named_term"
  assume "A \<in> {A. named_in_signature \<Sigma> A}"
  then show "book_finite_syntax_code A \<in> lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))"
    by (simp add: book_finite_syntax_code_lists)
qed

theorem book_admitted_syntax_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
  shows "card_of {A :: 'c book_named_term. named_in_signature \<Sigma> A} \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have alphabet: "card_of ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)) \<le>o card_of U"
    by (rule card_of_Plus_ordLeq_infinite[OF infinite names naturals])
  have lists_bound: "card_of (lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))) \<le>o card_of (lists U)"
    by (rule card_of_lists_mono[OF alphabet])
  have to_lists: "card_of {A :: 'c book_named_term. named_in_signature \<Sigma> A} \<le>o card_of (lists U)"
    by (rule ordLeq_transitive[OF book_admitted_syntax_lists_bound lists_bound])
  show ?thesis by (rule ordLeq_ordIso_trans[OF to_lists card_of_lists_infinite[OF infinite]])
qed

theorem book_all_terms_cardinal_bound:
  fixes U :: "'u set"
  assumes infinite: "infinite U"
    and names: "card_of (UNIV :: 'c set) \<le>o card_of U"
  shows "card_of (UNIV :: 'c book_named_term set) \<le>o card_of U"
proof -
  have every: "{A :: 'c book_named_term. named_in_signature (\<lambda>_. UNIV) A} = UNIV"
  proof
    show "UNIV \<subseteq> {A :: 'c book_named_term. named_in_signature (\<lambda>_. UNIV) A}"
    proof
      fix A :: "'c book_named_term"
      show "A \<in> {A. named_in_signature (\<lambda>_. UNIV) A}" by (induction A) simp_all
    qed
  qed simp
  have union: "(\<Union>\<sigma>. (\<lambda>_. UNIV :: 'c set) \<sigma>) = UNIV" by simp
  have bound: "card_of {A :: 'c book_named_term. named_in_signature (\<lambda>_. UNIV) A} \<le>o card_of U"
    by (rule book_admitted_syntax_cardinal_bound[OF infinite]; simp only: union; rule names)
  show ?thesis using bound by (simp only: every)
qed

lemma book_otypes_cardinal_bound:
  assumes infinite: "infinite U"
  shows "card_of (UNIV :: otype set) \<le>o card_of U"
proof -
  have types: "card_of (UNIV :: otype set) \<le>o card_of (UNIV :: nat set)"
  proof (rule card_of_ordLeqI[where f=book_type_nat_code])
    show "inj_on book_type_nat_code (UNIV :: otype set)" by (rule inj_onI) simp
  qed simp
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  show ?thesis by (rule ordLeq_transitive[OF types naturals])
qed

section \<open>Henkin stages over a signature of bounded cardinality\<close>

theorem book_henkin_stage_names_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<tau>. \<Sigma> \<tau>) \<le>o card_of U"
  shows "card_of (\<Union>\<tau>. book_henkin_signature \<Sigma> G k \<tau>) \<le>o card_of U"
proof (induction k)
  case 0
  have equality: "(\<Union>\<tau>. book_henkin_signature \<Sigma> G 0 \<tau>) = image BookOriginal (\<Union>\<tau>. \<Sigma> \<tau>)" by auto
  show ?case unfolding equality by (rule ordLeq_transitive[OF card_of_image names])
next
  case (Suc k)
  let ?Old = "\<Union>\<tau>. book_henkin_signature \<Sigma> G k \<tau>"
  let ?Terms = "{F :: ('c book_henkin_name) book_named_term. named_in_signature (book_henkin_signature \<Sigma> G k) F}"
  let ?New = "image (\<lambda>p. BookWitness k (fst p) (snd p)) ((UNIV :: otype set) \<times> ?Terms)"
  have terms: "card_of ?Terms \<le>o card_of U"
    by (rule book_admitted_syntax_cardinal_bound[OF infinite Suc.IH])
  have types: "card_of (UNIV :: otype set) \<le>o card_of U" by (rule book_otypes_cardinal_bound[OF infinite])
  have pairs: "card_of ((UNIV :: otype set) \<times> ?Terms) \<le>o card_of U"
    by (rule card_of_Times_ordLeq_infinite[OF infinite types terms])
  have new_names: "card_of ?New \<le>o card_of U" by (rule ordLeq_transitive[OF card_of_image pairs])
  have bound: "card_of (?Old \<union> ?New) \<le>o card_of U"
    by (rule card_of_Un_ordLeq_infinite[OF infinite Suc.IH new_names])
  have subset: "(\<Union>\<tau>. book_henkin_signature \<Sigma> G (Suc k) \<tau>) \<subseteq> ?Old \<union> ?New"
  proof
    fix c
    assume member: "c \<in> (\<Union>\<tau>. book_henkin_signature \<Sigma> G (Suc k) \<tau>)"
    obtain \<tau> where declared: "c \<in> book_henkin_signature \<Sigma> G (Suc k) \<tau>" using member by blast
    show "c \<in> ?Old \<union> ?New"
    proof (cases "c \<in> book_henkin_signature \<Sigma> G k \<tau>")
      case True
      then show ?thesis by blast
    next
      case False
      obtain F where shape: "c = BookWitness k \<tau> F"
        and predicate: "book_in_language book_minimal_logical_type UNIV (book_henkin_signature \<Sigma> G k) G F (Arr \<tau> Prop)"
        using declared False by auto
      have admitted: "F \<in> ?Terms"
        using book_language_named[OF predicate] unfolding named_in_language_def by blast
      have pair: "(\<tau>, F) \<in> (UNIV :: otype set) \<times> ?Terms" using admitted by simp
      have image_member: "(\<lambda>p. BookWitness k (fst p) (snd p)) (\<tau>, F) \<in> ?New" by (rule imageI[OF pair])
      show ?thesis using image_member by (simp only: fst_conv snd_conv shape; blast)
    qed
  qed
  show ?case by (rule ordLeq_transitive[OF card_of_mono1[OF subset] bound])
qed

theorem book_henkin_full_names_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<tau>. \<Sigma> \<tau>) \<le>o card_of U"
  shows "card_of (\<Union>\<tau>. book_henkin_full_signature \<Sigma> G \<tau>) \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have stages: "\<forall>k\<in>(UNIV :: nat set). card_of (\<Union>\<tau>. book_henkin_signature \<Sigma> G k \<tau>) \<le>o card_of U"
    by (intro ballI; rule book_henkin_stage_names_cardinal_bound[OF infinite names])
  have levels: "card_of (\<Union>k. \<Union>\<tau>. book_henkin_signature \<Sigma> G k \<tau>) \<le>o card_of U"
    by (rule card_of_UNION_ordLeq_infinite[OF infinite naturals stages])
  have equality: "(\<Union>\<tau>. book_henkin_full_signature \<Sigma> G \<tau>) = (\<Union>k. \<Union>\<tau>. book_henkin_signature \<Sigma> G k \<tau>)"
    by (auto simp: book_henkin_full_signature_def)
  show ?thesis by (simp only: equality; rule levels)
qed

corollary book_henkin_full_signature_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<tau>. \<Sigma> \<tau>) \<le>o card_of U"
  shows "card_of (book_henkin_full_signature \<Sigma> G \<tau>) \<le>o card_of U"
  by (rule ordLeq_transitive[OF card_of_mono1[OF SUP_upper[OF UNIV_I]] book_henkin_full_names_cardinal_bound[OF infinite names]])

text \<open>
  Source role: the cardinality bookkeeping behind extending the countable
  construction of p.398 to a signature of arbitrary infinite cardinality.
  Nothing here is a model or consistency statement; the bounds are on
  raw syntax and on the explicitly defined Henkin name stages.
\<close>

end
