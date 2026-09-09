theory Bacon_Book_Primitive_Conjunction_Formula_Syntax
  imports Bacon_Book_Primitive_Conjunction_Decoding
begin

section \<open>Minimal formula notation in the richer vocabulary\<close>

text \<open>
  A→B, ∀n.A, ⊥ and ¬A retain the minimal basis's literal syntax,
  with each minimal symbol injected by BCMinimal. The binder name in
  ⊥ and ¬ is the SAME book_prop_name(G) used in the minimal language.
  Source: Bacon, Table 4.1, p.93, and §5.2, p.104.

  Primitive A∧B remains book_conj_apply A B, headed by BCAnd. None
  of the following definitions replaces that symbol by a λ-expression.
  Encoding and decoding equations are syntactic correspondences only;
  they do not assume conjunction axioms or a logical-model clause.
\<close>

definition book_conj_imp :: "'c book_conj_term \<Rightarrow> 'c book_conj_term \<Rightarrow> 'c book_conj_term" where
  "book_conj_imp A B = NApp (NApp (NLogical (BCMinimal SImp)) A) B"

definition book_conj_all :: "sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_conj_term \<Rightarrow> 'c book_conj_term" where
  "book_conj_all G n A = NApp (NLogical (BCMinimal (SBAll (G n)))) (NLam n A)"

definition book_conj_bottom :: "sgcontext \<Rightarrow> 'c book_conj_term" where
  "book_conj_bottom G = NApp (NLogical (BCMinimal (SBAll Prop)))
    (NLam (book_prop_name G) (NVar (book_prop_name G)))"

definition book_conj_not_const :: "sgcontext \<Rightarrow> 'c book_conj_term" where
  "book_conj_not_const G = NLam (book_prop_name G)
    (book_conj_imp (NVar (book_prop_name G)) (book_conj_bottom G))"

definition book_conj_not :: "sgcontext \<Rightarrow> 'c book_conj_term \<Rightarrow> 'c book_conj_term" where
  "book_conj_not G A = NApp (book_conj_not_const G) A"

lemma book_conj_imp_operator_language:
  "book_in_language book_conj_logical_type UNIV \<Sigma> G (NLogical (BCMinimal SImp)) book_conj_type"
  by (simp add: book_language_logical_iff)

lemma book_conj_all_operator_language:
  "book_in_language book_conj_logical_type UNIV \<Sigma> G
    (NLogical (BCMinimal (SBAll \<sigma>))) (Arr (Arr \<sigma> Prop) Prop)"
  by (simp add: book_language_logical_iff)

lemma book_conj_imp_language:
  assumes first: "book_conj_formula \<Sigma> G A" and second: "book_conj_formula \<Sigma> G B"
  shows "book_conj_formula \<Sigma> G (book_conj_imp A B)"
  unfolding book_conj_imp_def
  by (rule book_language_App[OF book_language_App[OF book_conj_imp_operator_language first] second])

lemma book_conj_all_language:
  assumes body: "book_conj_formula \<Sigma> G A"
  shows "book_conj_formula \<Sigma> G (book_conj_all G n A)"
  unfolding book_conj_all_def
  by (rule book_language_App[OF book_conj_all_operator_language book_language_Lam[OF body]])

lemma book_conj_bottom_as_all:
  assumes rich: "sg_rich G"
  shows "book_conj_bottom G = book_conj_all G (book_prop_name G) (NVar (book_prop_name G))"
  by (simp only: book_conj_bottom_def book_conj_all_def book_prop_name_type[OF rich])

lemma book_conj_bottom_language:
  assumes rich: "sg_rich G"
  shows "book_conj_formula \<Sigma> G (book_conj_bottom G)"
proof -
  have variable: "book_conj_formula \<Sigma> G (NVar (book_prop_name G))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  show ?thesis by (simp only: book_conj_bottom_as_all[OF rich]; rule book_conj_all_language[OF variable])
qed

lemma book_conj_not_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_conj_logical_type UNIV \<Sigma> G (book_conj_not_const G) (Arr Prop Prop)"
proof -
  have variable: "book_conj_formula \<Sigma> G (NVar (book_prop_name G))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have body: "book_conj_formula \<Sigma> G (book_conj_imp (NVar (book_prop_name G)) (book_conj_bottom G))"
    by (rule book_conj_imp_language[OF variable book_conj_bottom_language[OF rich]])
  have abstraction: "book_in_language book_conj_logical_type UNIV \<Sigma> G
    (NLam (book_prop_name G) (book_conj_imp (NVar (book_prop_name G)) (book_conj_bottom G)))
    (Arr (G (book_prop_name G)) Prop)"
    by (rule book_language_Lam[OF body])
  show ?thesis using abstraction by (simp only: book_conj_not_const_def book_prop_name_type[OF rich])
qed

lemma book_conj_not_language:
  assumes rich: "sg_rich G" and body: "book_conj_formula \<Sigma> G A"
  shows "book_conj_formula \<Sigma> G (book_conj_not G A)"
  unfolding book_conj_not_def
  by (rule book_language_App[OF book_conj_not_const_language[OF rich] body])

lemma book_conj_imp_fv: "named_fv (book_conj_imp A B) = named_fv A \<union> named_fv B"
  by (simp add: book_conj_imp_def)
lemma book_conj_all_fv: "named_fv (book_conj_all G n A) = named_fv A - {n}"
  by (simp add: book_conj_all_def)
lemma book_conj_bottom_closed: "named_fv (book_conj_bottom G) = {}"
  by (simp add: book_conj_bottom_def)
lemma book_conj_not_const_closed: "named_fv (book_conj_not_const G) = {}"
  by (simp add: book_conj_not_const_def book_conj_imp_fv book_conj_bottom_closed)
lemma book_conj_not_fv: "named_fv (book_conj_not G A) = named_fv A"
  by (simp add: book_conj_not_def book_conj_not_const_closed)

section \<open>Literal encoding and decoding equations\<close>

lemma book_conj_encode_imp:
  "book_conj_encode (book_conj_imp A B) = book_imp (book_conj_encode A) (book_conj_encode B)"
  by (simp add: book_conj_imp_def book_imp_def)
lemma book_conj_encode_all:
  "book_conj_encode (book_conj_all G n A) = book_all G n (book_conj_encode A)"
  by (simp add: book_conj_all_def book_all_def)
lemma book_conj_encode_bottom:
  "book_conj_encode (book_conj_bottom G) = book_bottom G"
  by (simp add: book_conj_bottom_def book_bottom_def)
lemma book_conj_encode_not_const:
  "book_conj_encode (book_conj_not_const G) = book_not_const G"
  by (simp add: book_conj_not_const_def book_not_const_def book_conj_encode_imp book_conj_encode_bottom)
lemma book_conj_encode_not:
  "book_conj_encode (book_conj_not G A) = book_not G (book_conj_encode A)"
  by (simp add: book_conj_not_def book_not_def book_conj_encode_not_const)

lemma book_conj_decode_imp:
  "book_conj_decode (book_imp A B) = book_conj_imp (book_conj_decode A) (book_conj_decode B)"
  by (simp add: book_imp_def book_conj_imp_def)
lemma book_conj_decode_all:
  "book_conj_decode (book_all G n A) = book_conj_all G n (book_conj_decode A)"
  by (simp add: book_all_def book_conj_all_def)
lemma book_conj_decode_bottom:
  "book_conj_decode (book_bottom G) = book_conj_bottom G"
  by (simp add: book_bottom_def book_conj_bottom_def)
lemma book_conj_decode_not_const:
  "book_conj_decode (book_not_const G) = book_conj_not_const G"
  by (simp add: book_not_const_def book_conj_not_const_def book_conj_decode_imp book_conj_decode_bottom)
lemma book_conj_decode_not:
  "book_conj_decode (book_not G A) = book_conj_not G (book_conj_decode A)"
  by (simp add: book_not_def book_conj_not_def book_conj_decode_not_const)
lemma book_conj_decode_tag_application:
  "book_conj_decode (NApp (NApp (NConst (Inr ()) book_conj_type) A) B) =
    book_conj_apply (book_conj_decode A) (book_conj_decode B)"
  by (simp add: book_conj_apply_def)

end
