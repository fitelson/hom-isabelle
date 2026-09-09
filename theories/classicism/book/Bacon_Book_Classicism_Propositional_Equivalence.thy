theory Bacon_Book_Classicism_Propositional_Equivalence
  imports Bacon_Book_Classicism_Least_Theory
begin

section \<open>The propositional case of the book's Rule of Equivalence\<close>

theorem book_C_propositional_equivalence:
  assumes left: "book_theory_formula \<Sigma> G P" and right: "book_theory_formula \<Sigma> G Q"
    and premise: "book_C_proves \<Sigma> G (book_iff G P Q)"
  shows "book_C_proves \<Sigma> G (book_leibniz G Prop P Q)"
proof -
  have instance_ok: "book_equivalence_rule_instance \<Sigma> G [] P Q"
    using left right by (simp add: book_equivalence_rule_instance_def)
  have applied: "book_C_proves \<Sigma> G (book_iff G (book_vector_application P []) (book_vector_application Q []))"
    using premise by (simp only: book_vector_application_def list.map foldl.simps)
  have identity: "book_C_proves \<Sigma> G (book_leibniz G (foldr Arr (map G []) Prop) P Q)"
    by (rule book_C_proves.Equivalence[OF applied instance_ok])
  show ?thesis using identity by simp
qed

definition book_box_const :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "book_box_const G = NLam (book_prop_name G)
    (book_leibniz G Prop (NVar (book_prop_name G)) (book_top G))"

definition book_box :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_box G P = NApp (book_box_const G) P"

lemma book_box_const_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_box_const G) (Arr Prop Prop)"
proof -
  have variable: "book_theory_formula \<Sigma> G (NVar (book_prop_name G))"
    by (simp only: book_language_var_iff book_prop_name_type[OF rich])
  have body: "book_theory_formula \<Sigma> G
    (book_leibniz G Prop (NVar (book_prop_name G)) (book_top G))"
    by (rule book_leibniz_language[OF rich variable book_top_language[OF rich]])
  show ?thesis unfolding book_box_const_def
    using book_language_Lam[where n="book_prop_name G", OF body]
    by (simp only: book_prop_name_type[OF rich])
qed

lemma book_box_language:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G P \<Longrightarrow> book_theory_formula \<Sigma> G (book_box G P)"
  unfolding book_box_def by (rule book_language_App; (rule book_box_const_language | assumption); assumption?)

lemma book_box_fv:
  "named_fv (book_box G P) = named_fv P"
  by (simp add: book_box_def book_box_const_def book_leibniz_fv book_top_closed)

text \<open>
  □ is the literal λp.(p=ₜ⊤), with Table 4.1's defined Leibniz
  identity and defined truth. This does not replace the λ application
  by its β reduct in the syntax, or import the paper's □.
  Its modal proof rules remain to be derived in this calculus.
\<close>

end
