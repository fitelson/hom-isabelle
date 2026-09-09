theory Bacon_Source_Relational_Logical_Truth
  imports Bacon_Source_Relational_Binary_Lambda_Denotation
begin

section \<open>Truth of the literal Figure 1 abbreviations in R models\<close>

text \<open>
  v(⟦A→B⟧ᵍ) iff (v(⟦A⟧ᵍ) implies v(⟦B⟧ᵍ)), and
  v(⟦A↔B⟧ᵍ) iff v(⟦A⟧ᵍ)=v(⟦B⟧ᵍ).
  Source: Figure 1, pp.5–6, and Definition 3.1, pp.43–44.
  The operators remain literal closed λ terms. Their truth is derived
  through typed partial assignments and R β conversion, not stipulated.
  Arguments may be open and may mention either chosen binder name.
  No F model, F-rich stock or Propositional Equivalence rule is assumed.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_named_not_truth:
  assumes language: "paper_R_in_language signature stock A Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "valuation (denote g (named_paper_not A)) = (\<not> valuation (denote g A))"
  unfolding named_paper_not_def by (rule valuation_neg[OF language typed adequate])

lemma paper_R_named_or_truth:
  assumes first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_or A B)) = (valuation (denote g A) \<or> valuation (denote g B))"
  unfolding named_paper_or_def by (rule valuation_disj[OF first second typed aa ba])

lemma paper_R_named_and_truth:
  assumes first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_and A B)) = (valuation (denote g A) \<and> valuation (denote g B))"
  unfolding named_paper_and_def by (rule valuation_conj[OF first second typed aa ba])

lemma paper_R_named_or_not_truth:
  assumes first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_or (named_paper_not A) B)) =
    (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
proof -
  have nl: "paper_R_in_language signature stock (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF first])
  have na: "named_adequate g (named_paper_not A)"
    using aa by (simp only: named_adequate_def named_paper_primitive_fv)
  have or_value: "valuation (denote g (named_paper_or (named_paper_not A) B)) =
    (valuation (denote g (named_paper_not A)) \<or> valuation (denote g B))"
    by (rule paper_R_named_or_truth[OF nl second typed na ba])
  show ?thesis by (simp only: or_value paper_R_named_not_truth[OF first typed aa]; blast)
qed

theorem paper_R_named_paper_imp_truth:
  assumes first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_imp stock A B)) =
    (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
proof -
  let ?p = "named_paper_p stock"
  let ?q = "named_paper_q stock"
  let ?C = "named_paper_or (named_paper_not (NVar ?p)) (NVar ?q) :: 'c paper_named_term"
  have pt: "stock ?p = Prop" by (rule paper_R_named_paper_p_type[OF stock_rich])
  have qt: "stock ?q = Prop" by (rule paper_R_named_paper_q_type[OF stock_rich])
  have distinct: "?p \<noteq> ?q" by (rule paper_R_named_paper_names_distinct[OF stock_rich])
  have rt: "paper_R_type Prop" by simp
  have pl: "paper_R_in_language signature stock (NVar ?p) Prop"
    by (rule paper_R_language_Var[where G=stock and n="?p", OF pt rt])
  have ql: "paper_R_in_language signature stock (NVar ?q) Prop"
    by (rule paper_R_language_Var[where G=stock and n="?q", OF qt rt])
  have body: "paper_R_in_language signature stock ?C Prop"
    by (rule paper_R_named_or_language[OF paper_R_named_not_language[OF pl] ql])
  have support: "named_fv ?C \<subseteq> {?p,?q}" by (simp add: named_paper_primitive_fv)
  obtain k where kt: "named_env_typed domain stock k" and kp: "k ?p = Some (denote g A)"
    and kq: "k ?q = Some (denote g B)"
    and evaluated: "denote g (NApp (NApp (NLam ?p (NLam ?q ?C)) A) B) = denote k ?C"
    by (rule paper_R_binary_lambda_evaluate[OF pt qt distinct body support first second typed aa ba])
  have equation: "denote g (named_paper_imp stock A B) = denote k ?C"
    using evaluated by (simp only: named_paper_imp_def named_paper_imp_const_def)
  have pa: "named_adequate k (NVar ?p)" using kp by (auto simp: named_adequate_def dom_def)
  have qa: "named_adequate k (NVar ?q)" using kq by (auto simp: named_adequate_def dom_def)
  have core: "valuation (denote k ?C) =
    (valuation (denote k (NVar ?p)) \<longrightarrow> valuation (denote k (NVar ?q)))"
    by (rule paper_R_named_or_not_truth[OF pl ql kt pa qa])
  show ?thesis by (simp only: equation core denote_var[OF kt kp] denote_var[OF kt kq])
qed

theorem paper_R_named_paper_iff_truth:
  assumes first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_iff stock A B)) =
    (valuation (denote g A) = valuation (denote g B))"
proof -
  let ?p = "named_paper_p stock"
  let ?q = "named_paper_q stock"
  let ?L = "named_paper_or (named_paper_not (NVar ?p)) (NVar ?q) :: 'c paper_named_term"
  let ?R = "named_paper_or (named_paper_not (NVar ?q)) (NVar ?p) :: 'c paper_named_term"
  let ?C = "named_paper_and ?L ?R"
  have pt: "stock ?p = Prop" by (rule paper_R_named_paper_p_type[OF stock_rich])
  have qt: "stock ?q = Prop" by (rule paper_R_named_paper_q_type[OF stock_rich])
  have distinct: "?p \<noteq> ?q" by (rule paper_R_named_paper_names_distinct[OF stock_rich])
  have rt: "paper_R_type Prop" by simp
  have pl: "paper_R_in_language signature stock (NVar ?p) Prop"
    by (rule paper_R_language_Var[where G=stock and n="?p", OF pt rt])
  have ql: "paper_R_in_language signature stock (NVar ?q) Prop"
    by (rule paper_R_language_Var[where G=stock and n="?q", OF qt rt])
  have ll: "paper_R_in_language signature stock ?L Prop"
    by (rule paper_R_named_or_language[OF paper_R_named_not_language[OF pl] ql])
  have rl: "paper_R_in_language signature stock ?R Prop"
    by (rule paper_R_named_or_language[OF paper_R_named_not_language[OF ql] pl])
  have body: "paper_R_in_language signature stock ?C Prop" by (rule paper_R_named_and_language[OF ll rl])
  have support: "named_fv ?C \<subseteq> {?p,?q}" by (auto simp: named_paper_primitive_fv)
  obtain k where kt: "named_env_typed domain stock k" and kp: "k ?p = Some (denote g A)"
    and kq: "k ?q = Some (denote g B)"
    and evaluated: "denote g (NApp (NApp (NLam ?p (NLam ?q ?C)) A) B) = denote k ?C"
    by (rule paper_R_binary_lambda_evaluate[OF pt qt distinct body support first second typed aa ba])
  have equation: "denote g (named_paper_iff stock A B) = denote k ?C"
    using evaluated by (simp only: named_paper_iff_def named_paper_iff_const_def)
  have pa: "named_adequate k (NVar ?p)" using kp by (auto simp: named_adequate_def dom_def)
  have qa: "named_adequate k (NVar ?q)" using kq by (auto simp: named_adequate_def dom_def)
  have la: "named_adequate k ?L" and ra: "named_adequate k ?R"
    using pa qa by (auto simp: named_adequate_def named_paper_primitive_fv)
  have left_value: "valuation (denote k ?L) =
    (valuation (denote k (NVar ?p)) \<longrightarrow> valuation (denote k (NVar ?q)))"
    by (rule paper_R_named_or_not_truth[OF pl ql kt pa qa])
  have right_value: "valuation (denote k ?R) =
    (valuation (denote k (NVar ?q)) \<longrightarrow> valuation (denote k (NVar ?p)))"
    by (rule paper_R_named_or_not_truth[OF ql pl kt qa pa])
  have conjunction: "valuation (denote k ?C) = (valuation (denote k ?L) \<and> valuation (denote k ?R))"
    by (rule paper_R_named_and_truth[OF ll rl kt la ra])
  show ?thesis
    by (simp only: equation conjunction left_value right_value denote_var[OF kt kp] denote_var[OF kt kq]; blast)
qed

end

end
