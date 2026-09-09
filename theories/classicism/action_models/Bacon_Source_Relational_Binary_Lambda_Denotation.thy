theory Bacon_Source_Relational_Binary_Lambda_Denotation
  imports Bacon_Source_Relational_Binary_Lambda_Conversion
begin

section \<open>Evaluate closed binary operators using adequate partial assignments\<close>

text \<open>
  A closed binary operator has the same denotation at two typed
  assignments. Clause (ii.b) then replaces its two arguments by
  variables with the same denotations. Source: Definition 3.1,
  pp.43–44. Applying λp.λq.C to those very variables β-reduces
  to C without capturing free variables of arbitrary input formulas.
  Only the independent R model and endpoint adequacy are used.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_closed_binary_denote_transport:
  assumes operator: "paper_R_in_language signature stock L (Arr Prop (Arr Prop Prop))"
    and closed: "named_fv L = {}"
    and first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and gt: "named_env_typed domain stock g" and kt: "named_env_typed domain stock k"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
    and pt: "stock p = Prop" and qt: "stock q = Prop"
    and kp: "k p = Some (denote g A)" and kq: "k q = Some (denote g B)"
  shows "denote g (NApp (NApp L A) B) = denote k (NApp (NApp L (NVar p)) (NVar q))"
proof -
  have rt: "paper_R_type Prop" by simp
  have pl: "paper_R_in_language signature stock (NVar p) Prop"
    by (rule paper_R_language_Var[where G=stock and n=p, OF pt rt])
  have ql: "paper_R_in_language signature stock (NVar q) Prop"
    by (rule paper_R_language_Var[where G=stock and n=q, OF qt rt])
  have lg: "named_adequate g L" and lk: "named_adequate k L"
    by (simp_all only: named_adequate_def closed empty_subsetI)
  have la_g: "named_adequate g (NApp L A)" using aa by (auto simp: named_adequate_def closed)
  have lab_g: "named_adequate g (NApp (NApp L A) B)"
    using aa ba by (auto simp: named_adequate_def closed)
  have lp_k: "named_adequate k (NApp L (NVar p))"
    using kp by (auto simp: named_adequate_def closed dom_def)
  have lpq_k: "named_adequate k (NApp (NApp L (NVar p)) (NVar q))"
    using kp kq by (auto simp: named_adequate_def closed dom_def)
  have same_operator: "denote g L = denote k L"
    by (rule denote_locality[OF operator gt kt lg lk]; simp only: closed; simp)
  have pv: "denote g A = denote k (NVar p)" by (rule sym[OF denote_var[OF kt kp]])
  have qv: "denote g B = denote k (NVar q)" by (rule sym[OF denote_var[OF kt kq]])
  have partial: "denote g (NApp L A) = denote k (NApp L (NVar p))"
    by (rule denote_application_cong[OF operator first operator pl gt kt la_g lp_k same_operator pv])
  have left_head: "paper_R_in_language signature stock (NApp L A) (Arr Prop Prop)"
    by (rule paper_R_language_App[OF operator first])
  have right_head: "paper_R_in_language signature stock (NApp L (NVar p)) (Arr Prop Prop)"
    by (rule paper_R_language_App[OF operator pl])
  show ?thesis
    by (rule denote_application_cong[OF left_head second right_head ql gt kt lab_g lpq_k partial qv])
qed

lemma paper_R_binary_lambda_evaluate:
  assumes pt: "stock p = Prop" and qt: "stock q = Prop" and distinct: "p \<noteq> q"
    and body: "paper_R_in_language signature stock C Prop" and support: "named_fv C \<subseteq> {p,q}"
    and first: "paper_R_in_language signature stock A Prop" and second: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  obtains k where "named_env_typed domain stock k"
    "k p = Some (denote g A)" "k q = Some (denote g B)"
    "denote g (NApp (NApp (NLam p (NLam q C)) A) B) = denote k C"
proof -
  let ?k = "(g(p := Some (denote g A)))(q := Some (denote g B))"
  have am: "denote g A \<in> domain (stock p)" using denote_type[OF first typed aa] by (simp only: pt)
  have bm: "denote g B \<in> domain (stock q)" using denote_type[OF second typed ba] by (simp only: qt)
  have k1t: "named_env_typed domain stock (g(p := Some (denote g A)))"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF typed am])
  have kt: "named_env_typed domain stock ?k"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF k1t bm])
  have kp: "?k p = Some (denote g A)" by (simp add: distinct)
  have kq: "?k q = Some (denote g B)" by simp
  have bt: "paper_R_has_type stock C Prop" and names: "named_in_signature signature C"
    using body unfolding paper_R_in_language_def by blast+
  have operator: "paper_R_in_language signature stock (NLam p (NLam q C)) (Arr Prop (Arr Prop Prop))"
    unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_double_prop_lambda_type[OF pt qt bt]]; simp only: named_in_signature.simps; rule names)
  have closed: "named_fv (NLam p (NLam q C)) = {}" using support by auto
  have transported: "denote g (NApp (NApp (NLam p (NLam q C)) A) B) =
    denote ?k (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q))"
    by (rule paper_R_closed_binary_denote_transport[
      OF operator closed first second typed kt aa ba pt qt kp kq])
  have rt: "paper_R_type Prop" by simp
  have pl: "paper_R_in_language signature stock (NVar p) Prop"
    by (rule paper_R_language_Var[where G=stock and n=p, OF pt rt])
  have ql: "paper_R_in_language signature stock (NVar q) Prop"
    by (rule paper_R_language_Var[where G=stock and n=q, OF qt rt])
  have left: "paper_R_in_language signature stock
    (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) Prop"
    by (rule paper_R_language_App[OF paper_R_language_App[OF operator pl] ql])
  have left_adequate: "named_adequate ?k (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q))"
    using support kp kq by (auto simp: named_adequate_def closed dom_def)
  have body_adequate: "named_adequate ?k C"
    using support kp kq by (auto simp: named_adequate_def dom_def)
  have conversion: "paper_R_raw_beta_eta stock Prop
    (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) C"
    by (rule paper_R_double_prop_lambda_conversion[OF pt qt bt])
  have reduced: "denote ?k (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) = denote ?k C"
    by (rule denote_beta_eta[OF conversion left body kt left_adequate body_adequate])
  have result: "denote g (NApp (NApp (NLam p (NLam q C)) A) B) = denote ?k C"
    by (rule trans[OF transported reduced])
  show thesis by (rule that[OF kt kp kq result])
qed

end

end
