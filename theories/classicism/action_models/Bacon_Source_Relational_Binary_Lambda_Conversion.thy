theory Bacon_Source_Relational_Binary_Lambda_Conversion
  imports Bacon_Source_Relational_Logical_Language
begin

section \<open>Two literal same-variable β steps inside R\<close>

text \<open>
  ((λp.λq.C)p)q ≡β C for p,q:t and C:t.
  Source: Figure 2, p.8. These substitutions replace each variable
  by itself and are explicitly free-for, including shadowed binders.
  No arbitrary argument is substituted under a fixed operator binder,
  and no α rule or F conversion premise is used.
\<close>

lemma paper_R_same_variable_beta:
  "named_beta_contract (NApp (NLam p C) (NVar p)) C"
  using named_beta_contract.beta[where x=p and B="NVar p" and A=C,
    OF named_free_for_same_variable]
  by (simp only: named_subst_same_variable)

lemma paper_R_double_prop_lambda_conversion:
  assumes pt: "G p = Prop" and qt: "G q = Prop" and body: "paper_R_has_type G C Prop"
  shows "paper_R_raw_beta_eta G Prop (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) C"
proof -
  have pr: "paper_R_type (G p)" by (simp only: pt; simp)
  have qr: "paper_R_type (G q)" by (simp only: qt; simp)
  have pv: "paper_R_has_type G (NVar p) Prop"
    using paper_R_has_type.Var[where G=G and n=p, OF pr] by (simp only: pt)
  have qv: "paper_R_has_type G (NVar q) Prop"
    using paper_R_has_type.Var[where G=G and n=q, OF qr] by (simp only: qt)
  have raw_inner: "paper_R_has_type G (NLam q C) (Arr (G q) Prop)"
    by (rule paper_R_has_type.Lam[OF body qr]; simp)
  have inner: "paper_R_has_type G (NLam q C) (Arr Prop Prop)" using raw_inner by (simp only: qt)
  have whole: "paper_R_has_type G (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) Prop"
    by (rule paper_R_has_type.App[
      OF paper_R_has_type.App[OF paper_R_double_prop_lambda_type[OF pt qt body] pv] qv])
  have middle: "paper_R_has_type G (NApp (NLam q C) (NVar q)) Prop"
    by (rule paper_R_has_type.App[OF inner qv])
  have first_step: "named_compatible_step named_beta_contract
    (NApp (NApp (NLam p (NLam q C)) (NVar p)) (NVar q)) (NApp (NLam q C) (NVar q))"
    by (rule named_compatible_step.App_left, rule named_compatible_step.root,
      rule paper_R_same_variable_beta)
  have second_step: "named_compatible_step named_beta_contract (NApp (NLam q C) (NVar q)) C"
    by (rule named_compatible_step.root, rule paper_R_same_variable_beta)
  show ?thesis by (rule paper_R_raw_beta_eta.Trans[
    OF paper_R_raw_beta_eta.Beta[OF whole middle first_step]
      paper_R_raw_beta_eta.Beta[OF middle body second_step]])
qed

end
