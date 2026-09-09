theory Bacon_Source_Relational_Identity_Axiom_Truth
  imports Bacon_Source_Relational_Logical_Truth
begin

section \<open>Literal identity and the Ref and LL axioms\<close>

text \<open>
  A=A and A=B→(FA→FB) are true for A,B:σ and F:σ→t.
  Source: Figure 2, p.8, and Definition 3.1(ii.b,iii.f), pp.43–44.
  Identity is actual equality of denotations, not Leibniz equivalence.
  Implications retain their literal Figure 1 λ operators.

  Representation: the operand languages and each adequacy condition are
  explicit. Application congruence is a field of the independent R model;
  no F model, proof judgment, closedness, or total completion is used.
  Status: axiom truth only, ready for a separate proof induction.
\<close>

lemma paper_R_named_eq_language:
  assumes al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF al])
  have er: "paper_R_type (paper_logical_type (SEq \<sigma>))" using rt by simp
  have et: "paper_R_has_type G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_R_has_type.Logical[where G=G, OF er] by simp
  have el: "paper_R_in_language \<Sigma> G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using et by (simp add: paper_R_in_language_def)
  show ?thesis unfolding named_paper_eq_def
    by (rule paper_R_language_App[OF paper_R_language_App[OF el al] bl])
qed

context paper_R_bbk_model
begin

lemma paper_R_named_eq_truth:
  assumes al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (denote g (named_paper_eq \<sigma> A B)) = (denote g A = denote g B)"
  unfolding named_paper_eq_def by (rule valuation_identity[OF al bl typed aa ba])

theorem paper_R_Ref_truth:
  assumes al: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A"
  shows "valuation (denote g (named_paper_eq \<sigma> A A))"
  by (simp only: paper_R_named_eq_truth[OF al al typed aa aa])

theorem paper_R_LL_truth:
  assumes al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    and fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g"
    and aa: "named_adequate g A" and ba: "named_adequate g B" and fa: "named_adequate g F"
  shows "valuation (denote g (named_paper_imp stock (named_paper_eq \<sigma> A B)
    (named_paper_imp stock (NApp F A) (NApp F B))))"
proof -
  have el: "paper_R_in_language signature stock (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_eq_language[OF al bl])
  have fal: "paper_R_in_language signature stock (NApp F A) Prop" by (rule paper_R_language_App[OF fl al])
  have fbl: "paper_R_in_language signature stock (NApp F B) Prop" by (rule paper_R_language_App[OF fl bl])
  have il: "paper_R_in_language signature stock (named_paper_imp stock (NApp F A) (NApp F B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF stock_rich fal fbl])
  have ea: "named_adequate g (named_paper_eq \<sigma> A B)"
    using aa ba by (auto simp: named_adequate_def named_paper_primitive_fv)
  have faa: "named_adequate g (NApp F A)" and fba: "named_adequate g (NApp F B)"
    using fa aa ba by (auto simp: named_adequate_def)
  have ia: "named_adequate g (named_paper_imp stock (NApp F A) (NApp F B))"
    using faa fba by (auto simp: named_adequate_def named_paper_defined_fv)
  have equality: "valuation (denote g (named_paper_eq \<sigma> A B)) = (denote g A = denote g B)"
    by (rule paper_R_named_eq_truth[OF al bl typed aa ba])
  have inner: "valuation (denote g (named_paper_imp stock (NApp F A) (NApp F B))) =
      (valuation (denote g (NApp F A)) \<longrightarrow> valuation (denote g (NApp F B)))"
    by (rule paper_R_named_paper_imp_truth[OF fal fbl typed faa fba])
  have outer: "valuation (denote g (named_paper_imp stock (named_paper_eq \<sigma> A B)
      (named_paper_imp stock (NApp F A) (NApp F B)))) =
      (valuation (denote g (named_paper_eq \<sigma> A B)) \<longrightarrow>
        valuation (denote g (named_paper_imp stock (NApp F A) (NApp F B))))"
    by (rule paper_R_named_paper_imp_truth[OF el il typed ea ia])
  have entails: "denote g A = denote g B \<longrightarrow>
      (valuation (denote g (NApp F A)) \<longrightarrow> valuation (denote g (NApp F B)))"
  proof (rule impI)
    assume equal: "denote g A = denote g B"
    have applications: "denote g (NApp F A) = denote g (NApp F B)"
      by (rule denote_application_cong[OF fl al fl bl typed typed faa fba refl equal])
    show "valuation (denote g (NApp F A)) \<longrightarrow> valuation (denote g (NApp F B))"
      by (simp add: applications)
  qed
  show ?thesis by (simp only: outer inner equality; rule entails)
qed

end

end
