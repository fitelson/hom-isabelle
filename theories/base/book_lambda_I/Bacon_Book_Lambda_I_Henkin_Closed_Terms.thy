theory Bacon_Book_Lambda_I_Henkin_Closed_Terms
  imports Bacon_Book_Lambda_I_Henkin_Full_Signature Bacon_Book_Lambda_I_Calculus
begin

section \<open>The expanded λI language has a closed λI term of every type\<close>

text \<open>
  The unrestricted development allocates the witness name of λxσ.⊥ for
  inhabitation. That predicate is not a λI term, and the λI signature
  stages declare witness names only for closed λI predicates. Instead,
  for each σ the closed λI predicate λxσ.∀X(σ→t).(X x → X x) belongs to
  the initial expanded language: both binders occur in their bodies.
  Stage one declares its witness name, and that declared constant is a
  closed λI term of type σ in the full signature.

  The payload of the name is syntax inside an atomic constant; object
  language occurrences never traverse it. As in the unrestricted
  development the name is allocated without any truth claim about the
  predicate. No consistency premise is required.
\<close>

definition book_lambda_I_inhabitation_predicate :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_named_term" where
  "book_lambda_I_inhabitation_predicate G \<sigma> =
    NLam (named_chart_fresh G [] \<sigma>)
      (book_all G (named_chart_fresh G [named_chart_fresh G [] \<sigma>] (Arr \<sigma> Prop))
        (book_imp
          (NApp (NVar (named_chart_fresh G [named_chart_fresh G [] \<sigma>] (Arr \<sigma> Prop)))
            (NVar (named_chart_fresh G [] \<sigma>)))
          (NApp (NVar (named_chart_fresh G [named_chart_fresh G [] \<sigma>] (Arr \<sigma> Prop)))
            (NVar (named_chart_fresh G [] \<sigma>)))))"

lemma book_lambda_I_inhabitation_predicate_facts:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G
      (book_lambda_I_inhabitation_predicate G \<sigma>) (Arr \<sigma> Prop) \<and>
    named_fv (book_lambda_I_inhabitation_predicate G \<sigma> :: 'c book_named_term) = {} \<and>
    book_lambda_I (book_lambda_I_inhabitation_predicate G \<sigma> :: 'c book_named_term)"
proof -
  let ?x = "named_chart_fresh G [] \<sigma>"
  let ?X = "named_chart_fresh G [?x] (Arr \<sigma> Prop)"
  let ?Xx = "NApp (NVar ?X) (NVar ?x)"
  let ?body = "book_all G ?X (book_imp ?Xx ?Xx)"
  have xtype: "G ?x = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have Xtype: "G ?X = Arr \<sigma> Prop" by (rule named_chart_fresh_type[OF rich])
  have distinct: "?X \<noteq> ?x" using named_chart_fresh_notin[OF rich, where ns="[?x]" and \<sigma>="Arr \<sigma> Prop"] by simp
  have varx: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?x) \<sigma>"
    by (simp only: book_language_var_iff xtype)
  have varX: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar ?X) (Arr \<sigma> Prop)"
    by (simp only: book_language_var_iff Xtype)
  have Xx_raw: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?Xx Prop"
    by (rule book_language_App[OF varX varx])
  have Xx: "book_lambda_I_formula \<Sigma> G ?Xx" using Xx_raw by simp
  have imp: "book_lambda_I_formula \<Sigma> G (book_imp ?Xx ?Xx)"
    by (rule book_lambda_I_imp_language[OF Xx Xx])
  have occursX: "?X \<in> named_fv (book_imp ?Xx ?Xx)" unfolding book_imp_def by simp
  have body: "book_lambda_I_formula \<Sigma> G ?body"
    by (rule book_lambda_I_all_language[OF imp occursX])
  have body_fv: "named_fv ?body = {?x}"
    using distinct unfolding book_all_def book_imp_def by auto
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLam ?x ?body) (Arr (G ?x) Prop)"
    by (rule book_language_Lam[OF conjunct1[OF body]])
  have predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLam ?x ?body) (Arr \<sigma> Prop)"
    using language by (simp only: xtype)
  have closed: "named_fv (NLam ?x ?body :: 'c book_named_term) = {}" by (simp add: body_fv)
  have body_occurs: "?x \<in> named_fv (?body :: 'c book_named_term)" by (simp only: body_fv; simp)
  have relevant: "book_lambda_I (NLam ?x ?body :: 'c book_named_term)"
    by (rule iffD2[OF book_lambda_I.simps(5)], rule conjI[OF conjunct2[OF body] body_occurs])
  show ?thesis unfolding book_lambda_I_inhabitation_predicate_def
    by (rule conjI[OF predicate conjI[OF closed relevant]])
qed

theorem book_lambda_I_henkin_full_closed_term_exists:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<exists>A :: ('c book_henkin_name) book_named_term.
    book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_full_signature \<Sigma> G) G A \<sigma> \<and> named_fv A = {} \<and> book_lambda_I A"
proof -
  let ?F = "book_lambda_I_inhabitation_predicate G \<sigma> :: ('c book_henkin_name) book_named_term"
  have facts: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_signature \<Sigma> G 0) G ?F (Arr \<sigma> Prop) \<and>
    named_fv ?F = {} \<and> book_lambda_I ?F"
    by (rule book_lambda_I_inhabitation_predicate_facts[OF rich])
  have stage_declared: "BookWitness 0 \<sigma> ?F \<in> book_lambda_I_henkin_signature \<Sigma> G (Suc 0) \<sigma>"
    by (rule book_lambda_I_henkin_signature_witness[OF conjunct1[OF conjunct2[OF facts]]
      conjunct2[OF conjunct2[OF facts]] conjunct1[OF facts]])
  have declared: "BookWitness 0 \<sigma> ?F \<in> book_lambda_I_henkin_full_signature \<Sigma> G \<sigma>"
    by (rule subsetD[OF book_lambda_I_henkin_stage_in_full stage_declared])
  have term_language: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_full_signature \<Sigma> G) G (NConst (BookWitness 0 \<sigma> ?F) \<sigma>) \<sigma>"
    using declared by (simp add: book_language_const_iff)
  show ?thesis by (rule exI[where x="NConst (BookWitness 0 \<sigma> ?F) \<sigma>"],
    rule conjI[OF term_language]; simp)
qed

end
