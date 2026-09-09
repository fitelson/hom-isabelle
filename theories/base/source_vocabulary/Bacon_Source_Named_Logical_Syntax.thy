theory Bacon_Source_Named_Logical_Syntax
  imports Bacon_Source_Named_Charts Bacon_Source_Propositional
begin

section \<open>The named paper basis and its literal λ abbreviations\<close>

text \<open>
  The primitive applications are ¬A, A∧B, A∨B, A=σB, ∀σF, and ∃σF.
  Figure 1 defines → as λpq.¬p∨q and ↔ as λpq.(¬p∨q)∧(¬q∨p).
  Source: Bacon–Dorr §1.1 and Figure 1, pp.5–6.

  Isabelle representation. Two distinct names of type t are chosen from
  the rich stock G for these closed operators. Implication and biconditional
  apply those operators literally: they are not direct Boolean formulas.
  The chosen binder names may also occur in argument terms, which are
  outside the operators' binding scope. No substitution or β simplification
  of these applications is asserted. No H proof or model is introduced.
\<close>

definition named_paper_not :: "'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_not A = NApp (NLogical SNot) A"
definition named_paper_and :: "'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_and A B = NApp (NApp (NLogical SAnd) A) B"
definition named_paper_or :: "'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_or A B = NApp (NApp (NLogical SOr) A) B"
definition named_paper_eq :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_eq \<sigma> A B = NApp (NApp (NLogical (SEq \<sigma>)) A) B"
definition named_paper_all :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_all \<sigma> F = NApp (NLogical (SAll \<sigma>)) F"
definition named_paper_ex :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_ex \<sigma> F = NApp (NLogical (SEx \<sigma>)) F"

definition named_paper_p :: "sgcontext \<Rightarrow> nat" where
  "named_paper_p G = named_chart_fresh G [] Prop"
definition named_paper_q :: "sgcontext \<Rightarrow> nat" where
  "named_paper_q G = named_chart_fresh G [named_paper_p G] Prop"

lemma named_paper_p_type: "sg_rich G \<Longrightarrow> G (named_paper_p G) = Prop"
  unfolding named_paper_p_def by (rule named_chart_fresh_type; assumption)
lemma named_paper_q_type: "sg_rich G \<Longrightarrow> G (named_paper_q G) = Prop"
  unfolding named_paper_q_def by (rule named_chart_fresh_type; assumption)
lemma named_paper_names_distinct:
  assumes rich: "sg_rich G"
  shows "named_paper_p G \<noteq> named_paper_q G"
  using named_chart_fresh_notin[where ns="[named_paper_p G]" and \<sigma>=Prop, OF rich]
  unfolding named_paper_q_def by auto

definition named_paper_imp_const :: "sgcontext \<Rightarrow> 'c paper_named_term" where
  "named_paper_imp_const G = NLam (named_paper_p G) (NLam (named_paper_q G)
    (named_paper_or (named_paper_not (NVar (named_paper_p G))) (NVar (named_paper_q G))))"
definition named_paper_iff_const :: "sgcontext \<Rightarrow> 'c paper_named_term" where
  "named_paper_iff_const G = NLam (named_paper_p G) (NLam (named_paper_q G)
    (named_paper_and
      (named_paper_or (named_paper_not (NVar (named_paper_p G))) (NVar (named_paper_q G)))
      (named_paper_or (named_paper_not (NVar (named_paper_q G))) (NVar (named_paper_p G)))))"
definition named_paper_imp :: "sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_imp G A B = NApp (NApp (named_paper_imp_const G) A) B"
definition named_paper_iff :: "sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "named_paper_iff G A B = NApp (NApp (named_paper_iff_const G) A) B"

subsection \<open>Typing the first-class applications\<close>

lemma named_paper_unary_type:
  assumes head: "paper_logical_type l = Arr \<sigma> \<tau>" and arg: "has_ntype paper_logical_type G A \<sigma>"
  shows "has_ntype paper_logical_type G (NApp (NLogical l) A) \<tau>"
proof -
  have ht: "has_ntype paper_logical_type G (NLogical l) (Arr \<sigma> \<tau>)"
    using has_ntype.Logical[where L=paper_logical_type and G=G and l=l] by (simp only: head)
  show ?thesis by (rule has_ntype.App[OF ht arg])
qed

lemma named_paper_binary_type:
  assumes head: "paper_logical_type l = Arr \<sigma> (Arr \<rho> \<tau>)"
    and A: "has_ntype paper_logical_type G A \<sigma>" and B: "has_ntype paper_logical_type G B \<rho>"
  shows "has_ntype paper_logical_type G (NApp (NApp (NLogical l) A) B) \<tau>"
  by (rule has_ntype.App[OF named_paper_unary_type[OF head A] B])

lemma named_paper_not_type:
  "has_ntype paper_logical_type G A Prop \<Longrightarrow> has_ntype paper_logical_type G (named_paper_not A) Prop"
  unfolding named_paper_not_def by (rule named_paper_unary_type[OF paper_logical_type.simps(1)]; assumption)
lemma named_paper_and_type:
  "has_ntype paper_logical_type G A Prop \<Longrightarrow> has_ntype paper_logical_type G B Prop \<Longrightarrow>
    has_ntype paper_logical_type G (named_paper_and A B) Prop"
  unfolding named_paper_and_def by (rule named_paper_binary_type[OF paper_logical_type.simps(2)]; assumption)
lemma named_paper_or_type:
  "has_ntype paper_logical_type G A Prop \<Longrightarrow> has_ntype paper_logical_type G B Prop \<Longrightarrow>
    has_ntype paper_logical_type G (named_paper_or A B) Prop"
  unfolding named_paper_or_def by (rule named_paper_binary_type[OF paper_logical_type.simps(3)]; assumption)
lemma named_paper_eq_type:
  "has_ntype paper_logical_type G A \<sigma> \<Longrightarrow> has_ntype paper_logical_type G B \<sigma> \<Longrightarrow>
    has_ntype paper_logical_type G (named_paper_eq \<sigma> A B) Prop"
  unfolding named_paper_eq_def by (rule named_paper_binary_type[OF paper_logical_type.simps(6)]; assumption)
lemma named_paper_all_type:
  "has_ntype paper_logical_type G F (Arr \<sigma> Prop) \<Longrightarrow>
    has_ntype paper_logical_type G (named_paper_all \<sigma> F) Prop"
  unfolding named_paper_all_def by (rule named_paper_unary_type[OF paper_logical_type.simps(4)]; assumption)
lemma named_paper_ex_type:
  "has_ntype paper_logical_type G F (Arr \<sigma> Prop) \<Longrightarrow>
    has_ntype paper_logical_type G (named_paper_ex \<sigma> F) Prop"
  unfolding named_paper_ex_def by (rule named_paper_unary_type[OF paper_logical_type.simps(5)]; assumption)

lemma named_paper_prop_variables:
  assumes rich: "sg_rich G"
  shows "has_ntype paper_logical_type G (NVar (named_paper_p G)) Prop"
    and "has_ntype paper_logical_type G (NVar (named_paper_q G)) Prop"
  using has_ntype.Var[where L=paper_logical_type and G=G and n="named_paper_p G"]
    has_ntype.Var[where L=paper_logical_type and G=G and n="named_paper_q G"]
  by (simp_all only: named_paper_p_type[OF rich] named_paper_q_type[OF rich])

lemma named_paper_imp_const_type:
  assumes rich: "sg_rich G"
  shows "has_ntype paper_logical_type G (named_paper_imp_const G) (Arr Prop (Arr Prop Prop))"
proof -
  have body: "has_ntype paper_logical_type G
    (named_paper_or (named_paper_not (NVar (named_paper_p G))) (NVar (named_paper_q G))) Prop"
    by (rule named_paper_or_type[OF named_paper_not_type[OF named_paper_prop_variables(1)[OF rich]]
      named_paper_prop_variables(2)[OF rich]])
  have lambdas: "has_ntype paper_logical_type G (named_paper_imp_const G)
    (Arr (G (named_paper_p G)) (Arr (G (named_paper_q G)) Prop))"
    unfolding named_paper_imp_const_def by (rule has_ntype.Lam, rule has_ntype.Lam[OF body])
  show ?thesis using lambdas by (simp only: named_paper_p_type[OF rich] named_paper_q_type[OF rich])
qed

lemma named_paper_iff_const_type:
  assumes rich: "sg_rich G"
  shows "has_ntype paper_logical_type G (named_paper_iff_const G) (Arr Prop (Arr Prop Prop))"
proof -
  have first: "has_ntype paper_logical_type G
    (named_paper_or (named_paper_not (NVar (named_paper_p G))) (NVar (named_paper_q G))) Prop"
    by (rule named_paper_or_type[OF named_paper_not_type[OF named_paper_prop_variables(1)[OF rich]]
      named_paper_prop_variables(2)[OF rich]])
  have second: "has_ntype paper_logical_type G
    (named_paper_or (named_paper_not (NVar (named_paper_q G))) (NVar (named_paper_p G))) Prop"
    by (rule named_paper_or_type[OF named_paper_not_type[OF named_paper_prop_variables(2)[OF rich]]
      named_paper_prop_variables(1)[OF rich]])
  have lambdas: "has_ntype paper_logical_type G (named_paper_iff_const G)
    (Arr (G (named_paper_p G)) (Arr (G (named_paper_q G)) Prop))"
    unfolding named_paper_iff_const_def
    by (rule has_ntype.Lam, rule has_ntype.Lam, rule named_paper_and_type[OF first second])
  show ?thesis using lambdas by (simp only: named_paper_p_type[OF rich] named_paper_q_type[OF rich])
qed

lemma named_paper_imp_type:
  assumes rich: "sg_rich G" and A: "has_ntype paper_logical_type G A Prop" and B: "has_ntype paper_logical_type G B Prop"
  shows "has_ntype paper_logical_type G (named_paper_imp G A B) Prop"
  unfolding named_paper_imp_def by (rule has_ntype.App[OF has_ntype.App[OF named_paper_imp_const_type[OF rich] A] B])
lemma named_paper_iff_type:
  assumes rich: "sg_rich G" and A: "has_ntype paper_logical_type G A Prop" and B: "has_ntype paper_logical_type G B Prop"
  shows "has_ntype paper_logical_type G (named_paper_iff G A B) Prop"
  unfolding named_paper_iff_def by (rule has_ntype.App[OF has_ntype.App[OF named_paper_iff_const_type[OF rich] A] B])

subsection \<open>Signature and free-name accounting without substitution\<close>

lemma named_paper_primitive_signatures:
  "named_in_signature \<Sigma> (named_paper_not A) = named_in_signature \<Sigma> A"
  "named_in_signature \<Sigma> (named_paper_and A B) = (named_in_signature \<Sigma> A \<and> named_in_signature \<Sigma> B)"
  "named_in_signature \<Sigma> (named_paper_or A B) = (named_in_signature \<Sigma> A \<and> named_in_signature \<Sigma> B)"
  "named_in_signature \<Sigma> (named_paper_eq \<sigma> A B) = (named_in_signature \<Sigma> A \<and> named_in_signature \<Sigma> B)"
  "named_in_signature \<Sigma> (named_paper_all \<sigma> F) = named_in_signature \<Sigma> F"
  "named_in_signature \<Sigma> (named_paper_ex \<sigma> F) = named_in_signature \<Sigma> F"
  by (simp_all add: named_paper_not_def named_paper_and_def named_paper_or_def named_paper_eq_def named_paper_all_def named_paper_ex_def)

lemma named_paper_operator_signatures:
  "named_in_signature \<Sigma> (named_paper_imp_const G)"
  "named_in_signature \<Sigma> (named_paper_iff_const G)"
  by (simp_all add: named_paper_imp_const_def named_paper_iff_const_def named_paper_primitive_signatures)

lemma named_paper_defined_signatures:
  "named_in_signature \<Sigma> (named_paper_imp G A B) = (named_in_signature \<Sigma> A \<and> named_in_signature \<Sigma> B)"
  "named_in_signature \<Sigma> (named_paper_iff G A B) = (named_in_signature \<Sigma> A \<and> named_in_signature \<Sigma> B)"
  by (simp_all add: named_paper_imp_def named_paper_iff_def named_paper_operator_signatures)

lemma named_paper_primitive_fv:
  "named_fv (named_paper_not A) = named_fv A"
  "named_fv (named_paper_and A B) = named_fv A \<union> named_fv B"
  "named_fv (named_paper_or A B) = named_fv A \<union> named_fv B"
  "named_fv (named_paper_eq \<sigma> A B) = named_fv A \<union> named_fv B"
  "named_fv (named_paper_all \<sigma> F) = named_fv F"
  "named_fv (named_paper_ex \<sigma> F) = named_fv F"
  by (simp_all add: named_paper_not_def named_paper_and_def named_paper_or_def named_paper_eq_def named_paper_all_def named_paper_ex_def)

lemma named_paper_operators_closed:
  "named_fv (named_paper_imp_const G) = {}"
  "named_fv (named_paper_iff_const G) = {}"
  by (auto simp: named_paper_imp_const_def named_paper_iff_const_def named_paper_primitive_fv)

lemma named_paper_defined_fv:
  "named_fv (named_paper_imp G A B) = named_fv A \<union> named_fv B"
  "named_fv (named_paper_iff G A B) = named_fv A \<union> named_fv B"
  by (simp_all add: named_paper_imp_def named_paper_iff_def named_paper_operators_closed)

end
