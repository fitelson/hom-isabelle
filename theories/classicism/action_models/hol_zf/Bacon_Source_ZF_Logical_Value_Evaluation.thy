theory Bacon_Source_ZF_Logical_Value_Evaluation
  imports Bacon_Source_ZF_Logical_Values Bacon_Source_ZF_Dependent_Function_Graphs
begin

section \<open>Evaluate the six graph values only on their specified pair domains\<close>

text \<open>
  The following equations unfold exactly the six p.56 clauses.
  Each first application requires its pair in the outer graph domain;
  a binary second application requires its pair at the first arrow's
  target. These are equations of constructed sets/graphs, not claims
  that the values already belong to a selected logical stock.
\<close>

lemma paper_ZF_logical_not_apply:
  assumes pair: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
  shows "app (paper_ZF_logical_value A source target compose identity D T W SNot) (Opair i p) =
    Sep (paper_ZF_outgoing_code A source (target i)) (\<lambda>j. \<not> Elem j p)"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF pair])

lemma paper_ZF_logical_and_apply:
  assumes first: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
    and second: "Elem (Opair j q) (paper_ZF_pair_code A source target (D Prop) (target i))"
  shows "app (app (paper_ZF_logical_value A source target compose identity D T W SAnd) (Opair i p)) (Opair j q) =
    Sep (T Prop j p) (\<lambda>k. Elem k q)"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF first] paper_ZF_pair_lambda_apply[OF second])

lemma paper_ZF_logical_or_apply:
  assumes first: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
    and second: "Elem (Opair j q) (paper_ZF_pair_code A source target (D Prop) (target i))"
  shows "app (app (paper_ZF_logical_value A source target compose identity D T W SOr) (Opair i p)) (Opair j q) =
    union (T Prop j p) q"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF first] paper_ZF_pair_lambda_apply[OF second])

lemma paper_ZF_logical_forall_apply:
  assumes pair: "Elem (Opair i F) (paper_ZF_pair_code A source target (D (Arr \<sigma> Prop)) W)"
  shows "app (paper_ZF_logical_value A source target compose identity D T W (SAll \<sigma>)) (Opair i F) =
    Sep (paper_ZF_outgoing_code A source (target i))
      (\<lambda>j. \<forall>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a)))"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF pair])

lemma paper_ZF_logical_exists_apply:
  assumes pair: "Elem (Opair i F) (paper_ZF_pair_code A source target (D (Arr \<sigma> Prop)) W)"
  shows "app (paper_ZF_logical_value A source target compose identity D T W (SEx \<sigma>)) (Opair i F) =
    Sep (paper_ZF_outgoing_code A source (target i))
      (\<lambda>j. \<exists>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a)))"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF pair])

lemma paper_ZF_logical_identity_apply:
  assumes first: "Elem (Opair i a) (paper_ZF_pair_code A source target (D \<sigma>) W)"
    and second: "Elem (Opair j b) (paper_ZF_pair_code A source target (D \<sigma>) (target i))"
  shows "app (app (paper_ZF_logical_value A source target compose identity D T W (SEq \<sigma>)) (Opair i a)) (Opair j b) =
    Sep (paper_ZF_outgoing_code A source (target j)) (\<lambda>k. T \<sigma> k (T \<sigma> j a) = T \<sigma> k b)"
  by (simp only: paper_ZF_logical_value.simps paper_ZF_pair_lambda_apply[OF first] paper_ZF_pair_lambda_apply[OF second])

section \<open>Membership in the resulting proposition sets\<close>

lemma paper_ZF_logical_not_member:
  assumes pair: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
  shows "Elem j (app (paper_ZF_logical_value A source target compose identity D T W SNot) (Opair i p)) \<longleftrightarrow>
    j \<in> explode A \<and> source j = target i \<and> \<not> Elem j p"
  by (simp only: paper_ZF_logical_not_apply[where D=D and W=W, OF pair] Sep paper_ZF_outgoing_code_member; blast)

lemma paper_ZF_logical_and_member:
  assumes first: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
    and second: "Elem (Opair j q) (paper_ZF_pair_code A source target (D Prop) (target i))"
  shows "Elem k (app (app (paper_ZF_logical_value A source target compose identity D T W SAnd) (Opair i p)) (Opair j q))
    \<longleftrightarrow> Elem k (T Prop j p) \<and> Elem k q"
  by (simp only: paper_ZF_logical_and_apply[where D=D and W=W, OF first second] Sep)

lemma paper_ZF_logical_or_member:
  assumes first: "Elem (Opair i p) (paper_ZF_pair_code A source target (D Prop) W)"
    and second: "Elem (Opair j q) (paper_ZF_pair_code A source target (D Prop) (target i))"
  shows "Elem k (app (app (paper_ZF_logical_value A source target compose identity D T W SOr) (Opair i p)) (Opair j q))
    \<longleftrightarrow> Elem k (T Prop j p) \<or> Elem k q"
  by (simp only: paper_ZF_logical_or_apply[where D=D and W=W, OF first second] union)

lemma paper_ZF_logical_forall_member:
  assumes pair: "Elem (Opair i F) (paper_ZF_pair_code A source target (D (Arr \<sigma> Prop)) W)"
  shows "Elem j (app (paper_ZF_logical_value A source target compose identity D T W (SAll \<sigma>)) (Opair i F))
    \<longleftrightarrow> j \<in> explode A \<and> source j = target i \<and>
      (\<forall>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a)))"
  by (simp only: paper_ZF_logical_forall_apply[where D=D and W=W and \<sigma>=\<sigma>, OF pair] Sep paper_ZF_outgoing_code_member; blast)

lemma paper_ZF_logical_exists_member:
  assumes pair: "Elem (Opair i F) (paper_ZF_pair_code A source target (D (Arr \<sigma> Prop)) W)"
  shows "Elem j (app (paper_ZF_logical_value A source target compose identity D T W (SEx \<sigma>)) (Opair i F))
    \<longleftrightarrow> j \<in> explode A \<and> source j = target i \<and>
      (\<exists>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a)))"
  by (simp only: paper_ZF_logical_exists_apply[where D=D and W=W and \<sigma>=\<sigma>, OF pair] Sep paper_ZF_outgoing_code_member; blast)

lemma paper_ZF_logical_identity_member:
  assumes first: "Elem (Opair i a) (paper_ZF_pair_code A source target (D \<sigma>) W)"
    and second: "Elem (Opair j b) (paper_ZF_pair_code A source target (D \<sigma>) (target i))"
  shows "Elem k (app (app (paper_ZF_logical_value A source target compose identity D T W (SEq \<sigma>)) (Opair i a)) (Opair j b))
    \<longleftrightarrow> k \<in> explode A \<and> source k = target j \<and> T \<sigma> k (T \<sigma> j a) = T \<sigma> k b"
  by (simp only: paper_ZF_logical_identity_apply[where D=D and W=W and \<sigma>=\<sigma>, OF first second] Sep paper_ZF_outgoing_code_member; blast)

section \<open>A typed predicate graph makes each quantified test legitimate\<close>

text \<open>
  The raw All/Ex equations above use total HOL graph application.
  If F is a dependent function graph on the indicated predicate pair
  domain, each j,a selected by the clause is an actual graph input,
  and its value lies in the target proposition domain. A future
  premodel use must obtain this graph premise from the arrow subaction;
  it is not supplied by a raw Dσ→t membership assertion alone.
\<close>

lemma paper_ZF_logical_quantifier_test_type:
  assumes graph: "F \<in> explode (paper_ZF_Pi (paper_ZF_pair_code A source target (D \<sigma>) W)
      (\<lambda>z. D Prop (target (Fst z))))"
    and arrow: "j \<in> explode A" and origin: "source j = W"
    and argument: "a \<in> explode (D \<sigma> (target j))"
  shows "app F (Opair j a) \<in> explode (D Prop (target j))"
proof -
  have pair: "Elem (Opair j a) (paper_ZF_pair_code A source target (D \<sigma>) W)"
    using arrow origin argument by (simp only: paper_ZF_pair_code_member; blast)
  have result: "Elem (app F (Opair j a)) (D Prop (target (Fst (Opair j a))))"
    by (rule paper_ZF_Pi_value[OF graph pair])
  show ?thesis using result by (simp only: Fst explode_Elem)
qed

end
