theory Bacon_Book_ZF_Generic_Combinators
  imports Bacon_Book_ZF_Model_Assignments
    Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Model_Function_Extensionality
begin

section \<open>Generic combinator calculations, without a supplied interpretation\<close>

context book_ZF_modal_model
begin

lemma generic_pair:
  "w \<in> explode W \<Longrightarrow> v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow>
    a \<in> explode (D \<sigma> v) \<Longrightarrow> Elem (Opair v a) (book_ZF_pairs W R (D \<sigma>) w)"
  by (simp only: book_ZF_pairs_member explode_Elem; blast)

lemma generic_app_type:
  assumes ww: "w \<in> explode W" and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) w)"
    and am: "a \<in> explode (D \<sigma> w)"
  shows "app F (Opair w a) \<in> explode (D \<tau> w)"
  by (rule function_type[OF ww ww reflexive[OF ww] fm am])

lemma generic_restricted_application:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) w)" and am: "a \<in> explode (D \<sigma> v)"
  shows "app (i (Arr \<sigma> \<tau>) w v F) (Opair v a) = app F (Opair v a)"
  by (simp only: function_restriction[OF ww vw wv fm] book_ZF_restrict_def
    Lambda_app[OF generic_pair[OF vw vw reflexive[OF vw] am]])

lemma generic_k_current:
  assumes ww: "w \<in> explode W" and am: "a \<in> explode (D \<sigma> w)" and bm: "b \<in> explode (D \<tau> w)"
  shows "app (app (book_ZF_k W R D i w \<sigma> \<tau>) (Opair w a)) (Opair w b) = a"
  by (simp only: book_ZF_k_value[OF generic_pair[OF ww ww reflexive[OF ww] am]
      generic_pair[OF ww ww reflexive[OF ww] bm]] transport_identity[OF ww am])

lemma generic_s_current:
  assumes ww: "w \<in> explode W"
    and fm: "f \<in> explode (D (Arr \<sigma> (Arr \<tau> \<rho>)) w)"
    and gm: "g \<in> explode (D (Arr \<sigma> \<tau>) w)" and am: "a \<in> explode (D \<sigma> w)"
  shows "app (app (app (book_ZF_s W R D w \<sigma> \<tau> \<rho>) (Opair w f)) (Opair w g)) (Opair w a) =
    app (app f (Opair w a)) (Opair w (app g (Opair w a)))"
  by (rule book_ZF_s_value[OF generic_pair[OF ww ww reflexive[OF ww] fm]
      generic_pair[OF ww ww reflexive[OF ww] gm] generic_pair[OF ww ww reflexive[OF ww] am]])

lemma generic_k_transport:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
  shows "i (Arr \<sigma> (Arr \<tau> \<sigma>)) w v (book_ZF_k W R D i w \<sigma> \<tau>) = book_ZF_k W R D i v \<sigma> \<tau>"
  by (subst function_restriction[OF ww vw wv k_member_at[OF ww]];
    simp only: book_ZF_k_def outer_function_restriction[OF ww vw wv])

lemma generic_s_transport:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
  shows "i (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) w v
    (book_ZF_s W R D w \<sigma> \<tau> \<rho>) = book_ZF_s W R D v \<sigma> \<tau> \<rho>"
  by (subst function_restriction[OF ww vw wv s_member_at[OF ww]];
    simp only: book_ZF_s_def outer_function_restriction[OF ww vw wv])

definition generic_identity where
  "generic_identity w \<sigma> = app
    (app (book_ZF_s W R D w \<sigma> (Arr \<sigma> \<sigma>) \<sigma>)
      (Opair w (book_ZF_k W R D i w \<sigma> (Arr \<sigma> \<sigma>))))
    (Opair w (book_ZF_k W R D i w \<sigma> \<sigma>))"

lemma generic_identity_type:
  assumes ww: "w \<in> explode W"
  shows "generic_identity w \<sigma> \<in> explode (D (Arr \<sigma> \<sigma>) w)"
  unfolding generic_identity_def
  by (rule generic_app_type[OF ww generic_app_type[OF ww s_member_at[OF ww] k_member_at[OF ww]] k_member_at[OF ww]])

lemma generic_identity_future:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and am: "a \<in> explode (D \<sigma> v)"
  shows "app (generic_identity w \<sigma>) (Opair v a) = a"
proof -
  let ?K = "book_ZF_k W R D i w \<sigma> \<sigma>"
  have ka: "app ?K (Opair v a) \<in> explode (D (Arr \<sigma> \<sigma>) v)"
    by (rule function_type[OF ww vw wv k_member_at[OF ww] am])
  show ?thesis unfolding generic_identity_def
    by (simp only: book_ZF_s_value[OF generic_pair[OF ww ww reflexive[OF ww] k_member_at[OF ww]]
        generic_pair[OF ww ww reflexive[OF ww] k_member_at[OF ww]] generic_pair[OF ww vw wv am]]
      book_ZF_k_value[OF generic_pair[OF ww vw wv am] generic_pair[OF vw vw reflexive[OF vw] ka]]
      transport_identity[OF vw am])
qed

lemma generic_identity_graph:
  assumes ww: "w \<in> explode W"
  shows "generic_identity w \<sigma> = Lambda (book_ZF_pairs W R (D \<sigma>) w) Snd"
  by (rule function_as_lambda[OF ww generic_identity_type[OF ww]];
    simp only: Snd; rule generic_identity_future[OF ww]; assumption)

lemma generic_identity_transport:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
  shows "i (Arr \<sigma> \<sigma>) w v (generic_identity w \<sigma>) = generic_identity v \<sigma>"
  by (subst function_restriction[OF ww vw wv generic_identity_type[OF ww]];
    simp only: generic_identity_graph[OF ww] outer_function_restriction[OF ww vw wv] generic_identity_graph[OF vw])

end

text \<open>
  The identity value is S K K at the displayed types. Its membership is
  derived from the model's prescribed k/s and application closure; it is
  not an additional primitive or model field. The calculations cover every
  accessible future input and establish equality of the actual Lambda graph.
  No nonempty-domain, interpreter, canonical-model or proof-calculus premise
  is used.
\<close>

end
