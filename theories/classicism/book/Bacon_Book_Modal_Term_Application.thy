theory Bacon_Book_Modal_Term_Application
  imports Bacon_Book_Modal_Term_Classes
begin

definition book_C_identity_rep :: "'c book_named_term set \<Rightarrow> 'c book_named_term" where
  "book_C_identity_rep X = (SOME A. A \<in> X)"

definition book_C_term_app where
  "book_C_term_app \<Sigma> G w \<sigma> \<tau> X Y =
    book_C_identity_class \<Sigma> G w \<tau> (NApp (book_C_identity_rep X) (book_C_identity_rep Y))"

context book_C_identity_world
begin

lemma identity_rep_member:
  assumes domain: "X \<in> book_C_identity_domain \<Sigma> G w \<sigma>"
  shows "book_C_identity_rep X \<in> X"
proof -
  obtain A where am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    and shape: "X = book_C_identity_class \<Sigma> G w \<sigma> A"
    using domain unfolding book_C_identity_domain_def by blast
  have member: "A \<in> X" by (simp only: shape; rule identity_class_self[OF am])
  show ?thesis unfolding book_C_identity_rep_def by (rule someI[where x=A]; rule member)
qed

lemma identity_rep_typed:
  assumes domain: "X \<in> book_C_identity_domain \<Sigma> G w \<sigma>"
  shows "book_C_identity_rep X \<in> book_closed_terms \<Sigma> G \<sigma>"
proof -
  obtain A where shape: "X = book_C_identity_class \<Sigma> G w \<sigma> A"
    using domain unfolding book_C_identity_domain_def by blast
  have member: "book_C_identity_rep X \<in> X" by (rule identity_rep_member[OF domain])
  show ?thesis using member unfolding shape book_C_identity_class_def by blast
qed

lemma identity_rep_class:
  assumes domain: "X \<in> book_C_identity_domain \<Sigma> G w \<sigma>"
  shows "book_C_identity_class \<Sigma> G w \<sigma> (book_C_identity_rep X) = X"
proof -
  obtain A where am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    and shape: "X = book_C_identity_class \<Sigma> G w \<sigma> A"
    using domain unfolding book_C_identity_domain_def by blast
  have rm: "book_C_identity_rep X \<in> book_closed_terms \<Sigma> G \<sigma>" by (rule identity_rep_typed[OF domain])
  have member: "book_C_identity_rep X \<in> X" by (rule identity_rep_member[OF domain])
  have identity: "book_leibniz G \<sigma> A (book_C_identity_rep X) \<in> w"
    using member unfolding shape book_C_identity_class_def by blast
  have equal: "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> (book_C_identity_rep X)"
    using identity by (simp only: identity_class_eq_iff[OF am rm])
  show ?thesis by (rule trans[OF equal[symmetric] shape[symmetric]])
qed

theorem term_app_typed:
  assumes head: "X \<in> book_C_identity_domain \<Sigma> G w (Arr \<sigma> \<tau>)"
    and argument: "Y \<in> book_C_identity_domain \<Sigma> G w \<sigma>"
  shows "book_C_term_app \<Sigma> G w \<sigma> \<tau> X Y \<in> book_C_identity_domain \<Sigma> G w \<tau>"
  unfolding book_C_term_app_def book_C_identity_domain_def
  by (rule imageI; rule book_closed_terms_App[OF identity_rep_typed[OF head] identity_rep_typed[OF argument]])

theorem term_app_classes:
  assumes fm: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)" and am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "book_C_term_app \<Sigma> G w \<sigma> \<tau> (book_C_identity_class \<Sigma> G w (Arr \<sigma> \<tau>) F)
    (book_C_identity_class \<Sigma> G w \<sigma> A) = book_C_identity_class \<Sigma> G w \<tau> (NApp F A)"
proof -
  let ?X = "book_C_identity_class \<Sigma> G w (Arr \<sigma> \<tau>) F"
  let ?Y = "book_C_identity_class \<Sigma> G w \<sigma> A"
  have xd: "?X \<in> book_C_identity_domain \<Sigma> G w (Arr \<sigma> \<tau>)"
    unfolding book_C_identity_domain_def by (rule imageI[OF fm])
  have yd: "?Y \<in> book_C_identity_domain \<Sigma> G w \<sigma>"
    unfolding book_C_identity_domain_def by (rule imageI[OF am])
  show ?thesis unfolding book_C_term_app_def
    by (rule identity_class_application[OF identity_rep_typed[OF xd] fm identity_rep_typed[OF yd] am
      identity_rep_class[OF xd] identity_rep_class[OF yd]])
qed

end

text \<open>
  Appw([F]w,[A]w)=[FA]w is now an actual operation with a typed
  result, independent of representative choice. Hilbert choice is used
  only after proving that the supplied domain value has a closed typed
  member. No claim is made about the choice value off those domains.
  This operation is on identity classes; it is not yet the application
  of homomorphisms in the represented modal model.
\<close>

end
