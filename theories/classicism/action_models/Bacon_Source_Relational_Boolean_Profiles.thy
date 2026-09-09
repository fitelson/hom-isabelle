theory Bacon_Source_Relational_Boolean_Profiles
  imports Bacon_Source_Relational_Binary_Logical_Application
begin

section \<open>Conjunction and disjunction have their all-domain truth conditions\<close>

text \<open>
  Two independent typed variable witnesses lift the actual model clauses
  to arbitrary proposition values a,b∈Mₜ. Under an outgoing
  homomorphism, both arguments move to the target before those clauses
  are applied. Source: Definitions 3.1, 3.3 and 3.10, pp.43–50.
  No valuation-preservation or Boolean operator identity is assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_conjunction_application_truth:
  assumes am: "a \<in> domain Prop" and bm: "b \<in> domain Prop"
  shows "valuation (paper_R_binary_logical_application signature stock domain denote Prop SAnd a b) =
    (valuation a \<and> valuation b)"
proof -
  have pr: "paper_R_type Prop" by simp
  show ?thesis
  proof (rule paper_R_binary_logical_application_truth[
      where l=SAnd and \<sigma>=Prop and test="\<lambda>a b. valuation a \<and> valuation b",
      OF pr paper_logical_type.simps(2) am bm])
    fix P Q g
    assume pl: "paper_R_in_language signature stock P Prop" and ql: "paper_R_in_language signature stock Q Prop"
      and gt: "named_env_typed domain stock g" and pa: "named_adequate g P" and qa: "named_adequate g Q"
    show "valuation (denote g (NApp (NApp (NLogical SAnd) P) Q)) =
      (valuation (denote g P) \<and> valuation (denote g Q))"
      by (rule valuation_conj[OF pl ql gt pa qa])
  qed
qed

theorem paper_R_disjunction_application_truth:
  assumes am: "a \<in> domain Prop" and bm: "b \<in> domain Prop"
  shows "valuation (paper_R_binary_logical_application signature stock domain denote Prop SOr a b) =
    (valuation a \<or> valuation b)"
proof -
  have pr: "paper_R_type Prop" by simp
  show ?thesis
  proof (rule paper_R_binary_logical_application_truth[
      where l=SOr and \<sigma>=Prop and test="\<lambda>a b. valuation a \<or> valuation b",
      OF pr paper_logical_type.simps(3) am bm])
    fix P Q g
    assume pl: "paper_R_in_language signature stock P Prop" and ql: "paper_R_in_language signature stock Q Prop"
      and gt: "named_env_typed domain stock g" and pa: "named_adequate g P" and qa: "named_adequate g Q"
    show "valuation (denote g (NApp (NApp (NLogical SOr) P) Q)) =
      (valuation (denote g P) \<or> valuation (denote g Q))"
      by (rule valuation_disj[OF pl ql gt pa qa])
  qed
qed

end

lemma paper_R_boolean_profile_values:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and am: "a \<in> paper_bbk_domain M Prop" and bm: "b \<in> paper_bbk_domain M Prop"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
  shows "paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b)) =
    (paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop a) \<and>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop b))"
    and "paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b)) =
    (paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop a) \<or>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop b))"
proof -
  have hm: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source h) (paper_arrow_target h) (paper_arrow_map h)"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF category arrow]])
  have morphism: "paper_R_bbk_model_morphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
    (paper_bbk_valuation (paper_arrow_target h)) (paper_arrow_map h)"
    using hm by (simp only: paper_R_bbk_data_morphism_def source)
  interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain (paper_arrow_target h)"
    "paper_bbk_denote (paper_arrow_target h)" "paper_bbk_valuation (paper_arrow_target h)"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  have ha: "paper_arrow_map h Prop a \<in> paper_bbk_domain (paper_arrow_target h) Prop"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] am])
  have hb: "paper_arrow_map h Prop b \<in> paper_bbk_domain (paper_arrow_target h) Prop"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] bm])
  have pr: "paper_R_type Prop" by simp
  have mapped_conjunction: "paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b) =
    paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
      (paper_bbk_denote (paper_arrow_target h)) Prop SAnd (paper_arrow_map h Prop a) (paper_arrow_map h Prop b)"
    by (rule paper_R_binary_logical_application_morphism[where l=SAnd and \<sigma>=Prop, OF morphism pr paper_logical_type.simps(2) am bm])
  show "paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b)) =
    (paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop a) \<and>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop b))"
    by (simp only: mapped_conjunction; rule Target.paper_R_conjunction_application_truth[OF ha hb])
  have mapped_disjunction: "paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b) =
    paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
      (paper_bbk_denote (paper_arrow_target h)) Prop SOr (paper_arrow_map h Prop a) (paper_arrow_map h Prop b)"
    by (rule paper_R_binary_logical_application_morphism[where l=SOr and \<sigma>=Prop, OF morphism pr paper_logical_type.simps(3) am bm])
  show "paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b)) =
    (paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop a) \<or>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop b))"
    by (simp only: mapped_disjunction; rule Target.paper_R_disjunction_application_truth[OF ha hb])
qed

theorem paper_R_conjunction_truth_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and am: "a \<in> paper_bbk_domain M Prop" and bm: "b \<in> paper_bbk_domain M Prop"
  shows "paper_bbk_truth_profile_on Arrows M
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b) =
    paper_bbk_truth_profile_on Arrows M a \<inter> paper_bbk_truth_profile_on Arrows M b"
proof (rule set_eqI)
  fix h
  show "(h \<in> paper_bbk_truth_profile_on Arrows M
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SAnd a b)) =
    (h \<in> paper_bbk_truth_profile_on Arrows M a \<inter> paper_bbk_truth_profile_on Arrows M b)"
  proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M")
    case True
    have ha: "h \<in> Arrows" and hs: "paper_arrow_source h = M" using True by blast+
    show ?thesis by (simp only: paper_bbk_truth_profile_on_member Int_iff
      paper_R_boolean_profile_values(1)[OF category am bm ha hs]; blast)
  next
    case False
    show ?thesis using False by (auto simp only: paper_bbk_truth_profile_on_member Int_iff)
  qed
qed

theorem paper_R_disjunction_truth_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and am: "a \<in> paper_bbk_domain M Prop" and bm: "b \<in> paper_bbk_domain M Prop"
  shows "paper_bbk_truth_profile_on Arrows M
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b) =
    paper_bbk_truth_profile_on Arrows M a \<union> paper_bbk_truth_profile_on Arrows M b"
proof (rule set_eqI)
  fix h
  show "(h \<in> paper_bbk_truth_profile_on Arrows M
      (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) Prop SOr a b)) =
    (h \<in> paper_bbk_truth_profile_on Arrows M a \<union> paper_bbk_truth_profile_on Arrows M b)"
  proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M")
    case True
    have ha: "h \<in> Arrows" and hs: "paper_arrow_source h = M" using True by blast+
    show ?thesis by (simp only: paper_bbk_truth_profile_on_member Un_iff
      paper_R_boolean_profile_values(2)[OF category am bm ha hs]; blast)
  next
    case False
    show ?thesis using False by (auto simp only: paper_bbk_truth_profile_on_member Un_iff)
  qed
qed

end
