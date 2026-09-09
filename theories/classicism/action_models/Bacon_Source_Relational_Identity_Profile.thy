theory Bacon_Source_Relational_Identity_Profile
  imports Bacon_Source_Relational_Binary_Logical_Application
begin

section \<open>Primitive identity at every pair of original domain values\<close>

text \<open>
  For σ∈R and a,b∈Mσ, the value of the primitive =σ applied
  to a and b is true exactly when a=b. Source: Definition 3.1(iii.f),
  p.44. The generic binary witness proof uses two distinct σ-variable
  names, so the arguments are independent even when their values differ.
  No closed denotability, Functionality, or full-F model is assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_identity_application_truth:
  assumes sr: "paper_R_type \<sigma>" and am: "a \<in> domain \<sigma>" and bm: "b \<in> domain \<sigma>"
  shows "valuation (paper_R_binary_logical_application signature stock domain denote \<sigma> (SEq \<sigma>) a b) = (a = b)"
proof (rule paper_R_binary_logical_application_truth[
    where test="(=)" and l="SEq \<sigma>" and \<sigma>=\<sigma>,
    OF sr paper_logical_type.simps(6) am bm])
  fix P Q g
  assume pl: "paper_R_in_language signature stock P \<sigma>" and ql: "paper_R_in_language signature stock Q \<sigma>"
    and typed: "named_env_typed domain stock g" and pa: "named_adequate g P" and qa: "named_adequate g Q"
  show "valuation (denote g (NApp (NApp (NLogical (SEq \<sigma>)) P) Q)) = (denote g P = denote g Q)"
    by (rule valuation_identity[OF pl ql typed pa qa])
qed

end

section \<open>The identity profile records equality after each outgoing arrow\<close>

lemma paper_R_identity_profile_value:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows" and object: "M \<in> Obj"
    and sr: "paper_R_type \<sigma>" and am: "a \<in> paper_bbk_domain M \<sigma>" and bm: "b \<in> paper_bbk_domain M \<sigma>"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
  shows "paper_bbk_valuation (paper_arrow_target h)
      (paper_arrow_map h Prop (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M)
        (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b)) = (paper_arrow_map h \<sigma> a = paper_arrow_map h \<sigma> b)"
proof -
  have data: "paper_R_bbk_data_morphism \<Sigma> G (paper_arrow_source h) (paper_arrow_target h) (paper_arrow_map h)"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF category arrow]])
  have morphism: "paper_R_bbk_model_morphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
      (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
      (paper_bbk_valuation (paper_arrow_target h)) (paper_arrow_map h)"
    using data by (simp only: paper_R_bbk_data_morphism_def source)
  have hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h)) (paper_arrow_map h)"
    by (rule paper_R_bbk_model_morphism_raw[OF morphism])
  have ha: "paper_arrow_map h \<sigma> a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
    by (rule paper_R_bbk_homomorphism_domain[OF hom am])
  have hb: "paper_arrow_map h \<sigma> b \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
    by (rule paper_R_bbk_homomorphism_domain[OF hom bm])
  have moved: "paper_arrow_map h Prop (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b) =
    paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
      (paper_bbk_denote (paper_arrow_target h)) \<sigma> (SEq \<sigma>) (paper_arrow_map h \<sigma> a) (paper_arrow_map h \<sigma> b)"
    by (rule paper_R_binary_logical_application_morphism[OF morphism sr paper_logical_type.simps(6) am bm])
  interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain (paper_arrow_target h)"
    "paper_bbk_denote (paper_arrow_target h)" "paper_bbk_valuation (paper_arrow_target h)"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  show ?thesis by (simp only: moved; rule Target.paper_R_identity_application_truth[OF sr ha hb])
qed

theorem paper_R_identity_truth_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows" and object: "M \<in> Obj"
    and sr: "paper_R_type \<sigma>" and am: "a \<in> paper_bbk_domain M \<sigma>" and bm: "b \<in> paper_bbk_domain M \<sigma>"
  shows "paper_bbk_truth_profile_on Arrows M (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b) =
    {h\<in>Arrows. paper_arrow_source h = M \<and> paper_arrow_map h \<sigma> a = paper_arrow_map h \<sigma> b}"
proof (rule set_eqI)
  fix h
  show "(h \<in> paper_bbk_truth_profile_on Arrows M (paper_R_binary_logical_application \<Sigma> G (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b)) =
      (h \<in> {h\<in>Arrows. paper_arrow_source h = M \<and> paper_arrow_map h \<sigma> a = paper_arrow_map h \<sigma> b})"
  proof (cases "h \<in> Arrows \<and> paper_arrow_source h = M")
    case True
    have ha: "h \<in> Arrows" and hs: "paper_arrow_source h = M" using True by blast+
    show ?thesis by (simp only: paper_bbk_truth_profile_on_member mem_Collect_eq
      paper_R_identity_profile_value[OF category object sr am bm ha hs]; blast)
  next
    case False
    then show ?thesis by (auto simp only: paper_bbk_truth_profile_on_member mem_Collect_eq)
  qed
qed

end
