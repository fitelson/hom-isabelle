theory Bacon_Source_Named_Model_Vector_Denotation
  imports Bacon_Source_Named_BBK_Interface
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Vectors
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Conversion
begin

section \<open>Finite-vector facts in an arbitrary independent named model\<close>

text \<open>
  In every named BBK model, α-equivalent terms have equal denotations.
  For closed α-equivalent terms, the assignments may differ. Finite
  applications preserve equality of the head and corresponding arguments.
  Source: Bacon–Dorr Definition 3.1(ii.b–d), pp.43–44.

  Representation: this context is paper_named_bbk_model itself, not a
  finite-frame structure or its tagged construction. Generated α first
  gives typed βη; the proved inclusion into raw conversion then supplies
  the model's literal conversion premise. Locality handles closed terms.
  Status: no Functionality, pointwise λ-extensionality, or converse model
  transport is assumed. All argument and assignment guards remain explicit.
\<close>

context paper_named_bbk_model
begin

theorem paper_named_alpha_denote:
  assumes alpha: "named_alpha stock A B"
    and language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "denote g A = denote g B"
proof -
  have conversion: "named_beta_eta_in_language paper_logical_type signature stock \<sigma> A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  have raw: "named_raw_beta_eta paper_logical_type stock \<sigma> A B"
    by (rule named_conversion_to_raw[OF conversion])
  have right: "named_in_language paper_logical_type signature stock B \<sigma>"
    by (rule conjunct2[OF named_beta_eta_languages[OF conversion]])
  have adequate_B: "named_adequate g B"
    using adequate named_alpha_fv[OF alpha] unfolding named_adequate_def by simp
  show ?thesis by (rule denote_beta_eta[OF raw language right typed adequate adequate_B])
qed

theorem paper_named_closed_alpha_denote:
  assumes alpha: "named_alpha stock A B"
    and language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and closed: "named_fv A = {}"
    and first: "named_env_typed domain stock g"
    and second: "named_env_typed domain stock h"
  shows "denote g A = denote h B"
proof -
  have ga: "named_adequate g A" and ha: "named_adequate h A"
    by (simp_all add: named_adequate_def closed)
  have local_eq: "denote g A = denote h A"
    by (rule denote_locality[OF language first second ga ha]) (simp add: closed)
  have renamed: "denote h A = denote h B"
    by (rule paper_named_alpha_denote[OF alpha language second ha])
  show ?thesis by (rule trans[OF local_eq renamed])
qed

theorem paper_named_vector_self_denote:
  assumes language: "named_in_language paper_logical_type signature stock A \<tau>"
    and typed: "named_env_typed domain stock g"
    and adequate_A: "named_adequate g A"
    and adequate_app: "named_adequate g (named_app_vec (named_lam_vec ns A) (map NVar ns))"
  shows "denote g (named_app_vec (named_lam_vec ns A) (map NVar ns)) = denote g A"
proof -
  have conversion: "named_beta_eta_in_language paper_logical_type signature stock \<tau>
    (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
    by (rule named_lam_vec_self_application[OF language])
  have raw: "named_raw_beta_eta paper_logical_type stock \<tau>
    (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
    by (rule named_conversion_to_raw[OF conversion])
  have redex: "named_in_language paper_logical_type signature stock
    (named_app_vec (named_lam_vec ns A) (map NVar ns)) \<tau>"
    by (rule conjunct1[OF named_beta_eta_languages[OF conversion]])
  show ?thesis by (rule denote_beta_eta[OF raw redex language typed adequate_app adequate_A])
qed

theorem paper_named_app_vec_cong:
  assumes as_language:
      "list_all2 (\<lambda>A \<sigma>. named_in_language paper_logical_type signature stock A \<sigma>) As \<sigma>s"
    and bs_language:
      "list_all2 (\<lambda>B \<sigma>. named_in_language paper_logical_type signature stock B \<sigma>) Bs \<sigma>s"
    and f_language: "named_in_language paper_logical_type signature stock F (sarrow_type \<sigma>s \<tau>)"
    and h_language: "named_in_language paper_logical_type signature stock H (sarrow_type \<sigma>s \<tau>)"
    and g_typed: "named_env_typed domain stock g"
    and j_typed: "named_env_typed domain stock j"
    and fa: "named_adequate g F" and ha: "named_adequate j H"
    and as_adequate: "\<And>A. A \<in> set As \<Longrightarrow> named_adequate g A"
    and bs_adequate: "\<And>B. B \<in> set Bs \<Longrightarrow> named_adequate j B"
    and heads: "denote g F = denote j H"
    and arguments: "list_all2 (\<lambda>A B. denote g A = denote j B) As Bs"
  shows "denote g (named_app_vec F As) = denote j (named_app_vec H Bs)"
  using as_language bs_language f_language h_language fa ha
    as_adequate bs_adequate heads arguments
proof (induction As arbitrary: Bs \<sigma>s F H)
  case Nil
  have types: "\<sigma>s = []" using Nil.prems(1) by simp
  have bs: "Bs = []" using Nil.prems(2) by (simp add: types)
  show ?case using Nil.prems(9) by (simp add: bs)
next
  case (Cons A As)
  obtain \<sigma> \<rho>s where types: "\<sigma>s = \<sigma> # \<rho>s"
    using Cons.prems(1) by (cases \<sigma>s) auto
  obtain B Cs where bs: "Bs = B # Cs"
    using Cons.prems(2) by (cases Bs) (auto simp: types)
  have at: "named_in_language paper_logical_type signature stock A \<sigma>"
    and tail_a: "list_all2 (\<lambda>A \<sigma>. named_in_language paper_logical_type signature stock A \<sigma>) As \<rho>s"
    using Cons.prems(1) by (simp_all add: types)
  have bt: "named_in_language paper_logical_type signature stock B \<sigma>"
    and tail_b: "list_all2 (\<lambda>B \<sigma>. named_in_language paper_logical_type signature stock B \<sigma>) Cs \<rho>s"
    using Cons.prems(2) by (simp_all add: types bs)
  have ft: "named_in_language paper_logical_type signature stock F (Arr \<sigma> (sarrow_type \<rho>s \<tau>))"
    and ht: "named_in_language paper_logical_type signature stock H (Arr \<sigma> (sarrow_type \<rho>s \<tau>))"
    using Cons.prems(3,4) by (simp_all add: types)
  have aa: "named_adequate g A" by (rule Cons.prems(7)) simp
  have ba: "named_adequate j B" by (rule Cons.prems(8)) (simp add: bs)
  have next_fa: "named_adequate g (NApp F A)"
    using Cons.prems(5) aa unfolding named_adequate_def by auto
  have next_ha: "named_adequate j (NApp H B)"
    using Cons.prems(6) ba unfolding named_adequate_def by auto
  have ab: "denote g A = denote j B"
    and tail_eq: "list_all2 (\<lambda>A B. denote g A = denote j B) As Cs"
    using Cons.prems(10) by (simp_all add: bs)
  have next_eq: "denote g (NApp F A) = denote j (NApp H B)"
    by (rule denote_application_cong[OF ft at ht bt g_typed j_typed
      next_fa next_ha Cons.prems(9) ab])
  have tail_aa: "\<And>X. X \<in> set As \<Longrightarrow> named_adequate g X"
    by (rule Cons.prems(7)) simp
  have tail_ba: "\<And>X. X \<in> set Cs \<Longrightarrow> named_adequate j X"
    by (rule Cons.prems(8)) (simp add: bs)
  have result: "denote g (named_app_vec (NApp F A) As) =
    denote j (named_app_vec (NApp H B) Cs)"
    by (rule Cons.IH[OF tail_a tail_b named_language_App[OF ft at]
      named_language_App[OF ht bt] next_fa next_ha tail_aa tail_ba next_eq tail_eq])
  show ?case using result by (simp add: bs)
qed

end

end
