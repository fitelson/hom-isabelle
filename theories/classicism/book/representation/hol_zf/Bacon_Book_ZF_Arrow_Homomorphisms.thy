theory Bacon_Book_ZF_Arrow_Homomorphisms
  imports Bacon_Book_ZF_Proposition_Restriction
    Bacon_Book_Modal_Representation.Bacon_Book_Full_Function_Step
begin

section \<open>The recursive graph values are future homomorphisms\<close>

context book_full_C_coded_frame
begin

definition full_ZF_arrow_decode where
  "full_ZF_arrow_decode \<sigma> w F = (\<lambda>p.
    if p \<in> book_modalized_exponential_pairs worlds le (\<lambda>v. explode (full_ZF_D \<sigma> v)) w
    then app F (Opair (book_ZF_world_code (fst p)) (snd p)) else undefined)"

theorem full_ZF_h_arrow_homomorphism:
  assumes ww: "w \<in> worlds"
    and member: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
  shows "full_ZF_arrow_decode \<sigma> w (full_ZF_h (Arr \<sigma> \<tau>) w X) \<in>
    book_modalized_exponential worlds le (\<lambda>v. explode (full_ZF_D \<sigma> v)) (full_ZF_i \<sigma>)
      (\<lambda>v. explode (full_ZF_D \<tau> v)) (full_ZF_i \<tau>) w"
proof -
  interpret R: book_full_function_step \<Sigma> B G actual \<sigma> \<tau>
    "\<lambda>v. explode (full_ZF_D \<sigma> v)" "full_ZF_i \<sigma>" "full_ZF_h \<sigma>"
    "\<lambda>v. explode (full_ZF_D \<tau> v)" "full_ZF_i \<tau>" "full_ZF_h \<tau>"
    by (rule book_full_function_step.intro[OF book_full_C_canonical_frame_axioms];
      rule book_full_function_step_axioms.intro; rule full_ZF_representation_bijection)
  have same: "full_ZF_arrow_decode \<sigma> w (full_ZF_h (Arr \<sigma> \<tau>) w X) = R.Step.function_h w X"
  proof (rule ext)
    fix p :: "'c book_C_world \<times> ZF"
    obtain v a where ps: "p = (v,a)" by (cases p; blast)
    show "full_ZF_arrow_decode \<sigma> w (full_ZF_h (Arr \<sigma> \<tau>) w X) p = R.Step.function_h w X p"
    proof (cases "p \<in> book_modalized_exponential_pairs worlds le (\<lambda>v. explode (full_ZF_D \<sigma> v)) w")
      case True
      have vw: "v \<in> worlds" and access: "le w v" and am: "a \<in> explode (full_ZF_D \<sigma> v)"
        using True by (auto simp only: ps book_modalized_exponential_pairs_iff)
      have inverse: "R.Step.Arg.j v a = full_ZF_j \<sigma> v a"
        by (simp only: R.Step.Arg.j_def full_ZF_j_def full_ZF_inverse_def)
      show ?thesis by (simp only: full_ZF_arrow_decode_def if_P[OF True] ps if_P[OF True[unfolded ps]] fst_conv snd_conv
        R.Step.function_h_on[OF vw access am] full_ZF_arrow_value[OF vw access am] inverse)
    next
      case False
      show ?thesis by (simp only: full_ZF_arrow_decode_def if_not_P[OF False] R.Step.function_h_normal[OF False])
    qed
  qed
  show ?thesis by (simp only: same; rule R.canonical_function_homomorphism[OF ww member])
qed

theorem full_ZF_arrow_domain_homomorphisms:
  assumes ww: "w \<in> worlds" and member: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
  shows "full_ZF_arrow_decode \<sigma> w F \<in>
    book_modalized_exponential worlds le (\<lambda>v. explode (full_ZF_D \<sigma> v)) (full_ZF_i \<sigma>)
      (\<lambda>v. explode (full_ZF_D \<tau> v)) (full_ZF_i \<tau>) w"
proof -
  obtain X where xm: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and shape: "F = full_ZF_h (Arr \<sigma> \<tau>) w X"
    using member unfolding full_ZF_D_elements[OF worlds_admitted[OF ww]] by blast
  show ?thesis by (simp only: shape; rule full_ZF_h_arrow_homomorphism[OF ww xm])
qed

end

text \<open>
  Every function value in the single all-type ZF family is a genuine
  homomorphism on the future argument domains (Definition 17.9).
  The earlier generic function step is instantiated here with both
  lower bijections proved from the actual recursion. No lower-type
  representation or homomorphism condition remains an extra premise.
  Decoding only removes the representation of worlds and pairs; it
  does not change application on the graph's domain.
\<close>

end
