theory Bacon_Book_Full_Term_Quasi_Functionality
  imports Bacon_Book_Function_Identity_Predicate Bacon_Book_Full_MF_Instances
begin

context book_full_C_canonical_frame
begin

theorem full_term_future_application_separates:
  assumes world: "w \<in> worlds"
    and fm: "F \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and hm: "H \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and agrees: "\<And>v A. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow> A \<in> book_closed_terms (fst v) G \<sigma> \<Longrightarrow>
      book_C_identity_class (fst v) G (snd v) \<tau> (NApp F A) = book_C_identity_class (fst v) G (snd v) \<tau> (NApp H A)"
  shows "book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) F = book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) H"
proof -
  let ?n = "book_MF_argument G \<sigma> \<tau>"
  let ?P = "book_function_identity_predicate G ?n \<tau> F H"
  let ?U = "book_all G ?n (book_leibniz G \<tau> (NApp F (NVar ?n)) (NApp H (NVar ?n)))"
  have ww: "w \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF world])
  interpret W: book_C_identity_world "fst w" G "snd w" by (rule book_full_C_world_identity_algebra[OF rich ww])
  have nt: "G ?n = \<sigma>" by (rule book_MF_names_type(3)[OF rich])
  have fl: "book_in_language book_minimal_logical_type UNIV (fst w) G F (Arr \<sigma> \<tau>)" by (rule book_closed_terms_language[OF fm])
  have hl: "book_in_language book_minimal_logical_type UNIV (fst w) G H (Arr \<sigma> \<tau>)" by (rule book_closed_terms_language[OF hm])
  have fc: "named_fv F = {}" by (rule book_closed_terms_closed[OF fm])
  have hc: "named_fv H = {}" by (rule book_closed_terms_closed[OF hm])
  have predicate: "book_in_language book_minimal_logical_type UNIV (fst w) G ?P (Arr \<sigma> Prop)"
    by (rule book_function_identity_predicate_language[OF rich nt fl hl])
  have pc: "named_fv ?P = {}" by (rule book_function_identity_predicate_closed[OF fc hc])
  have ul: "book_theory_formula (fst w) G ?U"
    unfolding book_all_def using book_language_App[OF book_all_operator_language predicate]
    by (simp only: nt book_function_identity_predicate_def)
  have uc: "named_fv ?U = {}" by (simp add: book_all_fv book_leibniz_fv fc hc)
  have every: "\<forall>v\<in>worlds. le w v \<longrightarrow> ?U \<in> snd v"
  proof (intro ballI impI)
    fix v
    assume vw: "v \<in> worlds" and access: "le w v"
    have vv: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF vw])
    interpret V: book_C_identity_world "fst v" G "snd v" by (rule book_full_C_world_identity_algebra[OF rich vv])
    have fv: "F \<in> book_closed_terms (fst v) G (Arr \<sigma> \<tau>)" by (rule book_full_C_closed_terms_future[OF rich ww vv access fm])
    have hv: "H \<in> book_closed_terms (fst v) G (Arr \<sigma> \<tau>)" by (rule book_full_C_closed_terms_future[OF rich ww vv access hm])
    have applications: "\<forall>A\<in>book_closed_terms (fst v) G \<sigma>. NApp ?P A \<in> snd v"
    proof (rule ballI)
      fix A
      assume am: "A \<in> book_closed_terms (fst v) G \<sigma>"
      have identity: "book_leibniz G \<tau> (NApp F A) (NApp H A) \<in> snd v"
        using agrees[OF vw access am] by (simp only: V.identity_class_eq_iff[OF book_closed_terms_App[OF fv am] book_closed_terms_App[OF hv am]])
      show "NApp ?P A \<in> snd v" by (rule V.function_identity_predicate_instance_member[OF nt fv hv am identity])
    qed
    have pv: "?P \<in> book_closed_terms (fst v) G (Arr \<sigma> Prop)"
      by (rule book_closed_termsI[OF book_function_identity_predicate_language[OF rich nt
        book_closed_terms_language[OF fv] book_closed_terms_language[OF hv]] pc])
    have Hmax: "book_closed_maximal_extension (fst v) G (book_full_C_closed_theorems (fst v) G \<union> {}) (snd v)"
      using book_full_C_canonical_world_data(4)[OF vv] unfolding book_full_C_closed_maximal_extension_def .
    have universal: "NApp (NLogical (SBAll \<sigma>)) ?P \<in> snd v"
      using applications by (simp only: book_closed_maximal_forall_iff[OF rich Hmax book_full_C_canonical_world_data(5)[OF vv] pv])
    show "?U \<in> snd v" using universal by (simp only: book_all_def nt book_function_identity_predicate_def)
  qed
  have necessary: "book_box G ?U \<in> snd w" using every by (simp only: book_proposition_18_3[OF world ul uc])
  have original: "book_full_C_proves (fst w) G (book_MF_condition G \<sigma> \<tau> ?n F H)"
    by (rule book_full_C_MF_instance[OF rich nt fl hl]; simp add: fc hc)
  have conditional: "book_full_C_theory_derivable (fst w) G (snd w) (book_imp (book_box G ?U) (book_leibniz G (Arr \<sigma> \<tau>) F H))"
    using book_full_C_theory_from_C[where S="snd w", OF rich original] by (simp only: book_MF_condition_def)
  have il: "book_theory_formula (fst w) G (book_leibniz G (Arr \<sigma> \<tau>) F H)" by (rule book_leibniz_language[OF rich fl hl])
  have derived: "book_full_C_theory_derivable (fst w) G (snd w) (book_leibniz G (Arr \<sigma> \<tau>) F H)"
    by (rule book_full_C_theory_MP[OF book_full_C_theory_assume[OF necessary book_box_language[OF rich ul]] conditional il])
  have ic: "named_fv (book_leibniz G (Arr \<sigma> \<tau>) F H) = {}" by (simp add: book_leibniz_fv fc hc)
  have identity: "book_leibniz G (Arr \<sigma> \<tau>) F H \<in> snd w"
    by (rule book_full_C_closed_maximal_consequence[OF rich book_full_C_canonical_world_data(4)[OF ww] derived ic])
  show ?thesis by (simp only: W.identity_class_eq_iff[OF fm hm]; rule identity)
qed

theorem full_term_quasi_functional:
  assumes world: "w \<in> worlds"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and yd: "Y \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and agrees: "\<And>v a. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
      a \<in> book_C_identity_domain (fst v) G (snd v) \<sigma> \<Longrightarrow>
      book_C_term_app (fst v) G (snd v) \<sigma> \<tau> (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X) a =
      book_C_term_app (fst v) G (snd v) \<sigma> \<tau> (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) Y) a"
  shows "X = Y"
proof -
  obtain F where fm: "F \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and xs: "X = book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) F"
    using xd unfolding book_C_identity_domain_def by blast
  obtain H where hm: "H \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and ys: "Y = book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) H"
    using yd unfolding book_C_identity_domain_def by blast
  have ww: "w \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF world])
  have pointwise: "book_C_identity_class (fst v) G (snd v) \<tau> (NApp F A) =
    book_C_identity_class (fst v) G (snd v) \<tau> (NApp H A)"
    if vw: "v \<in> worlds" and access: "le w v" and am: "A \<in> book_closed_terms (fst v) G \<sigma>" for v A
  proof -
    have vv: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF vw])
    interpret V: book_C_identity_world "fst v" G "snd v" by (rule book_full_C_world_identity_algebra[OF rich vv])
    have fv: "F \<in> book_closed_terms (fst v) G (Arr \<sigma> \<tau>)" by (rule book_full_C_closed_terms_future[OF rich ww vv access fm])
    have hv: "H \<in> book_closed_terms (fst v) G (Arr \<sigma> \<tau>)" by (rule book_full_C_closed_terms_future[OF rich ww vv access hm])
    have ad: "book_C_identity_class (fst v) G (snd v) \<sigma> A \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
      unfolding book_C_identity_domain_def by (rule imageI[OF am])
    show ?thesis using agrees[OF vw access ad]
      by (simp only: xs ys book_full_C_term_counterpart_class[OF rich ww vv access fm]
        book_full_C_term_counterpart_class[OF rich ww vv access hm] V.term_app_classes[OF fv am] V.term_app_classes[OF hv am])
  qed
  have equal: "book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) F =
    book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) H"
    by (rule full_term_future_application_separates[OF world fm hm pointwise])
  show ?thesis by (simp only: xs ys; rule equal)
qed

end

text \<open>
  Closed function terms are separated by their applications throughout
  the full-C future. Witness completeness supplies the universal identity
  at each future world, Proposition 18.3 supplies its necessity at w,
  and the actual all-type MF theorem gives function identity at w.
  The codomain τ may be any full type, including e. Agreement only at
  w is not substituted for agreement at every future world.
  The final theorem states quasi-functionality for the actual class
  domains, counterpart maps and application, not only for chosen terms.
  This is the separation ingredient for Proposition 18.4's functional
  inverse, not yet construction of that inverse or a full modal model.
\<close>

end
