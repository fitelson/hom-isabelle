theory Typed_Source_Model
  imports Typed_Source_Operations Typed_Source_Binary
    "Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Nontrivial_Model"
    "Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Generic_Interpretation_Existence"
begin

section \<open>Constants in the same concrete encoded domains\<close>

definition src_I :: "'c \<Rightarrow> otype \<Rightarrow> ZF" where
  "src_I c a = src_enc a raw_root (SOME x. Elem x (raw_D a raw_root))"

lemma src_I_type: "Elem (src_I c a) (src_D a raw_root)"
proof -
  have ex: "\<exists>x. Elem x (raw_D a raw_root)"
    using raw_D_nonempty[of a raw_root] by (auto simp only: explode_Elem)
  have member: "Elem (SOME x. Elem x (raw_D a raw_root)) (raw_D a raw_root)"
    by (rule someI_ex[OF ex])
  show ?thesis unfolding src_I_def by (rule src_enc_type[OF member])
qed

text \<open>The interpretation is defined for every constant name at every
  type. Consequently no restriction on the size or content of the
  nonlogical signature is needed for its typing condition.\<close>

theorem src_model:
  "book_ZF_modal_model raw_W raw_rel raw_root src_D src_T \<Sigma> src_I"
proof (rule book_ZF_modal_model.intro[OF src_modal_structure],
    rule book_ZF_modal_model_axioms.intro)
  fix a b
  show "book_ZF_k raw_W raw_rel src_D src_T raw_root a b \<in>
    explode (src_D (Arr a (Arr b a)) raw_root)"
    by (simp only: explode_Elem, rule src_K_member, rule raw_worlds(1))
next
  fix a b c
  show "book_ZF_s raw_W raw_rel src_D raw_root a b c \<in>
    explode (src_D (Arr (Arr a (Arr b c)) (Arr (Arr a b) (Arr a c))) raw_root)"
    by (simp only: explode_Elem, rule src_S_member, rule raw_worlds(1))
next
  show "book_ZF_if_future raw_W raw_rel src_D src_T raw_root \<in>
    explode (src_D (Arr Prop (Arr Prop Prop)) raw_root)"
    by (simp only: explode_Elem, rule src_if_member, rule raw_worlds(1))
next
  fix a
  show "book_ZF_all raw_W raw_rel src_D raw_root a \<in>
    explode (src_D (Arr (Arr a Prop) Prop) raw_root)"
    by (simp only: explode_Elem, rule src_all_member, rule raw_worlds(1))
next
  fix a
  show "book_ZF_eq raw_W raw_rel src_D src_T raw_root a \<in>
    explode (src_D (Arr a (Arr a Prop)) raw_root)"
    by (simp only: explode_Elem, rule src_eq_member, rule raw_worlds(1))
next
  fix c a
  assume "c \<in> \<Sigma> a"
  show "src_I c a \<in> explode (src_D a raw_root)"
    by (simp only: explode_Elem, rule src_I_type)
qed

section \<open>Worldwise inhabitation and a concrete false proposition\<close>

definition raw_false :: "ZF \<Rightarrow> ZF" where
  "raw_false w = (if Nat2nat w=0 then zprop (False,False,{})
    else if Nat2nat w=1 then zmiddle (False,False) else zbit False)"

lemma raw_false_type: "Elem (raw_false w) (raw_D Prop w)"
  by (auto simp add: raw_false_def raw_D_def
      simp del: typed_R.simps typed_S.simps split: if_splits)

lemma raw_false_truth: "\<not> raw_truth w (raw_false w)"
  by (auto simp: raw_truth_def raw_false_def zprop_def zmiddle_def zbit_def
      bit_dec_def Fst typed_two_distinct split: if_splits)

theorem src_false_at_world:
  assumes "w \<in> explode raw_W"
  shows "\<exists>p\<in>explode (src_D Prop w). \<not> Elem w p"
proof -
  have member: "src_enc Prop w (raw_false w) \<in> explode (src_D Prop w)"
    by (simp only: explode_Elem, rule src_enc_type, rule raw_false_type)
  have false: "\<not> Elem w (src_enc Prop w (raw_false w))"
    by (simp only: src_enc_truth raw_T_id raw_false_truth simp_thms)
  show ?thesis
    by (rule bexI[where x="src_enc Prop w (raw_false w)"], rule false, rule member)
qed

theorem src_nontrivial_model:
  "book_ZF_nontrivial_modal_model raw_W raw_rel raw_root src_D src_T \<Sigma> src_I"
proof (rule book_ZF_nontrivial_modal_model.intro[OF src_model],
    rule book_ZF_nontrivial_modal_model_axioms.intro)
  fix w a
  assume "w \<in> explode raw_W"
  show "explode (src_D a w) \<noteq> {}" by (rule src_D_nonempty)
next
  fix w
  assume "w \<in> explode raw_W"
  then show "\<exists>p\<in>explode (src_D Prop w). \<not> Elem w p"
    by (rule src_false_at_world)
qed

section \<open>Generic interpretation without a supplied interpreter\<close>

theorem src_interpretation_exists:
  "\<exists>J. book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T \<Sigma> src_I G J"
proof -
  interpret model: book_ZF_modal_model raw_W raw_rel raw_root src_D src_T \<Sigma> src_I
    by (rule src_model)
  show ?thesis by (rule model.generic_interpretation_exists)
qed

theorem src_nontrivial_model_with_interpretation:
  "book_ZF_nontrivial_modal_model raw_W raw_rel raw_root src_D src_T \<Sigma> src_I \<and>
    (\<exists>J. book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T \<Sigma> src_I G J)"
  by (rule conjI[OF src_nontrivial_model src_interpretation_exists])

text \<open>The independent book modal-model predicate, its explicit
  nontriviality refinement, and existence of a full typed interpretation
  are proved for the same concrete data. No modelhood or interpreter
  premise occurs in these endpoints. They use the book interface's
  documented future-restricted implication convention. This is not yet
  by itself an identification with the paper's Definition 3.20 action-model
  predicate (proved separately in Typed_Paper_Model), nor a source-formula certificate of the Boolean Completeness,
  Atomicity, BF, or Rigid Comprehension claims. Those bridges must be
  separately established rather than inferred from similar notation.\<close>

ML \<open>
  val facts = [@{thm src_model}, @{thm src_nontrivial_model},
    @{thm src_interpretation_exists}, @{thm src_nontrivial_model_with_interpretation}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "SOURCE-MODEL: concrete nontrivial book model and generic interpretation; paper formula bridge remains separate";
\<close>

end
