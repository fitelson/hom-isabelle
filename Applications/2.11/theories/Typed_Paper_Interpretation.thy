theory Typed_Paper_Interpretation
  imports Typed_Paper_Translation Typed_Paper_Encoding
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Action_Model"
begin

section \<open>Interpreting the translated constants\<close>

definition pt_I :: "(paper_logical \<Rightarrow> ZF) \<Rightarrow> ('c + paper_logical) \<Rightarrow> otype \<Rightarrow> ZF" where
  "pt_I V c a = (case c of Inl d \<Rightarrow> src_I d a | Inr l \<Rightarrow> V l)"

lemma pt_model:
  assumes vm: "\<And>l. Elem (V l) (src_D (paper_logical_type l) raw_root)"
  shows "book_ZF_modal_model raw_W raw_rel raw_root src_D src_T (pt_signature S) (pt_I V)"
proof (rule book_ZF_modal_model.intro[OF src_modal_structure],
    rule book_ZF_modal_model_axioms.intro)
  fix a b
  show "book_ZF_k raw_W raw_rel src_D src_T raw_root a b \<in> explode (src_D (Arr a (Arr b a)) raw_root)"
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
  show "book_ZF_all raw_W raw_rel src_D raw_root a \<in> explode (src_D (Arr (Arr a Prop) Prop) raw_root)"
    by (simp only: explode_Elem, rule src_all_member, rule raw_worlds(1))
next
  fix a
  show "book_ZF_eq raw_W raw_rel src_D src_T raw_root a \<in> explode (src_D (Arr a (Arr a Prop)) raw_root)"
    by (simp only: explode_Elem, rule src_eq_member, rule raw_worlds(1))
next
  fix c a assume cm: "c \<in> pt_signature S a"
  show "pt_I V c a \<in> explode (src_D a raw_root)"
    using cm vm by (cases c) (auto simp: pt_I_def explode_Elem intro: src_I_type)
qed

lemma pt_interpreter_exists:
  assumes "\<And>l. Elem (V l) (src_D (paper_logical_type l) raw_root)"
  shows "\<exists>J. book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T
    (pt_signature S) (pt_I V) G J"
proof -
  interpret model: book_ZF_modal_model raw_W raw_rel raw_root src_D src_T "pt_signature S" "pt_I V"
    by (rule pt_model[OF assms])
  show ?thesis by (rule model.generic_interpretation_exists)
qed

section \<open>Partial paper assignments and total book assignments\<close>

definition pt_agree :: "sgcontext \<Rightarrow> ZF \<Rightarrow> ZF named_assignment \<Rightarrow>
    (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pt_agree G w g b \<longleftrightarrow> (\<forall>n x. g n = Some x \<longrightarrow> x = paper_enc (G n) w (b n))"

definition pt_complete :: "sgcontext \<Rightarrow> ZF \<Rightarrow> ZF named_assignment \<Rightarrow> nat \<Rightarrow> ZF" where
  "pt_complete G w g n = (case g n of None \<Rightarrow> (SOME x. Elem x (src_D (G n) w))
    | Some x \<Rightarrow> paper_dec (G n) w x)"

lemma pt_complete_type:
  assumes env: "paper_ZF_action_env_typed paper_D G w g"
  shows "book_env_typed (\<lambda>a. explode (src_D a w)) G (pt_complete G w g)"
proof (unfold book_env_typed_def, intro allI)
  fix n
  show "pt_complete G w g n \<in> explode (src_D (G n) w)"
  proof (cases "g n")
    case None
    have ex: "\<exists>x. Elem x (src_D (G n) w)"
      using src_D_nonempty[of "G n" w] by (auto simp only: explode_Elem)
    have "Elem (SOME x. Elem x (src_D (G n) w)) (src_D (G n) w)"
      by (rule someI_ex[OF ex])
    then show ?thesis by (simp only: pt_complete_def None option.case explode_Elem)
  next
    case (Some x)
    have xm: "Elem x (paper_D (G n) w)"
      using paper_ZF_action_env_value[OF env Some] by (simp only: explode_Elem)
    show ?thesis
      by (simp only: pt_complete_def Some option.case explode_Elem, rule paper_dec_type[OF xm])
  qed
qed

lemma pt_complete_agrees:
  assumes env: "paper_ZF_action_env_typed paper_D G w g"
  shows "pt_agree G w g (pt_complete G w g)"
proof (unfold pt_agree_def, intro allI impI)
  fix n x assume gx: "g n = Some x"
  have xm: "Elem x (paper_D (G n) w)"
    using paper_ZF_action_env_value[OF env gx] by (simp only: explode_Elem)
  show "x = paper_enc (G n) w (pt_complete G w g n)"
    by (simp only: pt_complete_def gx option.case paper_enc_dec[OF xm])
qed

lemma pt_agree_update:
  assumes "pt_agree G w g b"
  shows "pt_agree G w (g(n := Some (paper_enc (G n) w x))) (b(n := x))"
  using assms by (auto simp: pt_agree_def)

lemma pt_agree_move:
  assumes ww: "Elem w raw_W"
    and bt: "book_env_typed (\<lambda>a. explode (src_D a w)) G b"
    and agree: "pt_agree G w g b"
  shows "pt_agree G v (paper_ZF_action_transport_assignment G paper_T (Opair w v) g)
    (book_ZF_move src_T G w v b)"
proof (unfold pt_agree_def, intro allI impI)
  fix n y
  assume moved: "paper_ZF_action_transport_assignment G paper_T (Opair w v) g n = Some y"
  obtain x where old: "g n = Some x" and ye: "y = paper_T (G n) (Opair w v) x"
    using moved by (auto simp: paper_ZF_action_transport_assignment_def paper_hom_assignment_def
      split: option.splits)
  have xe: "x = paper_enc (G n) w (b n)"
    using agree old by (auto simp only: pt_agree_def)
  have bm: "Elem (b n) (src_D (G n) w)"
    using book_env_at[OF bt, of n] by (simp only: explode_Elem)
  show "y = paper_enc (G n) v (book_ZF_move src_T G w v b n)"
    by (simp only: ye xe paper_T_enc[OF ww bm] book_ZF_move_def)
qed

lemma pt_book_move_typed:
  assumes ww: "Elem w raw_W" and vw: "Elem v raw_W" and wv: "raw_rel w v"
    and bt: "book_env_typed (\<lambda>a. explode (src_D a w)) G b"
  shows "book_env_typed (\<lambda>a. explode (src_D a v)) G (book_ZF_move src_T G w v b)"
  using bt
  by (auto simp only: book_env_typed_def book_ZF_move_def explode_Elem
      intro: src_T_type[OF ww vw wv])

text \<open>The completion is needed only to start the comparison.
  During the abstraction induction an arbitrary compatible typed total
  assignment is transported and updated, so no unjustified claim that
  the choice of default values commutes with transport is needed.\<close>

lemma pt_abstract_matches:
  assumes graph: "E = Lambda (paper_ZF_pair_code A source target (D (G n)) (target h)) (app E)"
    and body: "\<And>z. Elem z (paper_ZF_pair_code A source target (D (G n)) (target h)) \<Longrightarrow>
      paper_ZF_action_abstraction_body compose T G n B h g z = Some (app E z)"
  shows "paper_ZF_action_abstract A source target compose D T G n B h g = Some E"
proof -
  let ?P = "paper_ZF_pair_code A source target (D (G n)) (target h)"
  let ?V = "paper_ZF_action_abstraction_body compose T G n B h g"
  have defined: "?V z \<noteq> None" if "z \<in> explode ?P" for z
    using body[of z] that by (simp only: explode_Elem option.distinct simp_thms)
  have evaluated: "paper_ZF_action_abstract A source target compose D T G n B h g =
    Some (Lambda ?P (\<lambda>z. the (?V z)))"
    by (rule paper_ZF_action_abstract_defined[OF defined])
  have eq: "Lambda ?P (\<lambda>z. the (?V z)) = Lambda ?P (app E)"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z assume "Elem z ?P"
    then show "the (?V z) = app E z" by (simp only: body option.sel)
  qed
  show ?thesis by (simp only: evaluated eq graph[symmetric])
qed

end
