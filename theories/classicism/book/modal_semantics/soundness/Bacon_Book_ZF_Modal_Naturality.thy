theory Bacon_Book_ZF_Modal_Naturality
  imports
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Generic_Interpretation_Existence
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Model_Truth
begin

section \<open>Naturality, coincidence and future truth for every admissible interpretation\<close>

text \<open>
  Naturality (Lemma 17.1) was proved for the constructed generic
  interpretation. By typed-input uniqueness every admissible
  interpretation agrees with it on typed inputs, so naturality
  transfers to the locale. The identity of the trivial move follows
  directly from the counterpart identity field, and the coincidence
  property (evaluation depends only on free variables) is proved by
  structural induction on typed terms. Truth at a future world of a
  proposition value is truth of the formula there under the moved
  assignment. Nothing here uses a proof judgment, countability or
  richness.
\<close>

context book_ZF_modal_interpretation
begin

theorem denote_generic:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g A = generic_interpretation G w g A"
  by (rule interpretation_unique[OF generic_interpretation_model language ww typed])

theorem denote_natural:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "i \<tau> w v (J w g A) = J v (book_ZF_move i G w v g) A"
proof -
  have moved: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G (book_ZF_move i G w v g)"
    by (rule assignment_move_typed[OF ww vw wv typed])
  show ?thesis
    by (simp only: denote_generic[OF language ww typed] denote_generic[OF language vw moved]
      generic_interpretation_natural[OF language ww vw wv typed])
qed

theorem move_identity:
  assumes ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_move i G w w g = g"
  by (rule ext; simp only: book_ZF_move_def; rule transport_identity[OF ww book_env_at[OF typed]])

theorem denote_coincidence:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and ww: "w \<in> explode W"
    and typed_g: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and typed_h: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "J w g A = J w h A"
  using language ww typed_g typed_h agree
proof (induction A arbitrary: \<tau> w g h)
  case (NVar n)
  show ?case by (simp only: denote_variable[OF NVar.prems(2,3)] denote_variable[OF NVar.prems(2,4)];
    rule NVar.prems(5); simp)
next
  case (NConst c \<sigma>)
  have declared: "c \<in> signature \<sigma>" using NConst.prems(1) by (simp only: book_language_const_iff; blast)
  show ?case by (simp only: denote_constant[OF NConst.prems(2) declared NConst.prems(3)]
    denote_constant[OF NConst.prems(2) declared NConst.prems(4)])
next
  case (NLogical l)
  show ?case by (simp only: denote_logical[OF NLogical.prems(2,3)] denote_logical[OF NLogical.prems(2,4)])
next
  case (NApp F A)
  obtain \<sigma> where fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
    by (rule book_language_App_obtain[OF NApp.prems(1)]; rule that; assumption)
  have heads: "J w g F = J w h F"
    by (rule NApp.IH(1)[OF fl NApp.prems(2,3,4)]; rule NApp.prems(5); simp)
  have arguments: "J w g A = J w h A"
    by (rule NApp.IH(2)[OF al NApp.prems(2,3,4)]; rule NApp.prems(5); simp)
  show ?case by (simp only: denote_application[OF NApp.prems(2) fl al NApp.prems(3)]
    denote_application[OF NApp.prems(2) fl al NApp.prems(4)] heads arguments)
next
  case (NLam n A)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language book_minimal_logical_type UNIV signature G A \<rho>"
    by (rule book_language_Lam_obtain[OF NLam.prems(1)]; rule that; assumption)
  show ?case
  proof (simp only: denote_abstraction[OF NLam.prems(2) body NLam.prems(3)]
      denote_abstraction[OF NLam.prems(2) body NLam.prems(4)],
      rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix p
    assume member: "Elem p (book_ZF_pairs W R (D (G n)) w)"
    have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
      and am: "Snd p \<in> explode (D (G n) (Fst p))"
      using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
    have moved_g: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> (Fst p))) G ((book_ZF_move i G w (Fst p) g)(n := Snd p))"
      by (rule book_env_update[OF assignment_move_typed[OF NLam.prems(2) vw access NLam.prems(3)] am])
    have moved_h: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> (Fst p))) G ((book_ZF_move i G w (Fst p) h)(n := Snd p))"
      by (rule book_env_update[OF assignment_move_typed[OF NLam.prems(2) vw access NLam.prems(4)] am])
    have agree: "((book_ZF_move i G w (Fst p) g)(n := Snd p)) m =
      ((book_ZF_move i G w (Fst p) h)(n := Snd p)) m" if free: "m \<in> named_fv A" for m
    proof (cases "m = n")
      case True
      show ?thesis by (simp add: True)
    next
      case False
      have outer: "m \<in> named_fv (NLam n A)" using free False by simp
      show ?thesis using NLam.prems(5)[OF outer] False by (simp add: book_ZF_move_def)
    qed
    show "J (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) A =
      J (Fst p) ((book_ZF_move i G w (Fst p) h)(n := Snd p)) A"
      by (rule NLam.IH[OF body vw moved_g moved_h agree])
  qed
qed

theorem truth_at_future:
  assumes pl: "book_in_language book_minimal_logical_type UNIV signature G P Prop"
    and ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "Elem v (J w g P) \<longleftrightarrow> book_ZF_truth_at J v (book_ZF_move i G w v g) P"
proof -
  have pm: "J w g P \<in> explode (D Prop w)" by (rule denote_type[OF ww pl typed])
  have restricted: "i Prop w v (J w g P) = Sep (J w g P) (R v)"
    by (rule proposition_restriction[OF ww vw wv pm])
  have natural: "i Prop w v (J w g P) = J v (book_ZF_move i G w v g) P"
    by (rule denote_natural[OF pl ww vw wv typed])
  have refl: "R v v" by (rule reflexive[OF vw])
  show ?thesis unfolding book_ZF_truth_at_def
    by (simp only: natural[symmetric] restricted Sep refl simp_thms)
qed

theorem proposition_future:
  assumes pl: "book_in_language book_minimal_logical_type UNIV signature G P Prop"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and member: "Elem v (J w g P)"
  shows "v \<in> explode W" and "R w v"
proof -
  have pm: "J w g P \<in> explode (D Prop w)" by (rule denote_type[OF ww pl typed])
  have future: "explode (J w g P) \<subseteq> explode (book_ZF_future W R w)" by (rule propositions[OF ww pm])
  have inside: "Elem v (book_ZF_future W R w)"
    using member future by (auto simp only: explode_Elem)
  show "v \<in> explode W" and "R w v" using inside by (auto simp only: book_ZF_future_member explode_Elem)
qed

end

end
