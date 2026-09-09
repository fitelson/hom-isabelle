theory Bacon_Book_ZF_Model_Interpretation_Uniqueness
  imports Bacon_Book_ZF_Interpretation_Clauses
begin

context book_ZF_modal_interpretation
begin

theorem interpretation_unique:
  assumes other: "book_ZF_modal_interpretation W R root D i signature I G K"
    and language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and ww: "w \<in> explode W"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g A = K w g A"
proof -
  interpret T: book_ZF_modal_interpretation W R root D i signature I G K by (rule other)
  show ?thesis using language ww typed
  proof (induction A arbitrary: \<tau> w g)
    case (NVar n)
    show ?case by (simp only: denote_variable[OF NVar.prems(2,3)] T.denote_variable[OF NVar.prems(2,3)])
  next
    case (NConst c \<sigma>)
    have declared: "c \<in> signature \<sigma>" using NConst.prems(1) by (simp only: book_language_const_iff; blast)
    show ?case by (simp only: denote_constant[OF NConst.prems(2) declared NConst.prems(3)]
      T.denote_constant[OF NConst.prems(2) declared NConst.prems(3)])
  next
    case (NLogical l)
    show ?case by (simp only: denote_logical[OF NLogical.prems(2,3)] T.denote_logical[OF NLogical.prems(2,3)])
  next
    case (NApp F A)
    obtain \<sigma> where fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>)"
      and al: "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
      by (rule book_language_App_obtain[OF NApp.prems(1)]; rule that; assumption)
    have heads: "J w g F = K w g F" by (rule NApp.IH(1)[OF fl NApp.prems(2,3)])
    have arguments: "J w g A = K w g A" by (rule NApp.IH(2)[OF al NApp.prems(2,3)])
    show ?case by (simp only: denote_application[OF NApp.prems(2) fl al NApp.prems(3)]
      T.denote_application[OF NApp.prems(2) fl al NApp.prems(3)] heads arguments)
  next
    case (NLam n A)
    obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
      and body: "book_in_language book_minimal_logical_type UNIV signature G A \<rho>"
      by (rule book_language_Lam_obtain[OF NLam.prems(1)]; rule that; assumption)
    show ?case
    proof (simp only: denote_abstraction[OF NLam.prems(2) body NLam.prems(3)]
        T.denote_abstraction[OF NLam.prems(2) body NLam.prems(3)],
        rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
      fix p
      assume member: "Elem p (book_ZF_pairs W R (D (G n)) w)"
      have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
        and am: "Snd p \<in> explode (D (G n) (Fst p))"
        using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
      have moved: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> (Fst p))) G (book_ZF_move i G w (Fst p) g)"
        by (rule assignment_move_typed[OF NLam.prems(2) vw access NLam.prems(3)])
      have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> (Fst p))) G ((book_ZF_move i G w (Fst p) g)(n := Snd p))"
        by (rule book_env_update[OF moved am])
      show "J (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) A =
        K (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) A"
        by (rule NLam.IH[OF body vw updated])
    qed
  qed
qed

end

text \<open>
  The independent clauses determine the interpretation uniquely on
  every well-typed term and typed assignment, at every world.
  At λ, the two actual graphs have the same future-pair domain,
  and the induction hypothesis compares their bodies at every
  transported, updated assignment. No equality of arbitrary
  off-language values, generic existence theorem or canonical
  interpretation is assumed.
\<close>

end
