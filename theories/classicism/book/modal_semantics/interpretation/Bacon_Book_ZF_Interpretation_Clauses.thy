theory Bacon_Book_ZF_Interpretation_Clauses
  imports Bacon_Book_ZF_Model_Assignments
begin

section \<open>Definition 17.13 as an independent interpretation relation\<close>

locale book_ZF_modal_interpretation = book_ZF_modal_model W R root D i signature I
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF
    and D :: book_ZF_domains and i :: book_ZF_counterparts
    and signature :: "'c ssignature" and I :: "'c \<Rightarrow> otype \<Rightarrow> ZF" +
  fixes G :: sgcontext and J :: "ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ('c,book_minimal_logical) named_term \<Rightarrow> ZF"
  assumes denote_type: "\<And>w g A \<tau>. w \<in> explode W \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV signature G A \<tau> \<Longrightarrow>
      book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<Longrightarrow> J w g A \<in> explode (D \<tau> w)"
    and denote_variable: "\<And>w g n. w \<in> explode W \<Longrightarrow>
      book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<Longrightarrow> J w g (NVar n) = g n"
    and denote_constant: "\<And>w g c \<sigma>. w \<in> explode W \<Longrightarrow> c \<in> signature \<sigma> \<Longrightarrow>
      book_env_typed (\<lambda>\<tau>. explode (D \<tau> w)) G g \<Longrightarrow> J w g (NConst c \<sigma>) = i \<sigma> root w (I c \<sigma>)"
    and denote_logical: "\<And>w g l. w \<in> explode W \<Longrightarrow>
      book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<Longrightarrow>
      J w g (NLogical l) = i (book_minimal_logical_type l) root w (book_ZF_logical_root W R D i root l)"
    and denote_application: "\<And>w g F A \<sigma> \<tau>. w \<in> explode W \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>) \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV signature G A \<sigma> \<Longrightarrow>
      book_env_typed (\<lambda>\<rho>. explode (D \<rho> w)) G g \<Longrightarrow>
      J w g (NApp F A) = app (J w g F) (Opair w (J w g A))"
    and denote_abstraction: "\<And>w g n A \<tau>. w \<in> explode W \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV signature G A \<tau> \<Longrightarrow>
      book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<Longrightarrow>
      J w g (NLam n A) = Lambda (book_ZF_pairs W R (D (G n)) w)
        (\<lambda>p. J (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) A)"
begin

theorem abstraction_future_application:
  assumes ww: "w \<in> explode W" and language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and vw: "v \<in> explode W" and access: "R w v" and am: "a \<in> explode (D (G n) v)"
  shows "app (J w g (NLam n A)) (Opair v a) = J v ((book_ZF_move i G w v g)(n := a)) A"
proof -
  have ve: "Elem v W" using vw by (simp only: explode_Elem)
  have ae: "Elem a (D (G n) v)" using am by (simp only: explode_Elem)
  have pair: "Elem (Opair v a) (book_ZF_pairs W R (D (G n)) w)"
    by (simp only: book_ZF_pairs_member; rule conjI[OF ve conjI[OF access ae]])
  show ?thesis by (simp only: denote_abstraction[OF ww language typed] Lambda_app[OF pair] Fst Snd)
qed

end

text \<open>
  The interpretation relation is separate from the independent
  model definition. Its clauses specify the literal typed extension
  to named λ-terms, including the whole future Lambda graph.
  No conversion, locality or naturality field is added: those
  properties must be derived. Existence of a J for every model is
  proved from the supplied combinators as generic_interpretation_exists
  in Bacon_Book_ZF_Generic_Interpretation_Existence.
\<close>

end
