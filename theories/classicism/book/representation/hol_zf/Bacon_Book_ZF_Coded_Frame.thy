theory Bacon_Book_ZF_Coded_Frame
  imports Bacon_Book_ZF_Countable_Codes
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Canonical_Frame
begin

section \<open>The canonical frame with an explicit bounded term code\<close>

text \<open>
  FOUNDATION: standard HOL-ZF, not pure HOL.
  The HOL-ZF representation of the canonical model needs a total code of
  the carrier's terms into the elements of an actual ZF set that is
  injective on the terms admitted by the ambient signature B (all of whose
  constants are declared in B). Every set the representation codes
  injectively lives over B: canonical-world sentence sets and identity
  classes at pairs whose signature is included in B. Off-language terms
  need only be bounded; they may share codes. For a countable name carrier
  the natural-number code of Bacon_Book_ZF_Countable_Codes serves, with
  bound Nat, and is globally injective. In general the code and its bound
  are locale parameters. Sets of terms are coded by separation inside the
  bound, exactly as before.
\<close>

definition book_ZF_admitted_terms :: "'c ssignature \<Rightarrow> 'c book_named_term set" where
  "book_ZF_admitted_terms B = {A. named_in_signature B A}"

definition book_ZF_admitted_term_sets :: "'c ssignature \<Rightarrow> 'c book_named_term set set" where
  "book_ZF_admitted_term_sets B = {S. S \<subseteq> book_ZF_admitted_terms B}"

lemma book_ZF_admitted_termsI:
  "named_in_signature B A \<Longrightarrow> A \<in> book_ZF_admitted_terms B"
  unfolding book_ZF_admitted_terms_def by simp

lemma book_ZF_admitted_term_setsI:
  "S \<subseteq> book_ZF_admitted_terms B \<Longrightarrow> S \<in> book_ZF_admitted_term_sets B"
  unfolding book_ZF_admitted_term_sets_def by simp

lemma book_ZF_admitted_term_setsD:
  "S \<in> book_ZF_admitted_term_sets B \<Longrightarrow> S \<subseteq> book_ZF_admitted_terms B"
  unfolding book_ZF_admitted_term_sets_def by simp

lemma named_in_signature_mono:
  assumes inside: "named_in_signature \<Omega> A" and sub: "\<And>\<tau>. \<Omega> \<tau> \<subseteq> B \<tau>"
  shows "named_in_signature B A"
  using inside by (induction A) (auto intro: subsetD[OF sub])

locale book_full_C_coded_frame = book_full_C_canonical_frame \<Sigma> B G actual
  for \<Sigma> :: "'c ssignature" and B :: "'c ssignature" and G :: sgcontext and actual :: "'c book_C_world" +
  fixes term_code :: "'c book_named_term \<Rightarrow> ZF" and term_bound :: ZF
  assumes term_code_injective: "inj_on term_code (book_ZF_admitted_terms B)"
    and term_code_bound: "range term_code \<subseteq> explode term_bound"
begin

abbreviation admitted_terms where "admitted_terms \<equiv> book_ZF_admitted_terms B"
abbreviation admitted_term_sets where "admitted_term_sets \<equiv> book_ZF_admitted_term_sets B"

definition full_ZF_admitted :: "'c book_C_world \<Rightarrow> bool" where
  "full_ZF_admitted w \<longleftrightarrow> (\<forall>\<tau>. fst w \<tau> \<subseteq> B \<tau>)"

lemma full_ZF_admittedD:
  "full_ZF_admitted w \<Longrightarrow> fst w \<tau> \<subseteq> B \<tau>"
  unfolding full_ZF_admitted_def by blast

lemma worlds_admitted:
  assumes ww: "w \<in> worlds"
  shows "full_ZF_admitted w"
  unfolding full_ZF_admitted_def
  by (intro allI; rule book_full_C_canonical_world_data(2)[OF book_full_C_rooted_world_data(1)[OF ww]])

lemma root_admitted:
  "full_ZF_admitted actual"
  by (rule worlds_admitted[OF book_full_C_root_is_world])

lemma world_sentences_admitted:
  assumes ww: "w \<in> worlds"
  shows "snd w \<in> admitted_term_sets"
proof (rule book_ZF_admitted_term_setsI, rule subsetI)
  fix A
  assume am: "A \<in> snd w"
  have closed: "book_closed_formula_set (fst w) G (snd w)"
    by (rule book_full_C_closed_maximal_data(1)[OF book_full_C_canonical_world_data(4)[OF
      book_full_C_rooted_world_data(1)[OF ww]]])
  have formula: "book_theory_formula (fst w) G A"
    by (rule conjunct1[OF book_closed_formula_set_member[OF closed am]])
  have inside: "named_in_signature (fst w) A" by (rule book_language_signature[OF formula])
  show "A \<in> admitted_terms"
    by (rule book_ZF_admitted_termsI[OF named_in_signature_mono[OF inside full_ZF_admittedD[OF worlds_admitted[OF ww]]]])
qed

definition class_code :: "'c book_named_term set \<Rightarrow> ZF" where
  "class_code S = paper_ZF_image_code term_bound term_code S"

theorem class_code_elements:
  "explode (class_code S) = term_code ` S"
  unfolding class_code_def by (rule paper_ZF_image_code_elements[OF term_code_bound subset_UNIV])

lemma class_code_bound:
  "class_code S \<in> explode (Power term_bound)"
  unfolding class_code_def by (rule paper_ZF_image_code_type)

theorem class_code_injective:
  "inj_on class_code admitted_term_sets"
proof (rule inj_onI)
  fix S T :: "'c book_named_term set"
  assume sm: "S \<in> admitted_term_sets" and tm: "T \<in> admitted_term_sets"
    and equal: "class_code S = class_code T"
  have ss: "S \<subseteq> admitted_terms" and ts: "T \<subseteq> admitted_terms"
    by (rule book_ZF_admitted_term_setsD[OF sm], rule book_ZF_admitted_term_setsD[OF tm])
  have decoded: "explode (class_code S) = explode (class_code T)" by (rule arg_cong[OF equal])
  have images: "term_code ` S = term_code ` T" using decoded by (simp only: class_code_elements)
  show "S = T" by (rule iffD1[OF inj_on_image_eq_iff[OF term_code_injective ss ts] images])
qed

lemma class_codes_bound:
  "range class_code \<subseteq> explode (Power term_bound)"
  using class_code_bound by blast

lemma class_codes_admitted_bound:
  "class_code ` admitted_term_sets \<subseteq> explode (Power term_bound)"
  using class_code_bound by blast

definition class_decode :: "ZF \<Rightarrow> 'c book_named_term set" where
  "class_decode = inv_into admitted_term_sets class_code"

lemma class_code_inverse:
  "S \<in> admitted_term_sets \<Longrightarrow> class_decode (class_code S) = S"
  unfolding class_decode_def by (rule inv_into_f_f[OF class_code_injective]; assumption)

end

locale book_coded_ambient_signature = book_ambient_signature \<Sigma> B
  for \<Sigma> :: "'c ssignature" and B :: "'c ssignature" +
  fixes term_code :: "'c book_named_term \<Rightarrow> ZF" and term_bound :: ZF
  assumes term_code_injective: "inj_on term_code (book_ZF_admitted_terms B)"
    and term_code_bound: "range term_code \<subseteq> explode term_bound"

sublocale book_countable_ambient_signature \<subseteq>
  book_coded_ambient_signature \<Sigma> B book_ZF_countable_code HOLZF.Nat
  by (unfold_locales; rule inj_on_subset[OF book_ZF_countable_code_injective subset_UNIV]
    book_ZF_countable_code_bound)

theorem book_countable_class_code:
  fixes \<Sigma> B :: "'c::countable ssignature"
  assumes frame: "book_full_C_canonical_frame \<Sigma> B G actual"
  shows "book_full_C_coded_frame.class_code book_ZF_countable_code HOLZF.Nat =
    (book_ZF_countable_set_code :: 'c book_named_term set \<Rightarrow> ZF)"
proof -
  interpret book_full_C_coded_frame \<Sigma> B G actual book_ZF_countable_code HOLZF.Nat
    by (intro book_full_C_coded_frame.intro book_full_C_coded_frame_axioms.intro frame
      inj_on_subset[OF book_ZF_countable_code_injective subset_UNIV] book_ZF_countable_code_bound)
  show ?thesis by (rule ext) (simp only: class_code_def book_ZF_countable_set_code_def)
qed

text \<open>
  The countable ambient signature is an instance of the coded ambient
  signature with the natural-number term code (globally injective, hence
  injective on the admitted terms), so every theorem stated for the coded
  locale specialises to the earlier countable statements.
  In any canonical frame on a countable carrier, the term-class code at
  that instance is literally the earlier countable set code, as
  book_countable_class_code records; the world-code analogue is
  book_countable_world_code in Bacon_Book_ZF_World_Codes. The frame
  premise is there only because Isabelle exposes a locale definition
  outside its locale under the locale predicate. These
  equations do not restore the earlier global names: book_ZF_world_code,
  book_ZF_term_class_domain and book_ZF_powerset_image now live in the
  term-specific coded-frame context, and the earlier polymorphic
  powerset-image utility on arbitrary countable types is not recovered.
\<close>

end
