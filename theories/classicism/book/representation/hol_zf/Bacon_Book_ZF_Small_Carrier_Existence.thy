theory Bacon_Book_ZF_Small_Carrier_Existence
  imports Bacon_Book_ZF_Countable_Nontrivial_Existence
    Bacon_Book_Classicism_Development.Bacon_Book_Named_Syntax_Cardinal
begin

section \<open>Model existence for ZF-small name carriers of arbitrary cardinality\<close>

text \<open>
  FOUNDATION: standard HOL-ZF, not pure HOL.
  A name carrier is ZF-small when it injects into the elements of an
  actual ZF set. Countable types are ZF-small (into Nat), and the HOL
  powerset of a ZF-small type is ZF-small (into the ZF powerset), so for
  instance the uncountable carrier nat set is ZF-small. For such a
  carrier every full-C-consistent theory, with no restriction on how
  many constants are declared, has a nontrivial modal model and an
  admissible interpretation in its original signature. The construction
  recodes the names into ('c + nat) × bool, whose all-False slice is an
  unused reserve at least as large as the declared names, and uses the
  general ambient signature and the bounded term code obtained from the
  syntax cardinal bounds. This generalises the countable construction
  displayed on pp.398–400 of Bacon's book; the cardinal invariant and
  the HOL-ZF carrier hypothesis are ours, not the book's. The HOL type
  ZF itself is not ZF-small; signatures declared over that type are covered
  by the declared-names route of Bacon_Book_ZF_Declared_Names_Existence when
  their declared union is bounded by a ZF set.
\<close>

definition book_ZF_small_carrier :: "('c \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> bool" where
  "book_ZF_small_carrier f U \<longleftrightarrow> inj f \<and> range f \<subseteq> explode U"

lemma book_ZF_small_carrierI:
  assumes "inj f" and "\<And>x. f x \<in> explode U"
  shows "book_ZF_small_carrier f U"
  using assms unfolding book_ZF_small_carrier_def by blast

lemma book_ZF_small_carrier_countable:
  "book_ZF_small_carrier (book_ZF_countable_code :: 'a::countable \<Rightarrow> ZF) HOLZF.Nat"
  unfolding book_ZF_small_carrier_def by (rule conjI[OF book_ZF_countable_code_injective book_ZF_countable_code_bound])

theorem book_ZF_small_carrier_powerset:
  fixes f :: "'a \<Rightarrow> ZF"
  assumes small: "book_ZF_small_carrier f U"
  shows "book_ZF_small_carrier (paper_ZF_image_code U f) (Power U)"
proof (rule book_ZF_small_carrierI)
  have injective: "inj f" and bound: "range f \<subseteq> explode U" using small unfolding book_ZF_small_carrier_def by blast+
  show "inj (paper_ZF_image_code U f)"
  proof (rule injI)
    fix S T :: "'a set"
    assume equal: "paper_ZF_image_code U f S = paper_ZF_image_code U f T"
    have images: "f ` S = f ` T"
      using arg_cong[OF equal, of explode]
      by (simp only: paper_ZF_image_code_elements[OF bound subset_UNIV])
    show "S = T" using images injective by (auto dest: injD)
  qed
next
  fix S :: "'a set"
  show "paper_ZF_image_code U f S \<in> explode (Power U)" by (rule paper_ZF_image_code_type)
qed

corollary book_ZF_small_carrier_nat_set:
  "book_ZF_small_carrier (paper_ZF_image_code HOLZF.Nat (book_ZF_countable_code :: nat \<Rightarrow> ZF)) (Power HOLZF.Nat)"
  by (rule book_ZF_small_carrier_powerset[OF book_ZF_small_carrier_countable])

subsection \<open>Recoding the carrier with an unused reserve\<close>

definition book_ZF_tag :: "bool \<Rightarrow> ZF" where
  "book_ZF_tag b = (if b then Empty else Singleton Empty)"

definition book_ZF_two :: ZF where
  "book_ZF_two = Upair Empty (Singleton Empty)"

lemma book_ZF_tag_injective: "inj book_ZF_tag"
  by (rule injI; simp add: book_ZF_tag_def Singleton_nonEmpty Singleton_nonEmpty[symmetric] split: if_splits)

lemma book_ZF_tag_two: "Elem (book_ZF_tag b) book_ZF_two"
  by (simp add: book_ZF_tag_def book_ZF_two_def Upair)

definition book_ZF_carrier_code :: "('c \<Rightarrow> ZF) \<Rightarrow> ('c + nat) \<times> bool \<Rightarrow> ZF" where
  "book_ZF_carrier_code f p = Opair
    (case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))
    (book_ZF_tag (snd p))"

definition book_ZF_carrier_bound :: "ZF \<Rightarrow> ZF" where
  "book_ZF_carrier_bound U = CartProd (CartProd (union U HOLZF.Nat) book_ZF_two) book_ZF_two"

theorem book_ZF_carrier_code_small:
  fixes f :: "'c \<Rightarrow> ZF"
  assumes small: "book_ZF_small_carrier f U"
  shows "book_ZF_small_carrier (book_ZF_carrier_code f) (book_ZF_carrier_bound U)"
proof (rule book_ZF_small_carrierI)
  have injective: "inj f" and bound: "range f \<subseteq> explode U" using small unfolding book_ZF_small_carrier_def by blast+
  show "inj (book_ZF_carrier_code f)"
  proof (rule injI)
    fix p q :: "('c + nat) \<times> bool"
    assume equal: "book_ZF_carrier_code f p = book_ZF_carrier_code f q"
    have components: "(case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty)) =
        (case fst q of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))"
      and tag_equal: "book_ZF_tag (snd p) = book_ZF_tag (snd q)"
      using equal unfolding book_ZF_carrier_code_def by (simp only: Opair; blast)+
    have tags: "snd p = snd q" by (rule injD[OF book_ZF_tag_injective tag_equal])
    have firsts: "fst p = fst q"
      using components
      by (cases "fst p"; cases "fst q"; simp add: Opair Singleton_nonEmpty Singleton_nonEmpty[symmetric]
        injD[OF injective] injD[OF inj_nat2Nat])
    show "p = q" using firsts tags by (rule prod_eqI)
  qed
next
  fix p :: "('c + nat) \<times> bool"
  have bound: "range f \<subseteq> explode U" using small unfolding book_ZF_small_carrier_def by blast
  have first: "Elem (case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))
    (CartProd (union U HOLZF.Nat) book_ZF_two)"
  proof (cases "fst p")
    case (Inl c)
    have in_range: "f c \<in> explode U" using bound by blast
    have in_U: "Elem (f c) U" using in_range by (simp only: explode_Elem)
    have inside: "Elem (f c) (union U HOLZF.Nat)" using in_U by (simp add: union)
    have tag: "Elem Empty book_ZF_two" by (simp add: book_ZF_two_def Upair)
    show ?thesis by (simp only: Inl sum.case CartProd; rule exI[of _ "f c"]; rule exI[of _ Empty]; simp add: inside tag)
  next
    case (Inr n)
    have inside: "Elem (nat2Nat n) (union U HOLZF.Nat)" by (simp add: union Elem_nat2Nat_Nat)
    have tag: "Elem (Singleton Empty) book_ZF_two" by (simp add: book_ZF_two_def Upair)
    show ?thesis by (simp only: Inr sum.case CartProd; rule exI[of _ "nat2Nat n"]; rule exI[of _ "Singleton Empty"]; simp add: inside tag)
  qed
  have pair: "Elem (Opair (case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))
      (book_ZF_tag (snd p))) (CartProd (CartProd (union U HOLZF.Nat) book_ZF_two) book_ZF_two)"
    by (rule iffD2[OF CartProd]; rule exI[of _ "case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty)"];
      rule exI[of _ "book_ZF_tag (snd p)"]; intro conjI; (rule first | rule book_ZF_tag_two | rule refl))
  show "book_ZF_carrier_code f p \<in> explode (book_ZF_carrier_bound U)"
    unfolding book_ZF_carrier_code_def book_ZF_carrier_bound_def explode_Elem by (rule pair)
qed

lemma book_ZF_carrier_bound_infinite:
  fixes f :: "'c \<Rightarrow> ZF"
  assumes small: "book_ZF_small_carrier f U"
  shows "infinite (explode (book_ZF_carrier_bound U))"
proof -
  have coded: "book_ZF_small_carrier (book_ZF_carrier_code f) (book_ZF_carrier_bound U)"
    by (rule book_ZF_carrier_code_small[OF small])
  have injective: "inj (book_ZF_carrier_code f)" and bound: "range (book_ZF_carrier_code f) \<subseteq> explode (book_ZF_carrier_bound U)"
    using coded unfolding book_ZF_small_carrier_def by blast+
  have naturals: "inj (\<lambda>n. book_ZF_carrier_code f (Inr n, True))"
    using injective by (auto simp: inj_on_def)
  have infinite_range: "infinite (range (\<lambda>n. book_ZF_carrier_code f (Inr n, True)))"
    using finite_imageD[OF _ naturals] infinite_UNIV_nat by blast
  have subset: "range (\<lambda>n. book_ZF_carrier_code f (Inr n, True)) \<subseteq> explode (book_ZF_carrier_bound U)"
    using bound by blast
  show ?thesis using infinite_range subset finite_subset by blast
qed

theorem book_ZF_small_carrier_term_code:
  fixes f :: "'c \<Rightarrow> ZF"
  assumes small: "book_ZF_small_carrier f U"
  obtains e :: "(('c + nat) \<times> bool) book_named_term \<Rightarrow> ZF"
  where "inj e" and "range e \<subseteq> explode (book_ZF_carrier_bound U)"
proof -
  have coded: "book_ZF_small_carrier (book_ZF_carrier_code f) (book_ZF_carrier_bound U)"
    by (rule book_ZF_carrier_code_small[OF small])
  have injective: "inj (book_ZF_carrier_code f)" and bound: "range (book_ZF_carrier_code f) \<subseteq> explode (book_ZF_carrier_bound U)"
    using coded unfolding book_ZF_small_carrier_def by blast+
  have names: "card_of (UNIV :: (('c + nat) \<times> bool) set) \<le>o card_of (explode (book_ZF_carrier_bound U))"
    by (rule card_of_ordLeqI[OF injective]; use bound in blast)
  have terms: "card_of (UNIV :: (('c + nat) \<times> bool) book_named_term set) \<le>o card_of (explode (book_ZF_carrier_bound U))"
    by (rule book_all_terms_cardinal_bound[OF book_ZF_carrier_bound_infinite[OF small] names])
  obtain e :: "(('c + nat) \<times> bool) book_named_term \<Rightarrow> ZF"
    where "inj_on e UNIV" and "e ` UNIV \<subseteq> explode (book_ZF_carrier_bound U)"
    using paper_ZF_cardinal_bounded_encoding[OF terms] by blast
  then show thesis by (rule that)
qed

subsection \<open>The recoded signature is a coded ambient signature\<close>

definition book_ZF_carrier_map :: "otype \<Rightarrow> 'c \<Rightarrow> ('c + nat) \<times> bool" where
  "book_ZF_carrier_map \<sigma> c = (Inl c, True)"

lemma book_ZF_carrier_map_injective: "inj_on (book_ZF_carrier_map \<sigma>) (\<Sigma> \<sigma>)"
  by (rule inj_onI; simp add: book_ZF_carrier_map_def)

lemma book_ZF_recoded_true:
  assumes member: "p \<in> book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>"
  shows "snd p = True"
  using member unfolding book_typed_image_signature_def book_ZF_carrier_map_def by auto

lemma book_ZF_recoded_reserve:
  "infinite (UNIV - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>)"
proof -
  have subset: "range (\<lambda>n. (Inr n, False)) \<subseteq> UNIV - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>"
    using book_ZF_recoded_true by fastforce
  have injective: "inj (\<lambda>n :: nat. ((Inr n, False) :: ('c + nat) \<times> bool))" by (rule injI) simp
  have infinite_range: "infinite (range (\<lambda>n :: nat. ((Inr n, False) :: ('c + nat) \<times> bool)))"
    using finite_imageD[OF _ injective] infinite_UNIV_nat by blast
  show ?thesis using infinite_range subset finite_subset by blast
qed

lemma book_ZF_recoded_large:
  "card_of (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>) \<le>o
    card_of (UNIV - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>)"
proof (rule card_of_ordLeqI[where f="\<lambda>p. (fst p, False)"])
  show "inj_on (\<lambda>p. (fst p, False)) (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>)"
  proof (rule inj_onI)
    fix p q assume pm: "p \<in> (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>)"
      and qm: "q \<in> (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>)"
      and equal: "(fst p, False) = (fst q, False)"
    have tags: "snd p = True" "snd q = True" using pm qm book_ZF_recoded_true by blast+
    show "p = q" using equal tags by (rule_tac prod_eqI) auto
  qed
next
  fix p assume "p \<in> (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>)"
  show "(fst p, False) \<in> UNIV - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>"
    using book_ZF_recoded_true[of "(fst p, False)"] by auto
qed

theorem book_ZF_recoded_coded_ambient:
  assumes injective: "inj e" and bound: "range e \<subseteq> explode T"
  shows "book_coded_ambient_signature (book_typed_image_signature book_ZF_carrier_map \<Sigma>) (\<lambda>_. UNIV) e T"
  by (unfold_locales; rule subset_UNIV book_ZF_recoded_reserve book_ZF_recoded_large
    inj_on_subset[OF injective subset_UNIV] bound)

subsection \<open>Original-signature model existence for ZF-small carriers\<close>

theorem book_full_C_small_carrier_nontrivial_modal_model_exists:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and carrier: "book_ZF_small_carrier f U"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
proof -
  let ?\<rho> = "book_ZF_carrier_map :: otype \<Rightarrow> 'c \<Rightarrow> ('c + nat) \<times> bool"
  let ?\<Omega> = "book_typed_image_signature ?\<rho> \<Sigma>"
  let ?T = "book_typed_name_map ?\<rho> ` S"
  obtain e :: "(('c + nat) \<times> bool) book_named_term \<Rightarrow> ZF"
    where ei: "inj e" and eb: "range e \<subseteq> explode (book_ZF_carrier_bound U)"
    using book_ZF_small_carrier_term_code[OF carrier] by blast
  have maps: "?\<rho> \<sigma> c \<in> ?\<Omega> \<sigma>" if "c \<in> \<Sigma> \<sigma>" for \<sigma> c
    by (rule book_typed_image_maps; rule that)
  have target_language: "book_theory_formula ?\<Omega> G P" if member: "P \<in> ?T" for P
  proof -
    obtain A where am: "A \<in> S" and eq: "P = book_typed_name_map ?\<rho> A" using member by (elim Set.imageE)
    show ?thesis unfolding eq by (rule book_typed_name_map_language[OF language[OF am] maps])
  qed
  have injective: "inj_on (?\<rho> \<sigma>) (\<Sigma> \<sigma>)" for \<sigma> by (rule book_ZF_carrier_map_injective)
  have target_consistent: "book_full_C_theory_consistent ?\<Omega> G ?T"
    using consistent book_full_C_consistent_typed_image_iff[where \<rho>="?\<rho>" and \<Sigma>=\<Sigma>, OF rich injective language] by blast
  interpret names: book_coded_ambient_signature ?\<Omega> "\<lambda>_. UNIV" e "book_ZF_carrier_bound U"
    by (rule book_ZF_recoded_coded_ambient[OF ei eb])
  obtain W R root D i I J where
    model: "book_ZF_nontrivial_modal_model W R root D i ?\<Omega> I" and
    interp: "book_ZF_modal_interpretation W R root D i ?\<Omega> I G J" and
    truth: "book_ZF_satisfies D G J root ?T"
    using names.book_full_C_ambient_nontrivial_modal_model_exists[OF rich target_language target_consistent]
    by blast
  interpret M: book_ZF_modal_interpretation W R root D i ?\<Omega> I G J by (rule interp)
  interpret N: book_ZF_nontrivial_modal_model W R root D i ?\<Omega> I by (rule model)
  let ?I = "\<lambda>c \<sigma>. I (?\<rho> \<sigma> c) \<sigma>"
  let ?J = "\<lambda>w g A. J w g (book_typed_name_map ?\<rho> A)"
  have pulled_model: "book_ZF_nontrivial_modal_model W R root D i \<Sigma> ?I"
    by (rule N.nontrivial_signature_pullback[OF maps])
  have pulled_interp: "book_ZF_modal_interpretation W R root D i \<Sigma> ?I G ?J"
    by (rule M.signature_pullback_interpretation[OF maps])
  have pulled_truth: "book_ZF_satisfies D G ?J root S"
    by (simp only: book_ZF_signature_pullback_satisfies; rule truth)
  show ?thesis
    apply (rule exI[where x=W], rule exI[where x=R], rule exI[where x=root])
    apply (rule exI[where x=D], rule exI[where x=i])
    apply (rule exI[where x="?I"], rule exI[where x="?J"])
    apply (rule conjI[OF pulled_model conjI[OF pulled_interp pulled_truth]])
    done
qed

corollary book_full_C_nat_set_carrier_nontrivial_modal_model_exists:
  fixes \<Sigma> :: "(nat set) ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
  by (rule book_full_C_small_carrier_nontrivial_modal_model_exists[OF rich book_ZF_small_carrier_nat_set language consistent])

text \<open>
  The hypotheses are exactly those of the countably declared theorem
  with countability of each Στ replaced by ZF-smallness of the carrier
  type. Neither theorem subsumes the other: the countable theorem allows
  any carrier (including the type ZF) but only countably many declared
  constants per type; this one allows every constant of a ZF-small
  carrier to be declared. The nat set instance is an uncountable
  carrier with no cardinality hypothesis at all.
\<close>

end
