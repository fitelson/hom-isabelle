theory Bacon_Book_ZF_Declared_Names_Existence
  imports Bacon_Book_ZF_Small_Carrier_Existence
begin

section \<open>Original-signature model existence for ZF-small declared names\<close>

text \<open>
  FOUNDATION: standard HOL-ZF, not pure HOL.
  The countable and small-carrier existence theorems are subsumed by one
  hypothesis on the declared names alone: the union of the declared
  constants admits an injective code into the elements of an actual ZF
  set, while the HOL name carrier stays arbitrary. Theorem 18.4 (p.398)
  is printed without a signature-cardinality qualification; its displayed
  canonical construction begins with a countable signature. The
  declared-name smallness premise, the cardinal reserve invariant and the
  bounded term code injective on admitted terms are formalization
  additions, not printed hypotheses.

  Route: recode the declared names into the carrier ('c + nat) × bool as
  before, but take as ambient signature only the declared-or-reserve
  names K = (Inl ` N ∪ range Inr) × UNIV, N the declared union. Every
  name of K is coded by the tagged carrier code, injectively on K and
  inside the tagged Cartesian bound; terms admitted by K are then
  cardinally bounded and receive a total code injective on those terms,
  which is exactly the (relativized) coded ambient interface. The
  canonical model is built there and pulled back along the original
  typed name map. No whole-carrier smallness and no countable sort on the
  carrier is used.
\<close>

definition book_ZF_small_declared :: "'c ssignature \<Rightarrow> ('c \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> bool" where
  "book_ZF_small_declared \<Sigma> f U \<longleftrightarrow>
    inj_on f (\<Union>\<tau>. \<Sigma> \<tau>) \<and> f ` (\<Union>\<tau>. \<Sigma> \<tau>) \<subseteq> explode U"

lemma book_ZF_small_declaredI:
  assumes injective: "inj_on f (\<Union>\<tau>. \<Sigma> \<tau>)"
    and bound: "\<And>c \<tau>. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> explode U"
  shows "book_ZF_small_declared \<Sigma> f U"
  using injective bound unfolding book_ZF_small_declared_def by blast

lemma book_ZF_small_declared_injective:
  "book_ZF_small_declared \<Sigma> f U \<Longrightarrow> inj_on f (\<Union>\<tau>. \<Sigma> \<tau>)"
  unfolding book_ZF_small_declared_def by blast

lemma book_ZF_small_declared_bound:
  "book_ZF_small_declared \<Sigma> f U \<Longrightarrow> f ` (\<Union>\<tau>. \<Sigma> \<tau>) \<subseteq> explode U"
  unfolding book_ZF_small_declared_def by blast

subsection \<open>Both earlier hypotheses give small declared names\<close>

theorem book_ZF_small_carrier_declared:
  "book_ZF_small_carrier f U \<Longrightarrow> book_ZF_small_declared \<Sigma> f U"
  unfolding book_ZF_small_carrier_def book_ZF_small_declared_def by (auto simp: inj_on_def)

lemma book_ZF_types_countable: "countable (UNIV :: otype set)"
proof -
  obtain f :: "otype \<Rightarrow> nat" where injective: "inj_on f UNIV"
    using iffD2[OF card_of_ordLeq book_otypes_cardinal_bound[OF infinite_UNIV_nat]] by blast
  show ?thesis unfolding countable_def by (rule exI[where x=f]; rule injective)
qed

theorem book_ZF_countable_declared:
  assumes small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
  shows "book_ZF_small_declared \<Sigma> (\<lambda>c. nat2Nat (to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) c)) HOLZF.Nat"
proof (rule book_ZF_small_declaredI)
  have countable: "countable (\<Union>\<tau>. \<Sigma> \<tau>)" by (rule countable_UN[OF book_ZF_types_countable]) (rule small)
  show "inj_on (\<lambda>c. nat2Nat (to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) c)) (\<Union>\<tau>. \<Sigma> \<tau>)"
  proof (rule inj_onI)
    fix x y
    assume xm: "x \<in> (\<Union>\<tau>. \<Sigma> \<tau>)" and ym: "y \<in> (\<Union>\<tau>. \<Sigma> \<tau>)"
      and equal: "nat2Nat (to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) x) = nat2Nat (to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) y)"
    have codes: "to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) x = to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) y" by (rule injD[OF inj_nat2Nat equal])
    show "x = y" by (rule inj_onD[OF inj_on_to_nat_on[OF countable] codes xm ym])
  qed
next
  fix c \<tau>
  show "nat2Nat (to_nat_on (\<Union>\<tau>. \<Sigma> \<tau>) c) \<in> explode HOLZF.Nat"
    by (simp add: explode_Elem Elem_nat2Nat_Nat)
qed

subsection \<open>The recoded ambient signature with a declared-names reserve\<close>

definition book_ZF_declared_names :: "'c ssignature \<Rightarrow> (('c + nat) \<times> bool) set" where
  "book_ZF_declared_names \<Sigma> = {p. fst p \<in> Inl ` (\<Union>\<tau>. \<Sigma> \<tau>) \<union> range Inr}"

lemma book_ZF_recoded_first:
  assumes member: "p \<in> book_typed_image_signature book_ZF_carrier_map \<Sigma> \<sigma>"
  shows "fst p \<in> Inl ` (\<Union>\<tau>. \<Sigma> \<tau>)"
proof -
  obtain c where cm: "c \<in> \<Sigma> \<sigma>" and shape: "p = (Inl c, True)"
    using member unfolding book_typed_image_signature_def book_ZF_carrier_map_def by auto
  have union: "c \<in> (\<Union>\<tau>. \<Sigma> \<tau>)" using cm by blast
  show ?thesis by (simp only: shape fst_conv; rule imageI[OF union])
qed

lemma book_ZF_declared_included:
  "book_typed_image_signature book_ZF_carrier_map \<Sigma> \<tau> \<subseteq> book_ZF_declared_names \<Sigma>"
  using book_ZF_recoded_first unfolding book_ZF_declared_names_def by blast

lemma book_ZF_declared_reserve:
  "infinite (book_ZF_declared_names \<Sigma> - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<tau>)"
proof -
  have inside: "(Inr n, False) \<in> book_ZF_declared_names \<Sigma>" for n
    unfolding book_ZF_declared_names_def by simp
  have subset: "range (\<lambda>n. (Inr n, False)) \<subseteq>
      book_ZF_declared_names \<Sigma> - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<tau>"
    using inside book_ZF_recoded_true by fastforce
  have injective: "inj (\<lambda>n :: nat. ((Inr n, False) :: ('c + nat) \<times> bool))" by (rule injI) simp
  have infinite_range: "infinite (range (\<lambda>n :: nat. ((Inr n, False) :: ('c + nat) \<times> bool)))"
    using finite_imageD[OF _ injective] infinite_UNIV_nat by blast
  show ?thesis using infinite_range subset finite_subset by blast
qed

lemma book_ZF_declared_large:
  "card_of (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>) \<le>o
    card_of (book_ZF_declared_names \<Sigma> - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<tau>)"
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
  fix p assume pm: "p \<in> (\<Union>\<rho>. book_typed_image_signature book_ZF_carrier_map \<Sigma> \<rho>)"
  have first: "fst p \<in> Inl ` (\<Union>\<tau>. \<Sigma> \<tau>)" using pm book_ZF_recoded_first by blast
  have inside: "(fst p, False) \<in> book_ZF_declared_names \<Sigma>"
    using first unfolding book_ZF_declared_names_def by simp
  show "(fst p, False) \<in> book_ZF_declared_names \<Sigma> - book_typed_image_signature book_ZF_carrier_map \<Sigma> \<tau>"
    using inside book_ZF_recoded_true[of "(fst p, False)"] by auto
qed

theorem book_ZF_declared_ambient:
  "book_ambient_signature (book_typed_image_signature book_ZF_carrier_map \<Sigma>) (\<lambda>_. book_ZF_declared_names \<Sigma>)"
  by (unfold_locales; rule book_ZF_declared_included book_ZF_declared_reserve book_ZF_declared_large)

subsection \<open>Bounded name and term codes for the declared-or-reserve names\<close>

lemma book_ZF_declared_names_cases:
  assumes member: "p \<in> book_ZF_declared_names \<Sigma>"
  obtains c where "fst p = Inl c" and "c \<in> (\<Union>\<tau>. \<Sigma> \<tau>)" | n where "fst p = Inr n"
  using member unfolding book_ZF_declared_names_def by auto

lemma book_ZF_declared_name_code_injective:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes injective: "inj_on f (\<Union>\<tau>. \<Sigma> \<tau>)"
  shows "inj_on (book_ZF_carrier_code f) (book_ZF_declared_names \<Sigma>)"
proof (rule inj_onI)
  fix p q :: "('c + nat) \<times> bool"
  assume pm: "p \<in> book_ZF_declared_names \<Sigma>" and qm: "q \<in> book_ZF_declared_names \<Sigma>"
    and equal: "book_ZF_carrier_code f p = book_ZF_carrier_code f q"
  have components: "(case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty)) =
      (case fst q of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))"
    and tag_equal: "book_ZF_tag (snd p) = book_ZF_tag (snd q)"
    using equal unfolding book_ZF_carrier_code_def by (simp only: Opair; blast)+
  have tags: "snd p = snd q" by (rule injD[OF book_ZF_tag_injective tag_equal])
  have firsts: "fst p = fst q"
  proof (rule book_ZF_declared_names_cases[OF pm]; rule book_ZF_declared_names_cases[OF qm])
    fix c d
    assume pc: "fst p = Inl c" and cm: "c \<in> (\<Union>\<tau>. \<Sigma> \<tau>)"
      and qd: "fst q = Inl d" and dm: "d \<in> (\<Union>\<tau>. \<Sigma> \<tau>)"
    have vals: "f c = f d" using components by (simp only: pc qd sum.case Opair; blast)
    have "c = d" by (rule inj_onD[OF injective vals cm dm])
    then show "fst p = fst q" by (simp only: pc qd)
  next
    fix c n
    assume pc: "fst p = Inl c" and qn: "fst q = Inr n"
    have "Singleton Empty = Empty" using components by (simp only: pc qn sum.case Opair; blast)
    then show "fst p = fst q" using Singleton_nonEmpty by blast
  next
    fix n c
    assume pn: "fst p = Inr n" and qc: "fst q = Inl c"
    have "Singleton Empty = Empty" using components by (simp only: pn qc sum.case Opair; blast)
    then show "fst p = fst q" using Singleton_nonEmpty by blast
  next
    fix n m
    assume pn: "fst p = Inr n" and qm': "fst q = Inr m"
    have "nat2Nat n = nat2Nat m" using components by (simp only: pn qm' sum.case Opair; blast)
    then have "n = m" by (rule injD[OF inj_nat2Nat])
    then show "fst p = fst q" by (simp only: pn qm')
  qed
  show "p = q" using firsts tags by (rule prod_eqI)
qed

lemma book_ZF_declared_name_code_bound:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes bound: "f ` (\<Union>\<tau>. \<Sigma> \<tau>) \<subseteq> explode U"
    and member: "p \<in> book_ZF_declared_names \<Sigma>"
  shows "book_ZF_carrier_code f p \<in> explode (book_ZF_carrier_bound U)"
proof -
  have first: "Elem (case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))
    (CartProd (union U HOLZF.Nat) book_ZF_two)"
  proof (rule book_ZF_declared_names_cases[OF member])
    fix c
    assume pc: "fst p = Inl c" and cm: "c \<in> (\<Union>\<tau>. \<Sigma> \<tau>)"
    have in_range: "f c \<in> explode U" using bound cm by blast
    have in_U: "Elem (f c) U" using in_range by (simp only: explode_Elem)
    have inside: "Elem (f c) (union U HOLZF.Nat)" using in_U by (simp add: union)
    have tag: "Elem Empty book_ZF_two" by (simp add: book_ZF_two_def Upair)
    show ?thesis by (simp only: pc sum.case CartProd; rule exI[of _ "f c"]; rule exI[of _ Empty]; simp add: inside tag)
  next
    fix n
    assume pn: "fst p = Inr n"
    have inside: "Elem (nat2Nat n) (union U HOLZF.Nat)" by (simp add: union Elem_nat2Nat_Nat)
    have tag: "Elem (Singleton Empty) book_ZF_two" by (simp add: book_ZF_two_def Upair)
    show ?thesis by (simp only: pn sum.case CartProd; rule exI[of _ "nat2Nat n"]; rule exI[of _ "Singleton Empty"]; simp add: inside tag)
  qed
  have pair: "Elem (Opair (case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty))
      (book_ZF_tag (snd p))) (CartProd (CartProd (union U HOLZF.Nat) book_ZF_two) book_ZF_two)"
    by (rule iffD2[OF CartProd]; rule exI[of _ "case fst p of Inl c \<Rightarrow> Opair (f c) Empty | Inr n \<Rightarrow> Opair (nat2Nat n) (Singleton Empty)"];
      rule exI[of _ "book_ZF_tag (snd p)"]; intro conjI; (rule first | rule book_ZF_tag_two | rule refl))
  show ?thesis unfolding book_ZF_carrier_code_def book_ZF_carrier_bound_def explode_Elem by (rule pair)
qed

lemma book_ZF_carrier_bound_infinite_always:
  "infinite (explode (book_ZF_carrier_bound U))"
proof -
  let ?g = "\<lambda>n. Opair (Opair (nat2Nat n) (Singleton Empty)) (book_ZF_tag False)"
  have injective: "inj ?g" by (rule injI) (simp add: Opair injD[OF inj_nat2Nat])
  have inside: "?g n \<in> explode (book_ZF_carrier_bound U)" for n
  proof -
    have first: "Elem (Opair (nat2Nat n) (Singleton Empty)) (CartProd (union U HOLZF.Nat) book_ZF_two)"
      by (simp only: CartProd; rule exI[of _ "nat2Nat n"]; rule exI[of _ "Singleton Empty"];
        simp add: union Elem_nat2Nat_Nat book_ZF_two_def Upair)
    show ?thesis unfolding book_ZF_carrier_bound_def explode_Elem
      by (rule iffD2[OF CartProd]; rule exI[of _ "Opair (nat2Nat n) (Singleton Empty)"];
        rule exI[of _ "book_ZF_tag False"]; intro conjI; (rule first | rule book_ZF_tag_two | rule refl))
  qed
  have infinite_range: "infinite (range ?g)" using finite_imageD[OF _ injective] infinite_UNIV_nat by blast
  have subset: "range ?g \<subseteq> explode (book_ZF_carrier_bound U)" using inside by blast
  show ?thesis using infinite_range subset finite_subset by blast
qed

lemma book_ZF_carrier_bound_default:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes bound: "f ` (\<Union>\<tau>. \<Sigma> \<tau>) \<subseteq> explode U"
  shows "book_ZF_carrier_code f (Inr 0, False) \<in> explode (book_ZF_carrier_bound U)"
proof -
  have member: "((Inr 0, False) :: ('c + nat) \<times> bool) \<in> book_ZF_declared_names \<Sigma>"
    unfolding book_ZF_declared_names_def by simp
  show ?thesis by (rule book_ZF_declared_name_code_bound[OF bound member])
qed

theorem book_ZF_small_declared_term_code:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes small: "book_ZF_small_declared \<Sigma> f U"
  obtains e :: "(('c + nat) \<times> bool) book_named_term \<Rightarrow> ZF"
  where "inj_on e (book_ZF_admitted_terms (\<lambda>_. book_ZF_declared_names \<Sigma>))"
    and "range e \<subseteq> explode (book_ZF_carrier_bound U)"
proof -
  let ?B = "\<lambda>_ :: otype. book_ZF_declared_names \<Sigma>"
  let ?V = "book_ZF_carrier_bound U"
  have injective: "inj_on f (\<Union>\<tau>. \<Sigma> \<tau>)" by (rule book_ZF_small_declared_injective[OF small])
  have bound: "f ` (\<Union>\<tau>. \<Sigma> \<tau>) \<subseteq> explode U" by (rule book_ZF_small_declared_bound[OF small])
  have union: "(\<Union>\<tau>. ?B \<tau>) = book_ZF_declared_names \<Sigma>" by simp
  have names: "card_of (\<Union>\<tau>. ?B \<tau>) \<le>o card_of (explode ?V)"
    unfolding union
    by (rule card_of_ordLeqI[OF book_ZF_declared_name_code_injective[OF injective]];
      use book_ZF_declared_name_code_bound[OF bound] in blast)
  have infinite: "infinite (explode ?V)" by (rule book_ZF_carrier_bound_infinite_always)
  have terms: "card_of {A :: (('c + nat) \<times> bool) book_named_term. named_in_signature ?B A} \<le>o card_of (explode ?V)"
    by (rule book_admitted_syntax_cardinal_bound[OF infinite names])
  obtain e0 :: "(('c + nat) \<times> bool) book_named_term \<Rightarrow> ZF"
    where e0i: "inj_on e0 {A. named_in_signature ?B A}"
      and e0b: "e0 ` {A. named_in_signature ?B A} \<subseteq> explode ?V"
    using paper_ZF_cardinal_bounded_encoding[OF terms] by blast
  let ?z = "book_ZF_carrier_code f (Inr 0, False)"
  have zm: "?z \<in> explode ?V" by (rule book_ZF_carrier_bound_default[OF bound])
  let ?e = "\<lambda>A. if named_in_signature ?B A then e0 A else ?z"
  have ei: "inj_on ?e (book_ZF_admitted_terms ?B)"
  proof (rule inj_onI)
    fix A C :: "(('c + nat) \<times> bool) book_named_term"
    assume am: "A \<in> book_ZF_admitted_terms ?B" and cm: "C \<in> book_ZF_admitted_terms ?B" and equal: "?e A = ?e C"
    have an: "named_in_signature ?B A" and cn: "named_in_signature ?B C"
      using am cm unfolding book_ZF_admitted_terms_def by simp_all
    have "e0 A = e0 C" using equal by (simp only: an cn if_True)
    then show "A = C" by (rule inj_onD[OF e0i]) (use an cn in simp_all)
  qed
  have eb: "range ?e \<subseteq> explode ?V" using e0b zm by auto
  show thesis by (rule that[OF ei eb])
qed

theorem book_ZF_declared_coded_ambient:
  assumes injective: "inj_on e (book_ZF_admitted_terms (\<lambda>_. book_ZF_declared_names \<Sigma>))"
    and bound: "range e \<subseteq> explode T"
  shows "book_coded_ambient_signature (book_typed_image_signature book_ZF_carrier_map \<Sigma>)
    (\<lambda>_. book_ZF_declared_names \<Sigma>) e T"
  by (unfold_locales; rule book_ZF_declared_included book_ZF_declared_reserve book_ZF_declared_large injective bound)

subsection \<open>Original-signature model existence for small declared names\<close>

theorem book_full_C_small_declared_nontrivial_modal_model_exists:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and declared: "book_ZF_small_declared \<Sigma> f U"
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
    where ei: "inj_on e (book_ZF_admitted_terms (\<lambda>_. book_ZF_declared_names \<Sigma>))"
      and eb: "range e \<subseteq> explode (book_ZF_carrier_bound U)"
    using book_ZF_small_declared_term_code[OF declared] by blast
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
  interpret names: book_coded_ambient_signature ?\<Omega> "\<lambda>_. book_ZF_declared_names \<Sigma>" e "book_ZF_carrier_bound U"
    by (rule book_ZF_declared_coded_ambient[OF ei eb])
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

subsection \<open>The type ZF as name carrier with set-bounded declared names\<close>

corollary book_full_C_ZF_carrier_nontrivial_modal_model_exists:
  fixes \<Sigma> :: "ZF ssignature"
  assumes rich: "sg_rich G"
    and bounded: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> explode U"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
proof -
  have declared: "book_ZF_small_declared \<Sigma> id U"
    by (rule book_ZF_small_declaredI[OF inj_on_id]; use bounded in auto)
  show ?thesis by (rule book_full_C_small_declared_nontrivial_modal_model_exists[OF rich declared language consistent])
qed

subsection \<open>The earlier scopes as consequences of the new endpoint\<close>

corollary book_full_C_small_carrier_nontrivial_modal_model_exists_from_small_declared:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and carrier: "book_ZF_small_carrier f U"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
  by (rule book_full_C_small_declared_nontrivial_modal_model_exists[OF rich
    book_ZF_small_carrier_declared[OF carrier] language consistent])

corollary book_full_C_countable_nontrivial_modal_model_exists_from_small_declared:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
  by (rule book_full_C_small_declared_nontrivial_modal_model_exists[OF rich
    book_ZF_countable_declared[OF small] language consistent])

text \<open>
  Scope. The only signature-size hypothesis is declared-name ZF-smallness:
  an injective code of the declared union into the elements of one ZF
  set. The whole-carrier and countable theorems remain in force with
  their independent proofs and are re-derived here as corollaries. On the
  carrier ZF, containment of the declared union in a ZF set suffices with
  the identity code; countably declared signatures on ZF were already
  covered. Signatures whose declared union admits no bounded injection are
  outside this construction; that is a limitation of the injective
  syntax-coding method, not a proof that every theory in such a signature
  lacks a set-valued model, since the independent model's constant
  interpretation need not be injective. All other qualifications
  (full minimal language, rich stock, nontrivial class, root consequence,
  HOL-ZF, future-restricted implication, literal box) are unchanged.
\<close>

end
