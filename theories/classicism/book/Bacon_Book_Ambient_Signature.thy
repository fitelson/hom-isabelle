theory Bacon_Book_Ambient_Signature
  imports Bacon_Book_Named_Syntax_Cardinal Bacon_Book_Typed_Name_Inverse
begin

section \<open>Ambient signatures with reserves of arbitrary infinite cardinality\<close>

text \<open>
  The book's construction preceding Definition 18.8 (p.399) fixes an
  ambient language with unused names at every type. Here the reserve
  Bτ − Στ is only required to be infinite and at least as large as the
  whole declared signature; no countability of the name carrier is
  assumed. Half of each reserve receives the Henkin witness names (via a
  chosen injection, using the syntax cardinal bounds), and the other half
  remains unused, so the same two conditions hold again for the enlarged
  signature. This is what makes the construction iterate along the
  successor worlds of Proposition 18.3 for signatures of any cardinality.
\<close>

locale book_ambient_signature =
  fixes \<Sigma> :: "'c ssignature" and B :: "'c ssignature"
  assumes ambient_included: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> B \<tau>"
    and ambient_reserve: "\<And>\<tau>. infinite (B \<tau> - \<Sigma> \<tau>)"
    and ambient_large: "\<And>\<tau>. card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
begin

definition book_ambient_scale :: "('c + nat) set" where
  "book_ambient_scale = (\<Union>\<rho>. \<Sigma> \<rho>) <+> (UNIV :: nat set)"

lemma scale_infinite: "infinite book_ambient_scale"
proof -
  have subset: "Inr ` (UNIV :: nat set) \<subseteq> book_ambient_scale" unfolding book_ambient_scale_def Plus_def by blast
  have inf: "infinite (Inr ` (UNIV :: nat set))" using finite_imageD[OF _ inj_Inr] infinite_UNIV_nat by blast
  show ?thesis using inf subset finite_subset by blast
qed

lemma names_le_scale: "card_of (\<Union>\<rho>. \<Sigma> \<rho>) \<le>o card_of book_ambient_scale"
  unfolding book_ambient_scale_def by (rule card_of_Plus1)

lemma scale_le_reserve: "card_of book_ambient_scale \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
    using ambient_reserve infinite_iff_card_of_nat by blast
  show ?thesis unfolding book_ambient_scale_def
    by (rule card_of_Plus_ordLeq_infinite[OF ambient_reserve ambient_large naturals])
qed

lemma double_scale_le_reserve:
  "card_of (book_ambient_scale <+> book_ambient_scale) \<le>o card_of (B \<tau> - \<Sigma> \<tau>)"
proof -
  have same: "card_of (book_ambient_scale <+> book_ambient_scale) =o card_of book_ambient_scale"
    using card_of_Plus_infinite[OF scale_infinite ordLeq_refl[OF card_of_Card_order]] by blast
  show ?thesis by (rule ordIso_ordLeq_trans[OF same scale_le_reserve])
qed

definition book_ambient_split :: "otype \<Rightarrow> ('c + nat) + ('c + nat) \<Rightarrow> 'c" where
  "book_ambient_split \<tau> = (SOME f. inj_on f (book_ambient_scale <+> book_ambient_scale) \<and>
    f ` (book_ambient_scale <+> book_ambient_scale) \<subseteq> B \<tau> - \<Sigma> \<tau>)"

lemma book_ambient_split_spec:
  "inj_on (book_ambient_split \<tau>) (book_ambient_scale <+> book_ambient_scale)"
  "book_ambient_split \<tau> ` (book_ambient_scale <+> book_ambient_scale) \<subseteq> B \<tau> - \<Sigma> \<tau>"
proof -
  have exists: "\<exists>f. inj_on f (book_ambient_scale <+> book_ambient_scale) \<and>
    f ` (book_ambient_scale <+> book_ambient_scale) \<subseteq> B \<tau> - \<Sigma> \<tau>"
    using double_scale_le_reserve[of \<tau>] unfolding card_of_ordLeq[symmetric] by blast
  have both: "inj_on (book_ambient_split \<tau>) (book_ambient_scale <+> book_ambient_scale) \<and>
    book_ambient_split \<tau> ` (book_ambient_scale <+> book_ambient_scale) \<subseteq> B \<tau> - \<Sigma> \<tau>"
    unfolding book_ambient_split_def by (rule someI_ex[OF exists])
  show "inj_on (book_ambient_split \<tau>) (book_ambient_scale <+> book_ambient_scale)"
    and "book_ambient_split \<tau> ` (book_ambient_scale <+> book_ambient_scale) \<subseteq> B \<tau> - \<Sigma> \<tau>"
    using both by blast+
qed

lemma book_ambient_split_left:
  assumes member: "s \<in> book_ambient_scale"
  shows "book_ambient_split \<tau> (Inl s) \<in> B \<tau> - \<Sigma> \<tau>"
  using book_ambient_split_spec(2)[of \<tau>] member unfolding Plus_def by blast

lemma book_ambient_split_right:
  assumes member: "s \<in> book_ambient_scale"
  shows "book_ambient_split \<tau> (Inr s) \<in> B \<tau> - \<Sigma> \<tau>"
  using book_ambient_split_spec(2)[of \<tau>] member unfolding Plus_def by blast

lemma book_ambient_split_sides:
  assumes sm: "s \<in> book_ambient_scale" and tm: "t \<in> book_ambient_scale"
  shows "book_ambient_split \<tau> (Inl s) \<noteq> book_ambient_split \<tau> (Inr t)"
proof
  assume equal: "book_ambient_split \<tau> (Inl s) = book_ambient_split \<tau> (Inr t)"
  have lm: "Inl s \<in> book_ambient_scale <+> book_ambient_scale"
    and rm: "Inr t \<in> book_ambient_scale <+> book_ambient_scale" using sm tm unfolding Plus_def by blast+
  have "Inl s = Inr t" by (rule inj_onD[OF book_ambient_split_spec(1) equal lm rm])
  then show False by simp
qed

subsection \<open>Witness names fit into the left half\<close>

lemma witness_names_le_scale:
  "card_of (book_henkin_full_signature \<Sigma> G \<tau>) \<le>o card_of book_ambient_scale"
  by (rule book_henkin_full_signature_cardinal_bound[OF scale_infinite names_le_scale])

definition book_ambient_witness_code :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_henkin_name \<Rightarrow> 'c + nat" where
  "book_ambient_witness_code G \<tau> = (SOME e. inj_on e (book_henkin_full_signature \<Sigma> G \<tau>) \<and>
    e ` book_henkin_full_signature \<Sigma> G \<tau> \<subseteq> book_ambient_scale)"

lemma book_ambient_witness_code_spec:
  "inj_on (book_ambient_witness_code G \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)"
  "book_ambient_witness_code G \<tau> ` book_henkin_full_signature \<Sigma> G \<tau> \<subseteq> book_ambient_scale"
proof -
  have exists: "\<exists>e. inj_on e (book_henkin_full_signature \<Sigma> G \<tau>) \<and>
    e ` book_henkin_full_signature \<Sigma> G \<tau> \<subseteq> book_ambient_scale"
    using witness_names_le_scale[of G \<tau>] unfolding card_of_ordLeq[symmetric] by blast
  have both: "inj_on (book_ambient_witness_code G \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>) \<and>
    book_ambient_witness_code G \<tau> ` book_henkin_full_signature \<Sigma> G \<tau> \<subseteq> book_ambient_scale"
    unfolding book_ambient_witness_code_def by (rule someI_ex[OF exists])
  show "inj_on (book_ambient_witness_code G \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)"
    and "book_ambient_witness_code G \<tau> ` book_henkin_full_signature \<Sigma> G \<tau> \<subseteq> book_ambient_scale"
    using both by blast+
qed

subsection \<open>The name map and the enlarged signature\<close>

definition book_ambient_name_map :: "sgcontext \<Rightarrow> otype \<Rightarrow> 'c book_henkin_name \<Rightarrow> 'c" where
  "book_ambient_name_map G \<tau> x =
    (if x \<in> BookOriginal ` \<Sigma> \<tau> then inv BookOriginal x
     else book_ambient_split \<tau> (Inl (book_ambient_witness_code G \<tau> x)))"

definition book_ambient_henkin_signature where
  "book_ambient_henkin_signature G = book_typed_image_signature (book_ambient_name_map G) (book_henkin_full_signature \<Sigma> G)"

lemma book_ambient_name_map_fixes:
  "c \<in> \<Sigma> \<tau> \<Longrightarrow> book_ambient_name_map G \<tau> (BookOriginal c) = c"
  by (simp add: book_ambient_name_map_def inv_f_f[OF book_henkin_original_injective])

lemma book_ambient_name_map_old:
  assumes old: "x \<in> BookOriginal ` \<Sigma> \<tau>"
  shows "book_ambient_name_map G \<tau> x \<in> \<Sigma> \<tau>"
proof -
  obtain c where member: "c \<in> \<Sigma> \<tau>" and shape: "x = BookOriginal c" using old by blast
  show ?thesis by (simp only: shape book_ambient_name_map_fixes[OF member]; rule member)
qed

lemma book_ambient_name_map_new:
  assumes fresh: "x \<notin> BookOriginal ` \<Sigma> \<tau>" and used: "x \<in> book_henkin_full_signature \<Sigma> G \<tau>"
  shows "book_ambient_name_map G \<tau> x \<in> B \<tau> - \<Sigma> \<tau>"
proof -
  have coded: "book_ambient_witness_code G \<tau> x \<in> book_ambient_scale"
    using book_ambient_witness_code_spec(2)[of G \<tau>] used by blast
  show ?thesis by (simp only: book_ambient_name_map_def fresh if_False; rule book_ambient_split_left[OF coded])
qed

lemma book_ambient_name_map_range:
  assumes used: "x \<in> book_henkin_full_signature \<Sigma> G \<tau>"
  shows "book_ambient_name_map G \<tau> x \<in> B \<tau>"
proof (cases "x \<in> BookOriginal ` \<Sigma> \<tau>")
  case True
  show ?thesis using book_ambient_name_map_old[OF True] ambient_included by blast
next
  case False
  show ?thesis using book_ambient_name_map_new[OF False used] by blast
qed

theorem book_ambient_name_map_injective:
  "inj_on (book_ambient_name_map G \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)"
proof (rule inj_onI)
  fix x y
  assume xm: "x \<in> book_henkin_full_signature \<Sigma> G \<tau>" and ym: "y \<in> book_henkin_full_signature \<Sigma> G \<tau>"
    and equal: "book_ambient_name_map G \<tau> x = book_ambient_name_map G \<tau> y"
  show "x = y"
  proof (cases "x \<in> BookOriginal ` \<Sigma> \<tau>")
    case True
    obtain c where cm: "c \<in> \<Sigma> \<tau>" and xs: "x = BookOriginal c" using True by blast
    show ?thesis
    proof (cases "y \<in> BookOriginal ` \<Sigma> \<tau>")
      case True
      obtain d where dm: "d \<in> \<Sigma> \<tau>" and ys: "y = BookOriginal d" using True by blast
      have "c = d" using equal by (simp only: xs ys book_ambient_name_map_fixes[OF cm] book_ambient_name_map_fixes[OF dm])
      then show ?thesis by (simp only: xs ys)
    next
      case False
      have new: "book_ambient_name_map G \<tau> y \<in> B \<tau> - \<Sigma> \<tau>" by (rule book_ambient_name_map_new[OF False ym])
      have old: "book_ambient_name_map G \<tau> x \<in> \<Sigma> \<tau>" by (rule book_ambient_name_map_old[OF True])
      show ?thesis using new old equal by auto
    qed
  next
    case False
    show ?thesis
    proof (cases "y \<in> BookOriginal ` \<Sigma> \<tau>")
      case True
      have new: "book_ambient_name_map G \<tau> x \<in> B \<tau> - \<Sigma> \<tau>" by (rule book_ambient_name_map_new[OF False xm])
      have old: "book_ambient_name_map G \<tau> y \<in> \<Sigma> \<tau>" by (rule book_ambient_name_map_old[OF True])
      show ?thesis using new old equal by auto
    next
      case False_y: False
      have cx: "book_ambient_witness_code G \<tau> x \<in> book_ambient_scale"
        and cy: "book_ambient_witness_code G \<tau> y \<in> book_ambient_scale"
        using book_ambient_witness_code_spec(2)[of G \<tau>] xm ym by blast+
      have lx: "Inl (book_ambient_witness_code G \<tau> x) \<in> book_ambient_scale <+> book_ambient_scale"
        and ly: "Inl (book_ambient_witness_code G \<tau> y) \<in> book_ambient_scale <+> book_ambient_scale"
        using cx cy unfolding Plus_def by blast+
      have splits: "book_ambient_split \<tau> (Inl (book_ambient_witness_code G \<tau> x)) =
        book_ambient_split \<tau> (Inl (book_ambient_witness_code G \<tau> y))"
        using equal by (simp only: book_ambient_name_map_def False False_y if_False)
      have codes: "book_ambient_witness_code G \<tau> x = book_ambient_witness_code G \<tau> y"
        using inj_onD[OF book_ambient_split_spec(1) splits lx ly] by simp
      show ?thesis by (rule inj_onD[OF book_ambient_witness_code_spec(1) codes xm ym])
    qed
  qed
qed

lemma book_ambient_henkin_signature_contains:
  "\<Sigma> \<tau> \<subseteq> book_ambient_henkin_signature G \<tau>"
proof
  fix c
  assume member: "c \<in> \<Sigma> \<tau>"
  have original: "BookOriginal c \<in> book_henkin_full_signature \<Sigma> G \<tau>"
    by (simp only: book_henkin_full_original_iff; rule member)
  have mapped: "book_ambient_name_map G \<tau> (BookOriginal c) \<in>
    book_typed_image_signature (book_ambient_name_map G) (book_henkin_full_signature \<Sigma> G) \<tau>"
    by (rule book_typed_image_maps; rule original)
  show "c \<in> book_ambient_henkin_signature G \<tau>"
    using mapped by (simp only: book_ambient_henkin_signature_def book_ambient_name_map_fixes[OF member])
qed

lemma book_ambient_henkin_signature_inside:
  "book_ambient_henkin_signature G \<tau> \<subseteq> B \<tau>"
  unfolding book_ambient_henkin_signature_def book_typed_image_signature_def
  using book_ambient_name_map_range by blast

lemma book_ambient_right_half_unused:
  assumes sm: "s \<in> book_ambient_scale"
  shows "book_ambient_split \<tau> (Inr s) \<in> B \<tau> - book_ambient_henkin_signature G \<tau>"
proof
  show "book_ambient_split \<tau> (Inr s) \<in> B \<tau>" using book_ambient_split_right[OF sm] by blast
next
  show "book_ambient_split \<tau> (Inr s) \<notin> book_ambient_henkin_signature G \<tau>"
  proof
    assume member: "book_ambient_split \<tau> (Inr s) \<in> book_ambient_henkin_signature G \<tau>"
    obtain x where xm: "x \<in> book_henkin_full_signature \<Sigma> G \<tau>"
      and equal: "book_ambient_split \<tau> (Inr s) = book_ambient_name_map G \<tau> x"
      using member unfolding book_ambient_henkin_signature_def book_typed_image_signature_def by blast
    show False
    proof (cases "x \<in> BookOriginal ` \<Sigma> \<tau>")
      case True
      have old: "book_ambient_name_map G \<tau> x \<in> \<Sigma> \<tau>" by (rule book_ambient_name_map_old[OF True])
      show False using book_ambient_split_right[OF sm, of \<tau>] old equal by auto
    next
      case False
      have coded: "book_ambient_witness_code G \<tau> x \<in> book_ambient_scale"
        using book_ambient_witness_code_spec(2)[of G \<tau>] xm by blast
      have sides: "book_ambient_split \<tau> (Inl (book_ambient_witness_code G \<tau> x)) \<noteq> book_ambient_split \<tau> (Inr s)"
        by (rule book_ambient_split_sides[OF coded sm])
      have equal': "book_ambient_split \<tau> (Inr s) = book_ambient_split \<tau> (Inl (book_ambient_witness_code G \<tau> x))"
        using equal by (simp only: book_ambient_name_map_def False if_False)
      show False by (rule notE[OF sides equal'[symmetric]])
    qed
  qed
qed

lemma book_ambient_right_half_le_reserve:
  "card_of book_ambient_scale \<le>o card_of (B \<tau> - book_ambient_henkin_signature G \<tau>)"
proof (rule card_of_ordLeqI[where f="\<lambda>s. book_ambient_split \<tau> (Inr s)"])
  show "inj_on (\<lambda>s. book_ambient_split \<tau> (Inr s)) book_ambient_scale"
  proof (rule inj_onI)
    fix s t
    assume sm: "s \<in> book_ambient_scale" and tm: "t \<in> book_ambient_scale"
      and equal: "book_ambient_split \<tau> (Inr s) = book_ambient_split \<tau> (Inr t)"
    have rs: "Inr s \<in> book_ambient_scale <+> book_ambient_scale"
      and rt: "Inr t \<in> book_ambient_scale <+> book_ambient_scale" using sm tm unfolding Plus_def by blast+
    have "Inr s = Inr t" using book_ambient_split_spec(1)[of \<tau>] equal rs rt unfolding inj_on_def by blast
    then show "s = t" by simp
  qed
next
  fix s assume "s \<in> book_ambient_scale"
  then show "book_ambient_split \<tau> (Inr s) \<in> B \<tau> - book_ambient_henkin_signature G \<tau>"
    by (rule book_ambient_right_half_unused)
qed

theorem book_ambient_henkin_signature_reserve:
  "infinite (B \<tau> - book_ambient_henkin_signature G \<tau>)"
proof
  assume finite: "finite (B \<tau> - book_ambient_henkin_signature G \<tau>)"
  have "finite book_ambient_scale" by (rule card_of_ordLeq_finite[OF book_ambient_right_half_le_reserve finite])
  then show False using scale_infinite by contradiction
qed

theorem book_ambient_henkin_signature_large:
  "card_of (\<Union>\<rho>. book_ambient_henkin_signature G \<rho>) \<le>o card_of (B \<tau> - book_ambient_henkin_signature G \<tau>)"
proof -
  have types: "card_of (UNIV :: otype set) \<le>o card_of book_ambient_scale"
    by (rule book_otypes_cardinal_bound[OF scale_infinite])
  have each: "\<forall>\<rho>\<in>(UNIV :: otype set). card_of (book_ambient_henkin_signature G \<rho>) \<le>o card_of book_ambient_scale"
  proof (intro ballI)
    fix \<rho> :: otype
    have image: "card_of (book_ambient_henkin_signature G \<rho>) \<le>o card_of (book_henkin_full_signature \<Sigma> G \<rho>)"
      unfolding book_ambient_henkin_signature_def book_typed_image_signature_def by (rule card_of_image)
    show "card_of (book_ambient_henkin_signature G \<rho>) \<le>o card_of book_ambient_scale"
      by (rule ordLeq_transitive[OF image witness_names_le_scale])
  qed
  have union: "card_of (\<Union>\<rho>\<in>(UNIV :: otype set). book_ambient_henkin_signature G \<rho>) \<le>o card_of book_ambient_scale"
    by (rule card_of_UNION_ordLeq_infinite[OF scale_infinite types each])
  show ?thesis by (rule ordLeq_transitive[OF union book_ambient_right_half_le_reserve])
qed

theorem book_ambient_henkin_signature_ambient:
  "book_ambient_signature (book_ambient_henkin_signature G) B"
  by (unfold_locales; rule book_ambient_henkin_signature_inside book_ambient_henkin_signature_reserve
    book_ambient_henkin_signature_large)

end

text \<open>
  Only Original(c) with c already declared is fixed. Every other used
  Henkin name goes into the left half of a two-sided injection of the
  scale (⋃Σ + ℕ) into the old reserve; the right half stays unused and
  is again at least as large as the enlarged signature. The chosen maps
  exist by the syntax cardinal bounds and the reserve assumptions; no
  enumeration and no countability of the carrier is used.
\<close>

end
