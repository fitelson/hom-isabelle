theory Bacon_Parametric_Henkin_Rank
  imports Bacon_Parametric_Henkin_Names Bacon_Parametric_Fresh_Witness_Elimination
begin

section \<open>Finite witness sets are ordered by structural dependence\<close>

text \<open>
  c ∈ names(A) ⇒ rank(c) < rank(cσ,A).  Thus a maximal-rank witness
  in a finite collection of witness axioms is fresh for the other axioms.
  Source role: Bacon, Proposition 15.4, p. 319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: rank is the size of the positive nested
  phenkin_full_name datatype.  The body is a proper nested part of its
  witness label.  Maximal rank is used for elimination, not introduction.
  No enumeration of names or formulas is involved.

  Status: consistency over a witness-free base in the expanded signature.
  For an embedded old theory, consistency in that expanded signature is
  an explicit premise, not silently inferred from old-signature consistency.
\<close>

lemma phenkin_body_name_size:
  fixes A :: "'c phenkin_full_name pterm"
  assumes "c \<in> phenkin_names A"
  shows "size c \<le> size_pterm size A"
  using assms
proof (induction A)
  case (PVar n)
  have False using PVar.prems by (simp only: phenkin_names.simps empty_iff)
  then show ?case by (rule FalseE)
next
  case (PConst d \<tau>)
  have eq: "c = d" using PConst.prems by (simp only: phenkin_names.simps singleton_iff)
  show ?case by (simp only: eq pterm.size; arith)
next
  case (PApp A B)
  have alternatives: "c \<in> phenkin_names A \<or> c \<in> phenkin_names B"
    using PApp.prems by (simp only: phenkin_names.simps Un_iff)
  have bound: "size c \<le> size_pterm size A + size_pterm size B"
  proof (rule disjE[OF alternatives])
    assume member: "c \<in> phenkin_names A"
    have "size c \<le> size_pterm size A" by (rule PApp.IH(1)[OF member])
    then show ?thesis by arith
  next
    assume member: "c \<in> phenkin_names B"
    have "size c \<le> size_pterm size B" by (rule PApp.IH(2)[OF member])
    then show ?thesis by arith
  qed
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PLam \<tau> A)
  have member: "c \<in> phenkin_names A" using PLam.prems by (simp only: phenkin_names.simps; simp)
  have bound: "size c \<le> size_pterm size A" by (rule PLam.IH[OF member])
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PEq \<tau> A B)
  have alternatives: "c \<in> phenkin_names A \<or> c \<in> phenkin_names B"
    using PEq.prems by (simp only: phenkin_names.simps Un_iff)
  have bound: "size c \<le> size_pterm size A + size_pterm size B"
  proof (rule disjE[OF alternatives])
    assume member: "c \<in> phenkin_names A"
    have "size c \<le> size_pterm size A" by (rule PEq.IH(1)[OF member])
    then show ?thesis by arith
  next
    assume member: "c \<in> phenkin_names B"
    have "size c \<le> size_pterm size B" by (rule PEq.IH(2)[OF member])
    then show ?thesis by arith
  qed
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PNeg A)
  have member: "c \<in> phenkin_names A" using PNeg.prems by (simp only: phenkin_names.simps; simp)
  have bound: "size c \<le> size_pterm size A" by (rule PNeg.IH[OF member])
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PConj A B)
  have alternatives: "c \<in> phenkin_names A \<or> c \<in> phenkin_names B"
    using PConj.prems by (simp only: phenkin_names.simps Un_iff)
  have bound: "size c \<le> size_pterm size A + size_pterm size B"
  proof (rule disjE[OF alternatives])
    assume member: "c \<in> phenkin_names A"
    have "size c \<le> size_pterm size A" by (rule PConj.IH(1)[OF member])
    then show ?thesis by arith
  next
    assume member: "c \<in> phenkin_names B"
    have "size c \<le> size_pterm size B" by (rule PConj.IH(2)[OF member])
    then show ?thesis by arith
  qed
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PDisj A B)
  have alternatives: "c \<in> phenkin_names A \<or> c \<in> phenkin_names B"
    using PDisj.prems by (simp only: phenkin_names.simps Un_iff)
  have bound: "size c \<le> size_pterm size A + size_pterm size B"
  proof (rule disjE[OF alternatives])
    assume member: "c \<in> phenkin_names A"
    have "size c \<le> size_pterm size A" by (rule PDisj.IH(1)[OF member])
    then show ?thesis by arith
  next
    assume member: "c \<in> phenkin_names B"
    have "size c \<le> size_pterm size B" by (rule PDisj.IH(2)[OF member])
    then show ?thesis by arith
  qed
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PImp A B)
  have alternatives: "c \<in> phenkin_names A \<or> c \<in> phenkin_names B"
    using PImp.prems by (simp only: phenkin_names.simps Un_iff)
  have bound: "size c \<le> size_pterm size A + size_pterm size B"
  proof (rule disjE[OF alternatives])
    assume member: "c \<in> phenkin_names A"
    have "size c \<le> size_pterm size A" by (rule PImp.IH(1)[OF member])
    then show ?thesis by arith
  next
    assume member: "c \<in> phenkin_names B"
    have "size c \<le> size_pterm size B" by (rule PImp.IH(2)[OF member])
    then show ?thesis by arith
  qed
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PForall \<tau> A)
  have member: "c \<in> phenkin_names A" using PForall.prems by (simp only: phenkin_names.simps; simp)
  have bound: "size c \<le> size_pterm size A" by (rule PForall.IH[OF member])
  show ?case using bound by (simp only: pterm.size; arith)
next
  case (PExists \<tau> A)
  have member: "c \<in> phenkin_names A" using PExists.prems by (simp only: phenkin_names.simps; simp)
  have bound: "size c \<le> size_pterm size A" by (rule PExists.IH[OF member])
  show ?case using bound by (simp only: pterm.size; arith)
qed

lemma phenkin_witness_rank:
  assumes "c \<in> phenkin_names A"
  shows "size c < size (PFWitness \<sigma> A)"
  using phenkin_body_name_size[OF assms]
  by (simp add: phenkin_full_name.size)

lemma phenkin_witness_fresh_body:
  "PFWitness \<sigma> A \<notin> phenkin_names A"
proof
  assume "PFWitness \<sigma> A \<in> phenkin_names A"
  then have "size (PFWitness \<sigma> A) < size (PFWitness \<sigma> A)"
    by (rule phenkin_witness_rank)
  then show False by simp
qed

lemma phenkin_fresh_lift:
  assumes "\<And>n. c \<notin> phenkin_names (s n)"
  shows "c \<notin> phenkin_names (plift_subst s n)"
proof (cases n)
  case 0
  show ?thesis by (simp add: 0)
next
  case (Suc m)
  show ?thesis using assms[of m] by (simp only: Suc plift_subst.simps phenkin_names_prename; simp)
qed

lemma phenkin_not_disj:
  "\<not> (P \<or> Q) \<longleftrightarrow> \<not> P \<and> \<not> Q"
proof
  assume neither: "\<not> (P \<or> Q)"
  show "\<not> P \<and> \<not> Q"
  proof (rule conjI)
    show "\<not> P"
    proof
      assume p: "P"
      have disj: "P \<or> Q" by (rule disjI1[OF p])
      show False by (rule notE[OF neither disj])
    qed
    show "\<not> Q"
    proof
      assume q: "Q"
      have disj: "P \<or> Q" by (rule disjI2[OF q])
      show False by (rule notE[OF neither disj])
    qed
  qed
next
  assume pair: "\<not> P \<and> \<not> Q"
  show "\<not> (P \<or> Q)"
  proof
    assume disj: "P \<or> Q"
    show False
    proof (rule disjE[OF disj])
      assume p: "P"
      show False by (rule notE[OF conjunct1[OF pair] p])
    next
      assume q: "Q"
      show False by (rule notE[OF conjunct2[OF pair] q])
    qed
  qed
qed

lemma phenkin_fresh_subst:
  assumes "c \<notin> phenkin_names A" and "\<And>n. c \<notin> phenkin_names (s n)"
  shows "c \<notin> phenkin_names (psubst s A)"
  using assms
proof (induction A arbitrary: s)
  case (PVar n)
  show ?case by (simp only: psubst.simps; rule PVar.prems(2))
next
  case (PConst d \<sigma>)
  show ?case using PConst.prems(1) by (simp only: psubst.simps; simp)
next
  case (PApp A B)
  have parts: "c \<notin> phenkin_names A \<and> c \<notin> phenkin_names B"
    using PApp.prems(1) by (simp only: phenkin_names.simps Un_iff phenkin_not_disj; simp)
  have left: "c \<notin> phenkin_names (psubst s A)"
    by (rule PApp.IH(1)[OF conjunct1[OF parts] PApp.prems(2)])
  have right: "c \<notin> phenkin_names (psubst s B)"
    by (rule PApp.IH(2)[OF conjunct2[OF parts] PApp.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps Un_iff phenkin_not_disj left right; simp)
next
  case (PLam \<sigma> A)
  have body: "c \<notin> phenkin_names A" using PLam.prems(1) by (simp only: phenkin_names.simps; simp)
  have lifted: "\<And>n. c \<notin> phenkin_names (plift_subst s n)"
    by (rule phenkin_fresh_lift[OF PLam.prems(2)])
  have result: "c \<notin> phenkin_names (psubst (plift_subst s) A)"
    by (rule PLam.IH[OF body lifted])
  show ?case by (simp only: psubst.simps phenkin_names.simps result; simp)
next
  case (PEq \<sigma> A B)
  have parts: "c \<notin> phenkin_names A \<and> c \<notin> phenkin_names B"
    using PEq.prems(1) by (simp only: phenkin_names.simps Un_iff phenkin_not_disj; simp)
  have left: "c \<notin> phenkin_names (psubst s A)"
    by (rule PEq.IH(1)[OF conjunct1[OF parts] PEq.prems(2)])
  have right: "c \<notin> phenkin_names (psubst s B)"
    by (rule PEq.IH(2)[OF conjunct2[OF parts] PEq.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps Un_iff phenkin_not_disj left right; simp)
next
  case (PNeg A)
  have body: "c \<notin> phenkin_names A" using PNeg.prems(1) by (simp only: phenkin_names.simps; simp)
  have result: "c \<notin> phenkin_names (psubst s A)" by (rule PNeg.IH[OF body PNeg.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps result; simp)
next
  case (PConj A B)
  have parts: "c \<notin> phenkin_names A \<and> c \<notin> phenkin_names B"
    using PConj.prems(1) by (simp only: phenkin_names.simps Un_iff phenkin_not_disj; simp)
  have left: "c \<notin> phenkin_names (psubst s A)"
    by (rule PConj.IH(1)[OF conjunct1[OF parts] PConj.prems(2)])
  have right: "c \<notin> phenkin_names (psubst s B)"
    by (rule PConj.IH(2)[OF conjunct2[OF parts] PConj.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps Un_iff phenkin_not_disj left right; simp)
next
  case (PDisj A B)
  have parts: "c \<notin> phenkin_names A \<and> c \<notin> phenkin_names B"
    using PDisj.prems(1) by (simp only: phenkin_names.simps Un_iff phenkin_not_disj; simp)
  have left: "c \<notin> phenkin_names (psubst s A)"
    by (rule PDisj.IH(1)[OF conjunct1[OF parts] PDisj.prems(2)])
  have right: "c \<notin> phenkin_names (psubst s B)"
    by (rule PDisj.IH(2)[OF conjunct2[OF parts] PDisj.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps Un_iff phenkin_not_disj left right; simp)
next
  case (PImp A B)
  have parts: "c \<notin> phenkin_names A \<and> c \<notin> phenkin_names B"
    using PImp.prems(1) by (simp only: phenkin_names.simps Un_iff phenkin_not_disj; simp)
  have left: "c \<notin> phenkin_names (psubst s A)"
    by (rule PImp.IH(1)[OF conjunct1[OF parts] PImp.prems(2)])
  have right: "c \<notin> phenkin_names (psubst s B)"
    by (rule PImp.IH(2)[OF conjunct2[OF parts] PImp.prems(2)])
  show ?case by (simp only: psubst.simps phenkin_names.simps Un_iff phenkin_not_disj left right; simp)
next
  case (PForall \<sigma> A)
  have body: "c \<notin> phenkin_names A" using PForall.prems(1) by (simp only: phenkin_names.simps; simp)
  have lifted: "\<And>n. c \<notin> phenkin_names (plift_subst s n)"
    by (rule phenkin_fresh_lift[OF PForall.prems(2)])
  have result: "c \<notin> phenkin_names (psubst (plift_subst s) A)"
    by (rule PForall.IH[OF body lifted])
  show ?case by (simp only: psubst.simps phenkin_names.simps result; simp)
next
  case (PExists \<sigma> A)
  have body: "c \<notin> phenkin_names A" using PExists.prems(1) by (simp only: phenkin_names.simps; simp)
  have lifted: "\<And>n. c \<notin> phenkin_names (plift_subst s n)"
    by (rule phenkin_fresh_lift[OF PExists.prems(2)])
  have result: "c \<notin> phenkin_names (psubst (plift_subst s) A)"
    by (rule PExists.IH[OF body lifted])
  show ?case by (simp only: psubst.simps phenkin_names.simps result; simp)
qed

lemma phenkin_fresh_full_axiom:
  assumes body: "c \<notin> phenkin_names A" and distinct: "c \<noteq> PFWitness \<sigma> A"
  shows "c \<notin> phenkin_names (phenkin_full_witness_axiom \<sigma> A)"
proof -
  have fresh_instance: "c \<notin> phenkin_names (psubst0 (phenkin_full_witness \<sigma> A) A)"
    unfolding psubst0_def
    by (rule phenkin_fresh_subst[OF body])
      (case_tac n; simp add: phenkin_full_witness_def distinct)
  show ?thesis using body fresh_instance
    by (simp only: phenkin_full_witness_axiom_def phenkin_names.simps Un_iff phenkin_not_disj; simp)
qed

definition phenkin_witness_indices ::
    "'c psignature \<Rightarrow> (otype \<times> 'c phenkin_full_name pterm) set" where
  "phenkin_witness_indices \<Sigma> =
    {i. has_ptype [fst i] (snd i) Prop \<and>
      pterm_in_signature (phenkin_full_signature \<Sigma>) (snd i)}"

definition phenkin_index_name :: "otype \<times> 'c phenkin_full_name pterm \<Rightarrow> 'c phenkin_full_name" where
  "phenkin_index_name i = PFWitness (fst i) (snd i)"

definition phenkin_index_axiom ::
    "otype \<times> 'c phenkin_full_name pterm \<Rightarrow> 'c phenkin_full_name pterm" where
  "phenkin_index_axiom i = phenkin_full_witness_axiom (fst i) (snd i)"

definition phenkin_all_witness_axioms ::
    "'c psignature \<Rightarrow> 'c phenkin_full_name pterm set" where
  "phenkin_all_witness_axioms \<Sigma> = image phenkin_index_axiom (phenkin_witness_indices \<Sigma>)"

lemma phenkin_index_name_injective:
  "phenkin_index_name i = phenkin_index_name j \<Longrightarrow> i = j"
  by (cases i; cases j) (simp add: phenkin_index_name_def)

lemma phenkin_max_rank_fresh:
  assumes rank: "size (phenkin_index_name j) \<le> size (phenkin_index_name i)" and different: "i \<noteq> j"
  shows "phenkin_index_name i \<notin> phenkin_names (phenkin_index_axiom j)"
proof -
  have fresh_body: "phenkin_index_name i \<notin> phenkin_names (snd j)"
  proof
    assume member: "phenkin_index_name i \<in> phenkin_names (snd j)"
    have less: "size (phenkin_index_name i) < size (PFWitness (fst j) (snd j))"
      by (rule phenkin_witness_rank[OF member])
    show False using less rank unfolding phenkin_index_name_def by arith
  qed
  have distinct: "phenkin_index_name i \<noteq> PFWitness (fst j) (snd j)"
  proof
    assume eq: "phenkin_index_name i = PFWitness (fst j) (snd j)"
    have names_eq: "phenkin_index_name i = phenkin_index_name j"
      using eq by (simp only: phenkin_index_name_def)
    have indices_eq: "i = j" by (rule phenkin_index_name_injective[OF names_eq])
    show False by (rule notE[OF different indices_eq])
  qed
  show ?thesis unfolding phenkin_index_axiom_def
    by (rule phenkin_fresh_full_axiom[OF fresh_body distinct])
qed


end
