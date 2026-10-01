theory Classicism_2_11_Syntax
  imports "Classicism_2_11.Typed_Paper_Model"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Universal_Closure_Syntax"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Box_Syntax"
begin

section \<open>Object-language formulas of Proposition 2.11\<close>

text \<open>
  Source: Bacon and Dorr, Classicism, 1 July 2022 draft. Figure 1, p.6
  (lifted ¬, ∧, ∨; □; ≤); Boolean Completeness, GLB and LB, pp.23–24;
  Atomicity and Atom, p.24; BF, p.20; Rigid and Rigid Comprehension,
  pp.27–28; Proposition 2.11, p.30.

  LB is the intended lower-bound clause ∀y(Xy → z ≤ y). The printed
  clause ∀y(Xy → y ≤ z) is kept separately as c211_LB_printed; with it,
  Boolean Completeness contradicts Booleanism (see the technical note).
  Every refutation endpoint below therefore concerns the corrected LB.

  All terms use the standard rich stock. Operators are closed λ-terms,
  applied by NApp, so no substitution or capture-avoidance is needed to
  form a formula. Within each defining body, binders that need
  independent access have distinct stock indices; closed operator
  subterms may reuse names, which is harmless because an argument of
  NApp lies outside the operator's binding scope. The ≠, ∀z⃗ and Yz⃗ notations are the usual
  abbreviations: ¬(=), iterated literal ∀, iterated application.
\<close>

abbreviation c211_G :: sgcontext where "c211_G \<equiv> sg_standard_stock"

definition c211_v :: "otype \<Rightarrow> nat \<Rightarrow> nat" where
  "c211_v \<sigma> k = sg_stock_index \<sigma> k"

lemma c211_v_type [simp]: "c211_G (c211_v \<sigma> k) = \<sigma>"
  by (simp only: c211_v_def sg_standard_stock_index)

lemma c211_v_eq_iff [simp]: "c211_v \<sigma> k = c211_v \<rho> m \<longleftrightarrow> \<sigma> = \<rho> \<and> k = m"
proof
  assume eq: "c211_v \<sigma> k = c211_v \<rho> m"
  have "\<sigma> = \<rho>" using arg_cong[OF eq, of c211_G] by simp
  moreover have "k = m"
    using eq unfolding c211_v_def sg_stock_index_def by simp
  ultimately show "\<sigma> = \<rho> \<and> k = m" by simp
qed simp

lemma c211_rich: "paper_R_rich c211_G"
  by (rule paper_R_rich_from_F[OF sg_standard_stock_rich])

subsection \<open>Figure 1: lifted Boolean operators and ≤\<close>

primrec c211_not :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_not Ind = NLogical SNot"
| "c211_not Prop = NLogical SNot"
| "c211_not (Arr \<sigma> \<rho>) = NLam (c211_v (Arr \<sigma> \<rho>) 0) (NLam (c211_v \<sigma> 2)
    (NApp (c211_not \<rho>) (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2)))))"

primrec c211_and :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_and Ind = NLogical SAnd"
| "c211_and Prop = NLogical SAnd"
| "c211_and (Arr \<sigma> \<rho>) = NLam (c211_v (Arr \<sigma> \<rho>) 0) (NLam (c211_v (Arr \<sigma> \<rho>) 1)
    (NLam (c211_v \<sigma> 2) (NApp (NApp (c211_and \<rho>)
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))))
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 1)) (NVar (c211_v \<sigma> 2))))))"

primrec c211_or :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_or Ind = NLogical SOr"
| "c211_or Prop = NLogical SOr"
| "c211_or (Arr \<sigma> \<rho>) = NLam (c211_v (Arr \<sigma> \<rho>) 0) (NLam (c211_v (Arr \<sigma> \<rho>) 1)
    (NLam (c211_v \<sigma> 2) (NApp (NApp (c211_or \<rho>)
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))))
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 1)) (NVar (c211_v \<sigma> 2))))))"

text \<open>≤τ := λX Y. Y =τ X ∨τ Y (Figure 1).\<close>

definition c211_leq :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_leq \<tau> = NLam (c211_v \<tau> 3) (NLam (c211_v \<tau> 4)
    (named_paper_eq \<tau> (NVar (c211_v \<tau> 4))
      (NApp (NApp (c211_or \<tau>) (NVar (c211_v \<tau> 3))) (NVar (c211_v \<tau> 4)))))"

definition c211_le :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_le \<tau> A B = NApp (NApp (c211_leq \<tau>) A) B"

definition c211_neg :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_neg \<tau> A = NApp (c211_not \<tau>) A"

definition c211_neq :: "otype \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_neq \<tau> A B = named_paper_not (named_paper_eq \<tau> A B)"

abbreviation c211_box :: "'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_box P \<equiv> paper_R_named_box c211_G P"

abbreviation c211_imp :: "'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_imp A B \<equiv> named_paper_imp c211_G A B"

abbreviation c211_iff :: "'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_iff A B \<equiv> named_paper_iff c211_G A B"

subsection \<open>Atomicity, p.24\<close>

text \<open>Atomτ := λy.∀z((z ≤τ y ∧ z ≠ y) ↔ z ≤τ ¬τ z).\<close>

definition c211_atom :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_atom \<tau> = NLam (c211_v \<tau> 5) (named_paper_all \<tau> (NLam (c211_v \<tau> 6)
    (c211_iff
      (named_paper_and (c211_le \<tau> (NVar (c211_v \<tau> 6)) (NVar (c211_v \<tau> 5)))
        (c211_neq \<tau> (NVar (c211_v \<tau> 6)) (NVar (c211_v \<tau> 5))))
      (c211_le \<tau> (NVar (c211_v \<tau> 6)) (c211_neg \<tau> (NVar (c211_v \<tau> 6)))))))"

text \<open>Atomicity: ∀x(x ≤ ¬τ x ∨ ∃y(Atomτ y ∧ y ≤τ x)).\<close>

definition c211_atomicity :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_atomicity \<tau> = named_paper_all \<tau> (NLam (c211_v \<tau> 7)
    (named_paper_or (c211_le \<tau> (NVar (c211_v \<tau> 7)) (c211_neg \<tau> (NVar (c211_v \<tau> 7))))
      (named_paper_ex \<tau> (NLam (c211_v \<tau> 8)
        (named_paper_and (NApp (c211_atom \<tau>) (NVar (c211_v \<tau> 8)))
          (c211_le \<tau> (NVar (c211_v \<tau> 8)) (NVar (c211_v \<tau> 7))))))))"

text \<open>□Atomicity: the necessitation of the (already closed) sentence.\<close>

definition c211_box_atomicity :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_box_atomicity \<tau> = c211_box (c211_atomicity \<tau>)"

subsection \<open>Boolean Completeness, pp.23–24\<close>

text \<open>LBτ := λz X.∀y(Xy → z ≤τ y), the intended clause.\<close>

definition c211_LB :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_LB \<tau> = NLam (c211_v \<tau> 9) (NLam (c211_v (Arr \<tau> Prop) 0)
    (named_paper_all \<tau> (NLam (c211_v \<tau> 10)
      (c211_imp (NApp (NVar (c211_v (Arr \<tau> Prop) 0)) (NVar (c211_v \<tau> 10)))
        (c211_le \<tau> (NVar (c211_v \<tau> 9)) (NVar (c211_v \<tau> 10)))))))"

text \<open>The clause as printed on p.24 (inequality reversed); not used below.\<close>

definition c211_LB_printed :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_LB_printed \<tau> = NLam (c211_v \<tau> 9) (NLam (c211_v (Arr \<tau> Prop) 0)
    (named_paper_all \<tau> (NLam (c211_v \<tau> 10)
      (c211_imp (NApp (NVar (c211_v (Arr \<tau> Prop) 0)) (NVar (c211_v \<tau> 10)))
        (c211_le \<tau> (NVar (c211_v \<tau> 10)) (NVar (c211_v \<tau> 9)))))))"

text \<open>GLBτ := λy X.∀z(LBτ z X ↔ z ≤τ y).\<close>

definition c211_GLB :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_GLB \<tau> = NLam (c211_v \<tau> 11) (NLam (c211_v (Arr \<tau> Prop) 1)
    (named_paper_all \<tau> (NLam (c211_v \<tau> 12)
      (c211_iff
        (NApp (NApp (c211_LB \<tau>) (NVar (c211_v \<tau> 12))) (NVar (c211_v (Arr \<tau> Prop) 1)))
        (c211_le \<tau> (NVar (c211_v \<tau> 12)) (NVar (c211_v \<tau> 11)))))))"

text \<open>Boolean Completeness: ∀X^{τ→t} ∃y^τ GLBτ y X.\<close>

definition c211_BC :: "otype \<Rightarrow> 'c paper_named_term" where
  "c211_BC \<tau> = named_paper_all (Arr \<tau> Prop) (NLam (c211_v (Arr \<tau> Prop) 2)
    (named_paper_ex \<tau> (NLam (c211_v \<tau> 13)
      (NApp (NApp (c211_GLB \<tau>) (NVar (c211_v \<tau> 13))) (NVar (c211_v (Arr \<tau> Prop) 2))))))"

subsection \<open>BF, p.20\<close>

text \<open>BF: ∀x□P → □∀xP, for every R type σ, binder x:σ and formula P.\<close>

definition c211_BF :: "otype \<Rightarrow> nat \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "c211_BF \<sigma> n P = c211_imp (named_paper_all \<sigma> (NLam n (c211_box P)))
    (c211_box (named_paper_all \<sigma> (NLam n P)))"

subsection \<open>Rigid and Rigid Comprehension, pp.27–28\<close>

text \<open>
  For σs = [σ1,…,σk], τ = σ1→…→σk→t and z⃗ = z1…zk:
  Rigid := λY.□∀X((∀z⃗(Yz⃗ → □Xz⃗)) ↔ Y ≤τ X);
  Rigid Comprehension: ∀X∃Y(Rigid Y ∧ ∀z⃗(Xz⃗ ↔ Yz⃗)).
\<close>

primrec c211_zs_from :: "nat \<Rightarrow> otype list \<Rightarrow> nat list" where
  "c211_zs_from k [] = []"
| "c211_zs_from k (\<sigma> # \<sigma>s) = c211_v \<sigma> (20 + k) # c211_zs_from (Suc k) \<sigma>s"

definition c211_zs :: "otype list \<Rightarrow> nat list" where
  "c211_zs \<sigma>s = c211_zs_from 0 \<sigma>s"

definition c211_rtype :: "otype list \<Rightarrow> otype" where
  "c211_rtype \<sigma>s = paper_type_vector \<sigma>s Prop"

definition c211_vapp :: "nat \<Rightarrow> nat list \<Rightarrow> 'c paper_named_term" where
  "c211_vapp f zs = named_app_vec (NVar f) (map NVar zs)"

definition c211_rigid :: "otype list \<Rightarrow> 'c paper_named_term" where
  "c211_rigid \<sigma>s = NLam (c211_v (c211_rtype \<sigma>s) 14)
    (c211_box (named_paper_all (c211_rtype \<sigma>s) (NLam (c211_v (c211_rtype \<sigma>s) 15)
      (c211_iff
        (paper_R_all_vec c211_G (c211_zs \<sigma>s)
          (c211_imp (c211_vapp (c211_v (c211_rtype \<sigma>s) 14) (c211_zs \<sigma>s))
            (c211_box (c211_vapp (c211_v (c211_rtype \<sigma>s) 15) (c211_zs \<sigma>s)))))
        (c211_le (c211_rtype \<sigma>s) (NVar (c211_v (c211_rtype \<sigma>s) 14))
          (NVar (c211_v (c211_rtype \<sigma>s) 15)))))))"

definition c211_RC :: "otype list \<Rightarrow> 'c paper_named_term" where
  "c211_RC \<sigma>s = named_paper_all (c211_rtype \<sigma>s) (NLam (c211_v (c211_rtype \<sigma>s) 16)
    (named_paper_ex (c211_rtype \<sigma>s) (NLam (c211_v (c211_rtype \<sigma>s) 17)
      (named_paper_and (NApp (c211_rigid \<sigma>s) (NVar (c211_v (c211_rtype \<sigma>s) 17)))
        (paper_R_all_vec c211_G (c211_zs \<sigma>s)
          (c211_iff (c211_vapp (c211_v (c211_rtype \<sigma>s) 16) (c211_zs \<sigma>s))
            (c211_vapp (c211_v (c211_rtype \<sigma>s) 17) (c211_zs \<sigma>s))))))))"

subsection \<open>Language membership\<close>

lemma c211_lang_Var:
  "paper_R_type \<sigma> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (NVar (c211_v \<sigma> k)) \<sigma>"
  by (rule paper_R_language_Var) simp_all

lemma c211_lang_Lam:
  assumes body: "paper_R_in_language \<Sigma> c211_G A \<tau>" and rt: "paper_R_type \<sigma>"
    and ni: "\<tau> \<noteq> Ind"
  shows "paper_R_in_language \<Sigma> c211_G (NLam (c211_v \<sigma> k) A) (Arr \<sigma> \<tau>)"
proof -
  have typed: "paper_R_has_type c211_G A \<tau>" and sig: "named_in_signature \<Sigma> A"
    using body unfolding paper_R_in_language_def by simp_all
  have "paper_R_has_type c211_G (NLam (c211_v \<sigma> k) A) (Arr (c211_G (c211_v \<sigma> k)) \<tau>)"
    by (rule paper_R_has_type.Lam[OF typed _ ni]) (simp add: rt)
  then show ?thesis using sig by (simp add: paper_R_in_language_def)
qed

lemma c211_lang_Logical:
  "paper_R_type (paper_logical_type l) \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G (NLogical l) (paper_logical_type l)"
  unfolding paper_R_in_language_def by (auto intro: paper_R_has_type.Logical)

lemma c211_relational_Arr:
  assumes "paper_R_relational (Arr \<sigma> \<rho>)"
  shows "paper_R_type \<sigma>" "paper_R_relational \<rho>" "paper_R_type \<rho>" "\<rho> \<noteq> Ind"
  using assms by (simp_all add: paper_R_relational_def)

lemma c211_relational_type: "paper_R_relational \<tau> \<Longrightarrow> paper_R_type \<tau>"
  and c211_relational_not_Ind: "paper_R_relational \<tau> \<Longrightarrow> \<tau> \<noteq> Ind"
  by (simp_all add: paper_R_relational_def)

lemma c211_not_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_not \<tau>) (Arr \<tau> \<tau>)"
proof (induction \<tau>)
  case Ind then show ?case by (simp add: paper_R_relational_def)
next
  case Prop
  show ?case using c211_lang_Logical[of SNot \<Sigma>] by simp
next
  case (Arr \<sigma> \<rho>)
  note facts = c211_relational_Arr[OF Arr.prems]
  have head: "paper_R_in_language \<Sigma> c211_G (c211_not \<rho>) (Arr \<rho> \<rho>)"
    by (rule Arr.IH(2)[OF facts(2)])
  have xz: "paper_R_in_language \<Sigma> c211_G
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))) \<rho>"
    by (rule paper_R_language_App[OF c211_lang_Var c211_lang_Var])
      (use facts in \<open>simp_all\<close>)
  have body: "paper_R_in_language \<Sigma> c211_G (NApp (c211_not \<rho>)
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2)))) \<rho>"
    by (rule paper_R_language_App[OF head xz])
  show ?case unfolding c211_not.simps
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF body facts(1) facts(4)]])
      (use Arr.prems in \<open>simp_all add: paper_R_relational_def\<close>)
qed

lemma c211_binop_language:
  assumes rt: "paper_R_relational (Arr \<sigma> \<rho>)"
    and head: "paper_R_in_language \<Sigma> c211_G H (Arr \<rho> (Arr \<rho> \<rho>))"
  shows "paper_R_in_language \<Sigma> c211_G
    (NLam (c211_v (Arr \<sigma> \<rho>) 0) (NLam (c211_v (Arr \<sigma> \<rho>) 1)
      (NLam (c211_v \<sigma> 2) (NApp (NApp H
        (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))))
        (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 1)) (NVar (c211_v \<sigma> 2)))))))
    (Arr (Arr \<sigma> \<rho>) (Arr (Arr \<sigma> \<rho>) (Arr \<sigma> \<rho>)))"
proof -
  note facts = c211_relational_Arr[OF rt]
  have ft: "paper_R_type (Arr \<sigma> \<rho>)" using rt by (simp add: paper_R_relational_def)
  have x: "paper_R_in_language \<Sigma> c211_G
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))) \<rho>"
    by (rule paper_R_language_App[OF c211_lang_Var[OF ft] c211_lang_Var[OF facts(1)]])
  have y: "paper_R_in_language \<Sigma> c211_G
      (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 1)) (NVar (c211_v \<sigma> 2))) \<rho>"
    by (rule paper_R_language_App[OF c211_lang_Var[OF ft] c211_lang_Var[OF facts(1)]])
  have body: "paper_R_in_language \<Sigma> c211_G (NApp (NApp H
        (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 0)) (NVar (c211_v \<sigma> 2))))
        (NApp (NVar (c211_v (Arr \<sigma> \<rho>) 1)) (NVar (c211_v \<sigma> 2)))) \<rho>"
    by (rule paper_R_language_App[OF paper_R_language_App[OF head x] y])
  show ?thesis
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF c211_lang_Lam[OF body facts(1) facts(4)] ft] ft])
      simp_all
qed

lemma c211_and_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_and \<tau>) (Arr \<tau> (Arr \<tau> \<tau>))"
proof (induction \<tau>)
  case Ind then show ?case by (simp add: paper_R_relational_def)
next
  case Prop show ?case using c211_lang_Logical[of SAnd \<Sigma>] by simp
next
  case (Arr \<sigma> \<rho>)
  show ?case unfolding c211_and.simps
    by (rule c211_binop_language[OF Arr.prems Arr.IH(2)[OF c211_relational_Arr(2)[OF Arr.prems]]])
qed

lemma c211_or_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_or \<tau>) (Arr \<tau> (Arr \<tau> \<tau>))"
proof (induction \<tau>)
  case Ind then show ?case by (simp add: paper_R_relational_def)
next
  case Prop show ?case using c211_lang_Logical[of SOr \<Sigma>] by simp
next
  case (Arr \<sigma> \<rho>)
  show ?case unfolding c211_or.simps
    by (rule c211_binop_language[OF Arr.prems Arr.IH(2)[OF c211_relational_Arr(2)[OF Arr.prems]]])
qed

lemma c211_eq_language:
  assumes "paper_R_type \<tau>" "paper_R_in_language \<Sigma> c211_G A \<tau>" "paper_R_in_language \<Sigma> c211_G B \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (named_paper_eq \<tau> A B) Prop"
proof -
  have "paper_R_in_language \<Sigma> c211_G (NLogical (SEq \<tau>)) (Arr \<tau> (Arr \<tau> Prop))"
    using c211_lang_Logical[of "SEq \<tau>" \<Sigma>] assms(1) by simp
  then show ?thesis unfolding named_paper_eq_def
    by (rule paper_R_language_App[OF paper_R_language_App[OF _ assms(2)] assms(3)])
qed

lemma c211_leq_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_leq \<tau>) (Arr \<tau> (Arr \<tau> Prop))"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  have body: "paper_R_in_language \<Sigma> c211_G (named_paper_eq \<tau> (NVar (c211_v \<tau> 4))
      (NApp (NApp (c211_or \<tau>) (NVar (c211_v \<tau> 3))) (NVar (c211_v \<tau> 4)))) Prop"
    by (rule c211_eq_language[OF tt c211_lang_Var[OF tt]
      paper_R_language_App[OF paper_R_language_App[OF c211_or_language[OF rt]
        c211_lang_Var[OF tt]] c211_lang_Var[OF tt]]])
  show ?thesis unfolding c211_leq_def
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF body tt] tt]) simp_all
qed

lemma c211_le_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A \<tau> \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G B \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_le \<tau> A B) Prop"
  unfolding c211_le_def
  by (rule paper_R_language_App[OF paper_R_language_App[OF c211_leq_language]])

lemma c211_neg_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A \<tau> \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G (c211_neg \<tau> A) \<tau>"
  unfolding c211_neg_def by (rule paper_R_language_App[OF c211_not_language])

lemma c211_neq_language:
  "paper_R_type \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A \<tau> \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G B \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_neq \<tau> A B) Prop"
  unfolding c211_neq_def by (rule paper_R_named_not_language[OF c211_eq_language])

lemma c211_all_language:
  "paper_R_type \<sigma> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G (named_paper_all \<sigma> (NLam (c211_v \<sigma> k) A)) Prop"
  by (rule paper_R_named_all_language[OF c211_lang_Lam]) simp_all

lemma c211_ex_language:
  "paper_R_type \<sigma> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G (named_paper_ex \<sigma> (NLam (c211_v \<sigma> k) A)) Prop"
  by (rule paper_R_named_ex_language[OF c211_lang_Lam]) simp_all

lemmas c211_connective_language =
  paper_R_named_and_language paper_R_named_or_language
  paper_R_named_paper_imp_language[OF c211_rich] paper_R_named_paper_iff_language[OF c211_rich]
  paper_R_named_box_language[OF c211_rich]

lemma c211_atom_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_atom \<tau>) (Arr \<tau> Prop)"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  note v = c211_lang_Var[OF tt]
  have body: "paper_R_in_language \<Sigma> c211_G (c211_iff
      (named_paper_and (c211_le \<tau> (NVar (c211_v \<tau> 6)) (NVar (c211_v \<tau> 5)))
        (c211_neq \<tau> (NVar (c211_v \<tau> 6)) (NVar (c211_v \<tau> 5))))
      (c211_le \<tau> (NVar (c211_v \<tau> 6)) (c211_neg \<tau> (NVar (c211_v \<tau> 6))))) Prop"
    by (intro c211_connective_language c211_le_language[OF rt] c211_neq_language[OF tt]
        c211_neg_language[OF rt] v)
  show ?thesis unfolding c211_atom_def
    by (rule c211_lang_Lam[OF c211_all_language[OF tt body] tt]) simp
qed

lemma c211_atomicity_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_atomicity \<tau>) Prop"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  note v = c211_lang_Var[OF tt]
  show ?thesis unfolding c211_atomicity_def
    by (intro c211_all_language[OF tt] c211_ex_language[OF tt] c211_connective_language
        c211_le_language[OF rt] c211_neg_language[OF rt] v
        paper_R_language_App[OF c211_atom_language[OF rt]])
qed

lemma c211_box_atomicity_language:
  "paper_R_relational \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G (c211_box_atomicity \<tau>) Prop"
  unfolding c211_box_atomicity_def
  by (rule paper_R_named_box_language[OF c211_rich c211_atomicity_language])

lemma c211_pred_type: "paper_R_relational \<tau> \<Longrightarrow> paper_R_type (Arr \<tau> Prop)"
  by (simp add: paper_R_relational_def)

lemma c211_LB_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_LB \<tau>) (Arr \<tau> (Arr (Arr \<tau> Prop) Prop))"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rt])
  have body: "paper_R_in_language \<Sigma> c211_G (named_paper_all \<tau> (NLam (c211_v \<tau> 10)
      (c211_imp (NApp (NVar (c211_v (Arr \<tau> Prop) 0)) (NVar (c211_v \<tau> 10)))
        (c211_le \<tau> (NVar (c211_v \<tau> 9)) (NVar (c211_v \<tau> 10)))))) Prop"
    by (intro c211_all_language[OF tt] c211_connective_language c211_le_language[OF rt]
        paper_R_language_App[OF c211_lang_Var[OF pt]] c211_lang_Var[OF tt])
  show ?thesis unfolding c211_LB_def
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF body pt] tt]) simp_all
qed

lemma c211_LB_printed_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_LB_printed \<tau>) (Arr \<tau> (Arr (Arr \<tau> Prop) Prop))"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rt])
  have body: "paper_R_in_language \<Sigma> c211_G (named_paper_all \<tau> (NLam (c211_v \<tau> 10)
      (c211_imp (NApp (NVar (c211_v (Arr \<tau> Prop) 0)) (NVar (c211_v \<tau> 10)))
        (c211_le \<tau> (NVar (c211_v \<tau> 10)) (NVar (c211_v \<tau> 9)))))) Prop"
    by (intro c211_all_language[OF tt] c211_connective_language c211_le_language[OF rt]
        paper_R_language_App[OF c211_lang_Var[OF pt]] c211_lang_Var[OF tt])
  show ?thesis unfolding c211_LB_printed_def
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF body pt] tt]) simp_all
qed

lemma c211_GLB_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_GLB \<tau>) (Arr \<tau> (Arr (Arr \<tau> Prop) Prop))"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rt])
  have body: "paper_R_in_language \<Sigma> c211_G (named_paper_all \<tau> (NLam (c211_v \<tau> 12)
      (c211_iff
        (NApp (NApp (c211_LB \<tau>) (NVar (c211_v \<tau> 12))) (NVar (c211_v (Arr \<tau> Prop) 1)))
        (c211_le \<tau> (NVar (c211_v \<tau> 12)) (NVar (c211_v \<tau> 11)))))) Prop"
    by (intro c211_all_language[OF tt] c211_connective_language c211_le_language[OF rt]
        paper_R_language_App[OF paper_R_language_App[OF c211_LB_language[OF rt]]]
        c211_lang_Var[OF pt] c211_lang_Var[OF tt])
  show ?thesis unfolding c211_GLB_def
    by (rule c211_lang_Lam[OF c211_lang_Lam[OF body pt] tt]) simp_all
qed

lemma c211_BC_language:
  assumes rt: "paper_R_relational \<tau>"
  shows "paper_R_in_language \<Sigma> c211_G (c211_BC \<tau>) Prop"
proof -
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rt])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rt])
  show ?thesis unfolding c211_BC_def
    by (intro c211_all_language[OF pt] c211_ex_language[OF tt]
        paper_R_language_App[OF paper_R_language_App[OF c211_GLB_language[OF rt]]]
        c211_lang_Var[OF pt] c211_lang_Var[OF tt])
qed

lemma c211_BF_language:
  assumes rt: "paper_R_type \<sigma>" and nt: "c211_G n = \<sigma>"
    and pl: "paper_R_in_language \<Sigma> c211_G P Prop"
  shows "paper_R_in_language \<Sigma> c211_G (c211_BF \<sigma> n P) Prop"
proof -
  have bnd: "\<And>A. paper_R_in_language \<Sigma> c211_G A Prop \<Longrightarrow>
      paper_R_in_language \<Sigma> c211_G (named_paper_all \<sigma> (NLam n A)) Prop"
    by (rule paper_R_named_all_binder_language; (assumption | rule nt | rule rt))
  show ?thesis unfolding c211_BF_def
    by (intro c211_connective_language bnd pl)
qed

lemma c211_BF_fv: "named_fv (c211_BF \<sigma> n P) = named_fv P - {n}"
  by (simp add: c211_BF_def named_paper_defined_fv named_paper_primitive_fv
      paper_R_named_box_fv)

subsection \<open>Language of the rigidity formulas\<close>

lemma c211_rtype_relational:
  "list_all paper_R_type \<sigma>s \<Longrightarrow> paper_R_relational (c211_rtype \<sigma>s)"
  by (induction \<sigma>s) (simp_all add: c211_rtype_def paper_R_relational_def)

lemma c211_zs_from_types: "map c211_G (c211_zs_from k \<sigma>s) = \<sigma>s"
  by (induction \<sigma>s arbitrary: k) simp_all

lemma c211_zs_types: "map c211_G (c211_zs \<sigma>s) = \<sigma>s"
  by (simp add: c211_zs_def c211_zs_from_types)

lemma c211_zs_from_bound: "m \<in> set (c211_zs_from k \<sigma>s) \<Longrightarrow> \<exists>\<rho> j. m = c211_v \<rho> (20 + j) \<and> k \<le> j"
proof (induction \<sigma>s arbitrary: k)
  case Nil then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  show ?case
  proof (cases "m = c211_v \<sigma> (20 + k)")
    case True then show ?thesis by blast
  next
    case False
    then have "m \<in> set (c211_zs_from (Suc k) \<sigma>s)" using Cons.prems by simp
    then obtain \<rho> j where "m = c211_v \<rho> (20 + j)" "Suc k \<le> j" using Cons.IH by blast
    then show ?thesis by (intro exI[of _ \<rho>] exI[of _ j]) simp
  qed
qed

lemma c211_zs_from_distinct: "distinct (c211_zs_from k \<sigma>s)"
proof (induction \<sigma>s arbitrary: k)
  case Nil then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  have "c211_v \<sigma> (20 + k) \<notin> set (c211_zs_from (Suc k) \<sigma>s)"
    using c211_zs_from_bound[of "c211_v \<sigma> (20 + k)" "Suc k" \<sigma>s] by auto
  then show ?case using Cons.IH by simp
qed

lemma c211_zs_distinct: "distinct (c211_zs \<sigma>s)"
  by (simp add: c211_zs_def c211_zs_from_distinct)

lemma c211_rtype_Cons: "c211_rtype (\<sigma> # \<sigma>s) = Arr \<sigma> (c211_rtype \<sigma>s)"
  by (simp add: c211_rtype_def)

lemma c211_vapp_language_gen:
  assumes types: "list_all paper_R_type (map c211_G zs)"
    and head: "paper_R_in_language \<Sigma> c211_G F (paper_type_vector (map c211_G zs) Prop)"
  shows "paper_R_in_language \<Sigma> c211_G (named_app_vec F (map NVar zs)) Prop"
  using types head
proof (induction zs arbitrary: F)
  case Nil then show ?case by simp
next
  case (Cons z zs)
  have zt: "paper_R_type (c211_G z)" using Cons.prems(1) by simp
  have arg: "paper_R_in_language \<Sigma> c211_G (NVar z) (c211_G z)"
    by (rule paper_R_language_Var[where G=c211_G and n=z, OF refl zt])
  have app: "paper_R_in_language \<Sigma> c211_G (NApp F (NVar z))
      (paper_type_vector (map c211_G zs) Prop)"
    by (rule paper_R_language_App[OF _ arg]) (use Cons.prems(2) in simp)
  show ?case using Cons.IH[OF _ app] Cons.prems(1) by simp
qed

lemma c211_vapp_language:
  assumes types: "list_all paper_R_type \<sigma>s"
  shows "paper_R_in_language \<Sigma> c211_G
    (c211_vapp (c211_v (c211_rtype \<sigma>s) k) (c211_zs \<sigma>s)) Prop"
proof -
  have rt: "paper_R_type (c211_rtype \<sigma>s)"
    by (rule c211_relational_type[OF c211_rtype_relational[OF types]])
  show ?thesis unfolding c211_vapp_def
    by (rule c211_vapp_language_gen)
      (use types rt in \<open>simp_all add: c211_zs_types c211_lang_Var[unfolded c211_rtype_def]
        c211_rtype_def\<close>)
qed

lemma c211_all_vec_language:
  "list_all paper_R_type \<sigma>s \<Longrightarrow> paper_R_in_language \<Sigma> c211_G P Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> c211_G (paper_R_all_vec c211_G (c211_zs \<sigma>s) P) Prop"
  by (rule paper_R_all_vec_language) (simp_all add: c211_zs_types)

lemma c211_rigid_language:
  assumes types: "list_all paper_R_type \<sigma>s"
  shows "paper_R_in_language \<Sigma> c211_G (c211_rigid \<sigma>s) (Arr (c211_rtype \<sigma>s) Prop)"
proof -
  have rr: "paper_R_relational (c211_rtype \<sigma>s)" by (rule c211_rtype_relational[OF types])
  have rt: "paper_R_type (c211_rtype \<sigma>s)" by (rule c211_relational_type[OF rr])
  have body: "paper_R_in_language \<Sigma> c211_G
      (c211_box (named_paper_all (c211_rtype \<sigma>s) (NLam (c211_v (c211_rtype \<sigma>s) 15)
        (c211_iff
          (paper_R_all_vec c211_G (c211_zs \<sigma>s)
            (c211_imp (c211_vapp (c211_v (c211_rtype \<sigma>s) 14) (c211_zs \<sigma>s))
              (c211_box (c211_vapp (c211_v (c211_rtype \<sigma>s) 15) (c211_zs \<sigma>s)))))
          (c211_le (c211_rtype \<sigma>s) (NVar (c211_v (c211_rtype \<sigma>s) 14))
            (NVar (c211_v (c211_rtype \<sigma>s) 15))))))) Prop"
    by (intro c211_connective_language c211_all_language[OF rt] c211_all_vec_language[OF types]
        c211_vapp_language[OF types] c211_le_language[OF rr] c211_lang_Var[OF rt])
  show ?thesis unfolding c211_rigid_def
    by (rule c211_lang_Lam[OF body rt]) simp
qed

lemma c211_RC_language:
  assumes types: "list_all paper_R_type \<sigma>s"
  shows "paper_R_in_language \<Sigma> c211_G (c211_RC \<sigma>s) Prop"
proof -
  have rr: "paper_R_relational (c211_rtype \<sigma>s)" by (rule c211_rtype_relational[OF types])
  have rt: "paper_R_type (c211_rtype \<sigma>s)" by (rule c211_relational_type[OF rr])
  show ?thesis unfolding c211_RC_def
    by (intro c211_all_language[OF rt] c211_ex_language[OF rt] c211_connective_language
        c211_all_vec_language[OF types] c211_vapp_language[OF types]
        paper_R_language_App[OF c211_rigid_language[OF types]] c211_lang_Var[OF rt])
qed

subsection \<open>Closedness\<close>

lemma c211_not_closed: "named_fv (c211_not \<tau>) = {}"
  by (induction \<tau>) auto

lemma c211_and_closed: "named_fv (c211_and \<tau>) = {}"
  by (induction \<tau>) auto

lemma c211_or_closed: "named_fv (c211_or \<tau>) = {}"
  by (induction \<tau>) auto

lemma c211_leq_closed: "named_fv (c211_leq \<tau>) = {}"
  by (auto simp: c211_leq_def named_paper_primitive_fv c211_or_closed)

lemma c211_le_fv: "named_fv (c211_le \<tau> A B) = named_fv A \<union> named_fv B"
  by (simp add: c211_le_def c211_leq_closed)

lemma c211_neg_fv: "named_fv (c211_neg \<tau> A) = named_fv A"
  by (simp add: c211_neg_def c211_not_closed)

lemma c211_neq_fv: "named_fv (c211_neq \<tau> A B) = named_fv A \<union> named_fv B"
  by (simp add: c211_neq_def named_paper_primitive_fv)

lemmas c211_fv_simps = named_paper_primitive_fv named_paper_defined_fv paper_R_named_box_fv
  c211_le_fv c211_neg_fv c211_neq_fv

lemma c211_atom_closed: "named_fv (c211_atom \<tau>) = {}"
  by (auto simp: c211_atom_def c211_fv_simps)

lemma c211_atomicity_closed: "named_fv (c211_atomicity \<tau>) = {}"
  by (auto simp: c211_atomicity_def c211_fv_simps c211_atom_closed)

lemma c211_box_atomicity_closed: "named_fv (c211_box_atomicity \<tau>) = {}"
  by (simp add: c211_box_atomicity_def paper_R_named_box_fv c211_atomicity_closed)

lemma c211_LB_closed: "named_fv (c211_LB \<tau>) = {}"
  by (auto simp: c211_LB_def c211_fv_simps)

lemma c211_GLB_closed: "named_fv (c211_GLB \<tau>) = {}"
  by (auto simp: c211_GLB_def c211_fv_simps c211_LB_closed)

lemma c211_BC_closed: "named_fv (c211_BC \<tau>) = {}"
  by (auto simp: c211_BC_def c211_fv_simps c211_GLB_closed)

lemma c211_vapp_fv: "named_fv (c211_vapp f zs) = insert f (set zs)"
proof -
  have "\<And>F. named_fv (named_app_vec F (map NVar zs)) = named_fv F \<union> set zs"
    by (induction zs) auto
  then show ?thesis unfolding c211_vapp_def by (metis Un_insert_left named_fv.simps(1) sup_bot_left)
qed

lemma c211_all_vec_fv: "named_fv (paper_R_all_vec G zs P) = named_fv P - set zs"
  by (induction zs) (auto simp: named_paper_primitive_fv)

lemma c211_rtype_size: "\<sigma> \<in> set \<sigma>s \<Longrightarrow> size \<sigma> < size (c211_rtype \<sigma>s)"
  unfolding c211_rtype_def by (induction \<sigma>s) auto

lemma c211_zs_not_rtype:
  "c211_v (c211_rtype \<sigma>s) k \<notin> set (c211_zs \<sigma>s)"
proof
  assume m: "c211_v (c211_rtype \<sigma>s) k \<in> set (c211_zs \<sigma>s)"
  have "c211_G (c211_v (c211_rtype \<sigma>s) k) \<in> set (map c211_G (c211_zs \<sigma>s))"
    using m by (simp only: set_map imageI)
  then have "c211_rtype \<sigma>s \<in> set \<sigma>s" by (simp only: c211_zs_types c211_v_type)
  then show False using c211_rtype_size by fastforce
qed

lemma c211_rigid_closed: "named_fv (c211_rigid \<sigma>s) = {}"
  using c211_zs_not_rtype[of \<sigma>s 14] c211_zs_not_rtype[of \<sigma>s 15]
  by (auto simp: c211_rigid_def c211_fv_simps c211_all_vec_fv c211_vapp_fv)

lemma c211_RC_closed: "named_fv (c211_RC \<sigma>s) = {}"
  using c211_zs_not_rtype[of \<sigma>s 16] c211_zs_not_rtype[of \<sigma>s 17]
  by (auto simp: c211_RC_def c211_fv_simps c211_all_vec_fv c211_vapp_fv c211_rigid_closed)

text \<open>The instance refuted below: monadic properties of propositions.\<close>

lemma c211_rtype_Prop: "c211_rtype [Prop] = Arr Prop Prop"
  by (simp add: c211_rtype_def)

lemma c211_zs_Prop: "c211_zs [Prop] = [c211_v Prop 20]"
  by (simp add: c211_zs_def)

ML \<open>
  val c211_syntax_names = ["c211_atomicity_language", "c211_box_atomicity_language",
    "c211_BC_language", "c211_BF_language", "c211_rigid_language", "c211_RC_language",
    "c211_box_atomicity_closed", "c211_BC_closed", "c211_RC_closed", "c211_BF_fv",
    "c211_zs_distinct", "c211_zs_types"];
  val _ = c211_syntax_names |> List.app (fn name =>
    let
      val th = Proof_Context.get_thm \<^context> name
      val _ = if null (Thm_Deps.all_oracles [th]) then () else error ("oracle: " ^ name)
      val _ = if null (Thm.hyps_of th) then () else error ("hyps: " ^ name)
      val _ = if null (Thm.tpairs_of th) then () else error ("tpairs: " ^ name)
    in () end);
  val _ = writeln ("C211-SYNTAX: " ^ string_of_int (length c211_syntax_names) ^ " clean endpoints")
\<close>

end
