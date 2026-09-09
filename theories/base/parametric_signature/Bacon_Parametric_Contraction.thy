theory Bacon_Parametric_Contraction
  imports Bacon_Parametric_Substitution
begin

section \<open>Beta and eta contraction in arbitrary-name languages\<close>

text \<open>
  (λv.A)B →β A[B/v], and λv.Fv →η F when v is not free in F.

  Isabelle representation: pbeta_contract is the first directed contraction;
  peta_contract uses PLam σ (PApp (pshift F) (PVar 0)) for the fresh-variable
  η pattern.  The name carrier remains arbitrary.

  Status: root contractions and their typing laws.  Contextual conversion
  and propositional evaluation are in the separate Conversion and
  Propositional theories; normalization and confluence are not claimed.
\<close>

inductive pbeta_contract :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  beta: "pbeta_contract (PApp (PLam \<sigma> M) N) (psubst0 N M)"

inductive peta_contract :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  eta: "peta_contract (PLam \<sigma> (PApp (pshift F) (PVar 0))) F"

section \<open>Subject reduction\<close>

text \<open>
  If Γ ⊢ A:σ and A →β B or A →η B, then Γ ⊢ B:σ.

  Isabelle representation: constructor-typing inversion lemmas expose immediate
  premises.  pbeta_preserves_typing and peta_preserves_typing then apply
  substitution preservation or reflect typing through pshift.

  Status: root subject reduction.  No normalization, confluence, or equality
  of interpreted values is asserted by these syntax lemmas.
\<close>


lemma ptype_app_iff:
  "has_ptype \<Gamma> (PApp M N) \<tau> \<longleftrightarrow>
    (\<exists>\<sigma>. has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<and> has_ptype \<Gamma> N \<sigma>)"
proof
  assume h: "has_ptype \<Gamma> (PApp M N) \<tau>"
  show "\<exists>\<sigma>. has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<and> has_ptype \<Gamma> N \<sigma>"
    using h by (cases rule: has_ptype.cases) (intro exI conjI; assumption)
next
  assume "\<exists>\<sigma>. has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<and> has_ptype \<Gamma> N \<sigma>"
  then obtain \<sigma> where m: "has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and n: "has_ptype \<Gamma> N \<sigma>" by (elim exE conjE)
  show "has_ptype \<Gamma> (PApp M N) \<tau>" by (rule has_ptype.PApp[OF m n])
qed

lemma ptype_lam_iff:
  "has_ptype \<Gamma> (PLam \<sigma> M) \<tau> \<longleftrightarrow>
    (\<exists>\<rho>. \<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho> \<and> has_ptype (\<sigma> # \<Gamma>) M \<rho>)"
proof
  assume h: "has_ptype \<Gamma> (PLam \<sigma> M) \<tau>"
  show "\<exists>\<rho>. \<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho> \<and> has_ptype (\<sigma> # \<Gamma>) M \<rho>"
    using h by (cases rule: has_ptype.cases) (intro exI conjI; (assumption | rule refl))
next
  assume "\<exists>\<rho>. \<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho> \<and> has_ptype (\<sigma> # \<Gamma>) M \<rho>"
  then obtain \<rho> where eq: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho>"
    and m: "has_ptype (\<sigma> # \<Gamma>) M \<rho>" by (elim exE conjE)
  show "has_ptype \<Gamma> (PLam \<sigma> M) \<tau>"
    using has_ptype.PLam[OF m] by (simp only: eq)
qed

lemma ptype_eq_iff:
  "has_ptype \<Gamma> (PEq \<sigma> M N) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>)"
proof
  assume h: "has_ptype \<Gamma> (PEq \<sigma> M N) \<tau>"
  show "\<tau> = Prop \<and> has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have ab: "has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>" using h by (rule conjunct2)
  have a: "has_ptype \<Gamma> M \<sigma>" using ab by (rule conjunct1)
  have b: "has_ptype \<Gamma> N \<sigma>" using ab by (rule conjunct2)
  show "has_ptype \<Gamma> (PEq \<sigma> M N) \<tau>"
    using has_ptype.PEq[OF a b] by (simp only: eq)
qed

lemma ptype_neg_iff:
  "has_ptype \<Gamma> (PNeg A) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype \<Gamma> A Prop)"
proof
  assume h: "has_ptype \<Gamma> (PNeg A) \<tau>"
  show "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have a: "has_ptype \<Gamma> A Prop" using h by (rule conjunct2)
  show "has_ptype \<Gamma> (PNeg A) \<tau>"
    using has_ptype.PNeg[OF a] by (simp only: eq)
qed

lemma ptype_conj_iff:
  "has_ptype \<Gamma> (PConj A B) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop)"
proof
  assume h: "has_ptype \<Gamma> (PConj A B) \<tau>"
  show "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have ab: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" using h by (rule conjunct2)
  have a: "has_ptype \<Gamma> A Prop" using ab by (rule conjunct1)
  have b: "has_ptype \<Gamma> B Prop" using ab by (rule conjunct2)
  show "has_ptype \<Gamma> (PConj A B) \<tau>"
    using has_ptype.PConj[OF a b] by (simp only: eq)
qed

lemma ptype_disj_iff:
  "has_ptype \<Gamma> (PDisj A B) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop)"
proof
  assume h: "has_ptype \<Gamma> (PDisj A B) \<tau>"
  show "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have ab: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" using h by (rule conjunct2)
  have a: "has_ptype \<Gamma> A Prop" using ab by (rule conjunct1)
  have b: "has_ptype \<Gamma> B Prop" using ab by (rule conjunct2)
  show "has_ptype \<Gamma> (PDisj A B) \<tau>"
    using has_ptype.PDisj[OF a b] by (simp only: eq)
qed

lemma ptype_imp_iff:
  "has_ptype \<Gamma> (PImp A B) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop)"
proof
  assume h: "has_ptype \<Gamma> (PImp A B) \<tau>"
  show "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have ab: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" using h by (rule conjunct2)
  have a: "has_ptype \<Gamma> A Prop" using ab by (rule conjunct1)
  have b: "has_ptype \<Gamma> B Prop" using ab by (rule conjunct2)
  show "has_ptype \<Gamma> (PImp A B) \<tau>"
    using has_ptype.PImp[OF a b] by (simp only: eq)
qed

lemma ptype_forall_iff:
  "has_ptype \<Gamma> (PForall \<sigma> A) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop)"
proof
  assume h: "has_ptype \<Gamma> (PForall \<sigma> A) \<tau>"
  show "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have a: "has_ptype (\<sigma> # \<Gamma>) A Prop" using h by (rule conjunct2)
  show "has_ptype \<Gamma> (PForall \<sigma> A) \<tau>"
    using has_ptype.PForall[OF a] by (simp only: eq)
qed

lemma ptype_exists_iff:
  "has_ptype \<Gamma> (PExists \<sigma> A) \<tau> \<longleftrightarrow> (\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop)"
proof
  assume h: "has_ptype \<Gamma> (PExists \<sigma> A) \<tau>"
  show "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
    using h by (cases rule: has_ptype.cases) (intro conjI; (assumption | rule refl))
next
  assume h: "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
  have eq: "\<tau> = Prop" using h by (rule conjunct1)
  have a: "has_ptype (\<sigma> # \<Gamma>) A Prop" using h by (rule conjunct2)
  show "has_ptype \<Gamma> (PExists \<sigma> A) \<tau>"
    using has_ptype.PExists[OF a] by (simp only: eq)
qed

lemma pvar_typing_iff:
  "has_ptype \<Gamma> (PVar n) \<tau> \<longleftrightarrow> lookup \<Gamma> n = Some \<tau>"
proof
  assume "has_ptype \<Gamma> (PVar n) \<tau>"
  then show "lookup \<Gamma> n = Some \<tau>" by (cases rule: has_ptype.cases) assumption
next
  assume "lookup \<Gamma> n = Some \<tau>"
  then show "has_ptype \<Gamma> (PVar n) \<tau>" by (rule has_ptype.PVar)
qed

text \<open>
  Undoing a variable renaming restores A; substituting B into a freshly
  inserted unused slot leaves A unchanged.

  Isabelle representation: psubst_prename_inverse proves the general inverse
  equation; psubst0_pshift and pshift_reflects_typing specialize it.

  Status: syntactic inverse and typing reflection.  The auxiliary PConst in
  typing reflection is not assumed to belong to an arbitrary signature.
\<close>

lemma psubst_prename_inverse:
  assumes "\<And>n. s (r n) = PVar n"
  shows "psubst s (prename r M) = M"
  using assms
proof (induction M arbitrary: s r)
  case (PLam \<sigma> M)
  have "psubst (plift_subst s) (prename (lift_ren r) M) = M"
    by (rule PLam.IH) (case_tac n; simp add: PLam.prems)
  then show ?case by simp
next
  case (PForall \<sigma> M)
  have "psubst (plift_subst s) (prename (lift_ren r) M) = M"
    by (rule PForall.IH) (case_tac n; simp add: PForall.prems)
  then show ?case by simp
next
  case (PExists \<sigma> M)
  have "psubst (plift_subst s) (prename (lift_ren r) M) = M"
    by (rule PExists.IH) (case_tac n; simp add: PExists.prems)
  then show ?case by simp
qed (simp_all only: prename.simps psubst.simps)

lemma psubst0_pshift[simp]: "psubst0 T (pshift M) = M"
  unfolding psubst0_def pshift_def
  by (rule psubst_prename_inverse) simp

lemma pshift_reflects_typing:
  assumes "has_ptype (\<sigma> # \<Gamma>) (pshift M) \<tau>"
  shows "has_ptype \<Gamma> M \<tau>"
proof -
  have witness: "has_ptype \<Gamma> (PConst undefined \<sigma>) \<sigma>"
    by (rule has_ptype.PConst)
  have "has_ptype \<Gamma> (psubst0 (PConst undefined \<sigma>) (pshift M)) \<tau>"
    by (rule psubst0_preserves_typing[OF assms witness])
  then show ?thesis by simp
qed

lemma pbeta_preserves_typing:
  assumes step: "pbeta_contract M N" and typed: "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> N \<tau>"
  using step typed
proof cases
  case (beta \<sigma> A T)
  have app_typed: "has_ptype \<Gamma> (PApp (PLam \<sigma> A) T) \<tau>"
    using typed beta by simp
  obtain \<rho> where lam: "has_ptype \<Gamma> (PLam \<sigma> A) (\<rho> \<rightarrow>\<^sub>o \<tau>)"
    and arg: "has_ptype \<Gamma> T \<rho>"
    using app_typed[unfolded ptype_app_iff] by (elim exE conjE)
  obtain \<upsilon> where shape: "(\<rho> \<rightarrow>\<^sub>o \<tau>) = (\<sigma> \<rightarrow>\<^sub>o \<upsilon>)"
    and body: "has_ptype (\<sigma> # \<Gamma>) A \<upsilon>"
    using lam[unfolded ptype_lam_iff] by (elim exE conjE)
  have pair: "\<rho> = \<sigma> \<and> \<tau> = \<upsilon>" using shape by (simp only: otype.inject)
  have eq: "\<rho> = \<sigma>" by (rule conjunct1[OF pair])
  have result_type: "\<tau> = \<upsilon>" by (rule conjunct2[OF pair])
  have arg': "has_ptype \<Gamma> T \<sigma>" using arg by (simp only: eq)
  have body': "has_ptype (\<sigma> # \<Gamma>) A \<tau>" using body by (simp only: result_type)
  have "has_ptype \<Gamma> (psubst0 T A) \<tau>"
    by (rule psubst0_preserves_typing[OF body' arg'])
  then show ?thesis using beta by simp
qed

lemma peta_preserves_typing:
  assumes step: "peta_contract M N" and typed: "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> N \<tau>"
  using step typed
proof cases
  case (eta \<sigma>)
  obtain \<rho> where result: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho>"
    and body: "has_ptype (\<sigma> # \<Gamma>) (PApp (pshift N) (PVar 0)) \<rho>"
    using typed eta by (simp only: ptype_lam_iff) (elim exE conjE)
  note app_components = body[unfolded ptype_app_iff]
  let ?pick = "\<lambda>(K :: 'a pterm). SOME nu :: otype.
      has_ptype (\<sigma> # \<Gamma>) (pshift K) (nu \<rightarrow>\<^sub>o \<rho>) \<and>
      has_ptype (\<sigma> # \<Gamma>) (PVar 0 :: 'a pterm) nu"
  have parts: "has_ptype (\<sigma> # \<Gamma>) (pshift N) (?pick N \<rightarrow>\<^sub>o \<rho>) \<and>
      has_ptype (\<sigma> # \<Gamma>) (PVar 0 :: 'a pterm) (?pick N)"
    by (rule someI_ex[where P="\<lambda>nu :: otype.
          has_ptype (\<sigma> # \<Gamma>) (pshift N) (nu \<rightarrow>\<^sub>o \<rho>) \<and>
          has_ptype (\<sigma> # \<Gamma>) (PVar 0 :: 'a pterm) nu", OF app_components])
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift N) (?pick N \<rightarrow>\<^sub>o \<rho>)"
    by (rule conjunct1[OF parts])
  have zero: "has_ptype (\<sigma> # \<Gamma>) (PVar 0 :: 'a pterm) (?pick N)"
    by (rule conjunct2[OF parts])
  have eq: "?pick N = \<sigma>" using zero by (simp add: pvar_typing_iff)
  have "has_ptype \<Gamma> N (?pick N \<rightarrow>\<^sub>o \<rho>)"
    by (rule pshift_reflects_typing[OF shifted])
  then show ?thesis using eta result eq by simp
qed

end
