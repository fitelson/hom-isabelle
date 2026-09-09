theory Bacon_Source_Propositional_Typing
  imports Bacon_Source_Propositional
begin

section \<open>Recovering the types of substituted propositions\<close>

text \<open>
  PC substitutes formulas for propositional letters (Bacon–Dorr Figure 2).
  If the resulting source formula has type t, every occurring substituted
  proposition has type t.  This follows from the fixed connective types
  in §1.1 and the literal Figure 1 abbreviations.

  Isabelle representation: elementary source typing inversion and uniqueness
  recover the atom types.  Signature recovery uses the existing exact
  atom-occurrence characterization.

  Status: the existing paper_PC guard is not strengthened.  The final lemma
  derives the additional atom-language information needed by PC transport.
\<close>

lemma source_app_type_obtain:
  assumes "has_stype L \<Gamma> (SApp M N) \<tau>"
  obtains \<sigma> where "has_stype L \<Gamma> M (Arr \<sigma> \<tau>)" and "has_stype L \<Gamma> N \<sigma>"
  using assms by (cases rule: has_stype.cases) (rule that; assumption)

lemma source_lam_type_obtain:
  assumes "has_stype L \<Gamma> (SLam \<sigma> M) \<tau>"
  obtains \<rho> where "\<tau> = Arr \<sigma> \<rho>" and "has_stype L (\<sigma> # \<Gamma>) M \<rho>"
  using assms by (cases rule: has_stype.cases) (rule that; (rule refl | assumption))

lemma source_typing_unique:
  assumes first: "has_stype L \<Gamma> A \<sigma>" and second: "has_stype L \<Gamma> A \<rho>"
  shows "\<sigma> = \<rho>"
  using first second
proof (induction arbitrary: \<rho> rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  have look: "lookup \<Gamma> n = Some \<rho>"
    using Var.prems by (cases rule: has_stype.cases) assumption
  show ?case using Var.hyps look by simp
next
  case Const
  show ?case using Const.prems by (cases rule: has_stype.cases) simp
next
  case Logical
  show ?case using Logical.prems by (cases rule: has_stype.cases) simp
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  obtain \<nu> where mt: "has_stype L \<Gamma> M (Arr \<nu> \<rho>)"
    and nt: "has_stype L \<Gamma> N \<nu>"
    by (rule source_app_type_obtain[OF App.prems]; rule that; assumption)
  have eq: "Arr \<sigma> \<tau> = Arr \<nu> \<rho>" by (rule App.IH(1)[OF mt])
  show ?case using eq by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  obtain \<nu> where eq: "\<rho> = Arr \<sigma> \<nu>" and mt: "has_stype L (\<sigma> # \<Gamma>) M \<nu>"
    by (rule source_lam_type_obtain[OF Lam.prems]; rule that; assumption)
  have body_eq: "\<tau> = \<nu>" by (rule Lam.IH[OF mt])
  show ?case by (simp only: eq body_eq)
qed

lemma source_unary_proposition_type_iff:
  assumes head: "has_stype L \<Gamma> F (Arr Prop Prop)"
  shows "has_stype L \<Gamma> (SApp F A) Prop \<longleftrightarrow> has_stype L \<Gamma> A Prop"
proof
  assume app: "has_stype L \<Gamma> (SApp F A) Prop"
  obtain \<sigma> where ft: "has_stype L \<Gamma> F (Arr \<sigma> Prop)" and at: "has_stype L \<Gamma> A \<sigma>"
    by (rule source_app_type_obtain[OF app]; rule that; assumption)
  have eq: "Arr \<sigma> Prop = Arr Prop Prop" by (rule source_typing_unique[OF ft head])
  have sigma: "\<sigma> = Prop" using eq by simp
  show "has_stype L \<Gamma> A Prop" using at by (simp only: sigma)
next
  assume arg: "has_stype L \<Gamma> A Prop"
  show "has_stype L \<Gamma> (SApp F A) Prop" by (rule has_stype.App[OF head arg])
qed

lemma source_binary_proposition_type_iff:
  assumes head: "has_stype L \<Gamma> F (Arr Prop (Arr Prop Prop))"
  shows "has_stype L \<Gamma> (SApp (SApp F A) B) Prop \<longleftrightarrow>
    (has_stype L \<Gamma> A Prop \<and> has_stype L \<Gamma> B Prop)"
proof
  assume app: "has_stype L \<Gamma> (SApp (SApp F A) B) Prop"
  obtain \<rho> where fa: "has_stype L \<Gamma> (SApp F A) (Arr \<rho> Prop)"
    and bt: "has_stype L \<Gamma> B \<rho>" by (rule source_app_type_obtain[OF app]; rule that; assumption)
  obtain \<sigma> where ft: "has_stype L \<Gamma> F (Arr \<sigma> (Arr \<rho> Prop))"
    and at: "has_stype L \<Gamma> A \<sigma>" by (rule source_app_type_obtain[OF fa]; rule that; assumption)
  have eq: "Arr \<sigma> (Arr \<rho> Prop) = Arr Prop (Arr Prop Prop)"
    by (rule source_typing_unique[OF ft head])
  have sigma: "\<sigma> = Prop" using eq by simp
  have rho: "\<rho> = Prop" using eq by simp
  show "has_stype L \<Gamma> A Prop \<and> has_stype L \<Gamma> B Prop"
    using at bt by (simp only: sigma rho; rule conjI; assumption)
next
  assume pair: "has_stype L \<Gamma> A Prop \<and> has_stype L \<Gamma> B Prop"
  show "has_stype L \<Gamma> (SApp (SApp F A) B) Prop"
    by (rule has_stype.App[OF has_stype.App[OF head conjunct1[OF pair]] conjunct2[OF pair]])
qed

lemma paper_not_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_not A) Prop \<longleftrightarrow>
    has_stype paper_logical_type \<Gamma> A Prop"
  unfolding paper_not_def
proof (rule source_unary_proposition_type_iff)
  show "has_stype paper_logical_type \<Gamma> (SLogical SNot) (Arr Prop Prop)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=SNot] by simp
qed

lemma paper_and_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_and A B) Prop \<longleftrightarrow>
    (has_stype paper_logical_type \<Gamma> A Prop \<and> has_stype paper_logical_type \<Gamma> B Prop)"
  unfolding paper_and_def
proof (rule source_binary_proposition_type_iff)
  show "has_stype paper_logical_type \<Gamma> (SLogical SAnd) (Arr Prop (Arr Prop Prop))"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=SAnd] by simp
qed

lemma paper_or_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_or A B) Prop \<longleftrightarrow>
    (has_stype paper_logical_type \<Gamma> A Prop \<and> has_stype paper_logical_type \<Gamma> B Prop)"
  unfolding paper_or_def
proof (rule source_binary_proposition_type_iff)
  show "has_stype paper_logical_type \<Gamma> (SLogical SOr) (Arr Prop (Arr Prop Prop))"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=SOr] by simp
qed

lemma paper_imp_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_imp A B) Prop \<longleftrightarrow>
    (has_stype paper_logical_type \<Gamma> A Prop \<and> has_stype paper_logical_type \<Gamma> B Prop)"
  unfolding paper_imp_def by (rule source_binary_proposition_type_iff[OF paper_imp_const_type])

lemma paper_iff_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_iff A B) Prop \<longleftrightarrow>
    (has_stype paper_logical_type \<Gamma> A Prop \<and> has_stype paper_logical_type \<Gamma> B Prop)"
  unfolding paper_iff_def by (rule source_binary_proposition_type_iff[OF paper_iff_const_type])

lemma paper_prop_instance_type_iff:
  "has_stype paper_logical_type \<Gamma> (paper_prop_instance v P) Prop \<longleftrightarrow>
    (\<forall>a\<in>sprop_atoms P. has_stype paper_logical_type \<Gamma> (v a) Prop)"
  by (induction P)
    (auto simp: paper_not_type_iff paper_and_type_iff paper_or_type_iff
      paper_imp_type_iff paper_iff_type_iff)

lemma paper_prop_instance_language_iff:
  "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_prop_instance v P) Prop \<longleftrightarrow>
    (\<forall>a\<in>sprop_atoms P. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop)"
  by (auto simp: sterm_in_language_def paper_prop_instance_type_iff
      paper_prop_instance_signature_iff)

lemma paper_PC_atoms:
  assumes "paper_PC \<Sigma> \<Gamma> A"
  obtains P :: "nat sprop_template" and v where "sprop_tautology P"
    and "A = paper_prop_instance v P"
    and "\<forall>a\<in>sprop_atoms P. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
proof -
  have language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    by (rule paper_PC_language[OF assms])
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and eq: "A = paper_prop_instance v P"
    using conjunct2[OF assms[unfolded paper_PC_def]] by (elim exE conjE)
  have atoms: "\<forall>a\<in>sprop_atoms P. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (v a) Prop"
    using language by (simp only: eq paper_prop_instance_language_iff)
  show thesis by (rule that[OF taut eq atoms])
qed

end
