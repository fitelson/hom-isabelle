theory Bacon_C_PC_Beta_Congruence
  imports Bacon_C_Vector_Contexts
begin

section \<open>Syntactic βη congruence through the PC skeleton\<close>

text \<open>
  A ≡βη A′ and B ≡βη B′ imply ¬A ≡βη ¬A′,
  A ∧ B ≡βη A′ ∧ B′, and similarly for ∨ and →.  At the
  appropriate types, F ≡βη F′ and A ≡βη A′ also imply
  F A ≡βη F′ A′.  Source role: contextual β and η from Bacon–Dorr
  Figure 2, p.8, used to normalize tuple projections in the full-vector
  PC case of Appendix A.2(i), p.65.

  Isabelle representation.  These are congruences of the typed syntactic
  relation beta_eta_equiv.  They are not applications of C Equivalence,
  CE, or CEV, and do not abstract arbitrary C theorems.  Source and target
  typing are retained in the generic context-transport lemmas.
\<close>

lemma C_PC_conversion_context:
  assumes conversion: "beta_eta_equiv \<Gamma> \<tau> A B"
    and typing: "\<And>X. \<Gamma> \<turnstile> X : \<tau> \<Longrightarrow> \<Delta> \<turnstile> f X : \<rho>"
    and beta_context: "\<And>X Y. compatible_step beta_contract X Y \<Longrightarrow>
      compatible_step beta_contract (f X) (f Y)"
    and eta_context: "\<And>X Y. compatible_step eta_contract X Y \<Longrightarrow>
      compatible_step eta_contract (f X) (f Y)"
  shows "beta_eta_equiv \<Delta> \<rho> (f A) (f B)"
  using conversion typing
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule beta_eta_equiv.Refl[OF Refl.prems[OF Refl.hyps]])
next
  case (Beta \<Gamma> M \<tau> N)
  have M: "\<Delta> \<turnstile> f M : \<rho>" by (rule Beta.prems[OF Beta.hyps(1)])
  have N: "\<Delta> \<turnstile> f N : \<rho>" by (rule Beta.prems[OF Beta.hyps(2)])
  have step: "compatible_step beta_contract (f M) (f N)" by (rule beta_context[OF Beta.hyps(3)])
  show ?case by (rule beta_eta_equiv.Beta[OF M N step])
next
  case (Eta \<Gamma> M \<tau> N)
  have M: "\<Delta> \<turnstile> f M : \<rho>" by (rule Eta.prems[OF Eta.hyps(1)])
  have N: "\<Delta> \<turnstile> f N : \<rho>" by (rule Eta.prems[OF Eta.hyps(2)])
  have step: "compatible_step eta_contract (f M) (f N)" by (rule eta_context[OF Eta.hyps(3)])
  show ?case by (rule beta_eta_equiv.Eta[OF M N step])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma C_PC_conversion_binary_context:
  assumes left: "beta_eta_equiv \<Gamma> \<sigma> A A'" and right: "beta_eta_equiv \<Gamma> \<tau> B B'"
    and typing: "\<And>X Y. \<Gamma> \<turnstile> X : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Y : \<tau> \<Longrightarrow>
      \<Gamma> \<turnstile> f X Y : \<rho>"
    and beta_left: "\<And>X X' Y. compatible_step beta_contract X X' \<Longrightarrow>
      compatible_step beta_contract (f X Y) (f X' Y)"
    and eta_left: "\<And>X X' Y. compatible_step eta_contract X X' \<Longrightarrow>
      compatible_step eta_contract (f X Y) (f X' Y)"
    and beta_right: "\<And>X Y Y'. compatible_step beta_contract Y Y' \<Longrightarrow>
      compatible_step beta_contract (f X Y) (f X Y')"
    and eta_right: "\<And>X Y Y'. compatible_step eta_contract Y Y' \<Longrightarrow>
      compatible_step eta_contract (f X Y) (f X Y')"
  shows "beta_eta_equiv \<Gamma> \<rho> (f A B) (f A' B')"
proof -
  have B: "\<Gamma> \<turnstile> B : \<tau>" by (rule beta_eta_equiv_left_type[OF right])
  have A': "\<Gamma> \<turnstile> A' : \<sigma>" by (rule beta_eta_equiv_right_type[OF left])
  have first: "beta_eta_equiv \<Gamma> \<rho> (f A B) (f A' B)"
  proof (rule C_PC_conversion_context[where f="\<lambda>X. f X B", OF left])
    fix X
    assume X: "\<Gamma> \<turnstile> X : \<sigma>"
    show "\<Gamma> \<turnstile> f X B : \<rho>" by (rule typing[OF X B])
  next
    fix X Y
    assume step: "compatible_step beta_contract X Y"
    show "compatible_step beta_contract (f X B) (f Y B)" by (rule beta_left[OF step])
  next
    fix X Y
    assume step: "compatible_step eta_contract X Y"
    show "compatible_step eta_contract (f X B) (f Y B)" by (rule eta_left[OF step])
  qed
  have second: "beta_eta_equiv \<Gamma> \<rho> (f A' B) (f A' B')"
  proof (rule C_PC_conversion_context[where f="\<lambda>Y. f A' Y", OF right])
    fix Y
    assume Y: "\<Gamma> \<turnstile> Y : \<tau>"
    show "\<Gamma> \<turnstile> f A' Y : \<rho>" by (rule typing[OF A' Y])
  next
    fix X Y
    assume step: "compatible_step beta_contract X Y"
    show "compatible_step beta_contract (f A' X) (f A' Y)" by (rule beta_right[OF step])
  next
    fix X Y
    assume step: "compatible_step eta_contract X Y"
    show "compatible_step eta_contract (f A' X) (f A' Y)" by (rule eta_right[OF step])
  qed
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

subsection \<open>Negation and the three Boolean binary constructors\<close>

lemma C_PC_beta_eta_Neg:
  assumes conversion: "beta_eta_equiv \<Gamma> Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Neg A) (Neg B)"
proof (rule C_PC_conversion_context[where f=Neg, OF conversion])
  fix X
  assume X: "\<Gamma> \<turnstile> X : Prop"
  show "\<Gamma> \<turnstile> Neg X : Prop" by (rule has_type.Neg[OF X])
next
  fix X Y
  assume step: "compatible_step beta_contract X Y"
  show "compatible_step beta_contract (Neg X) (Neg Y)" by (rule compatible_step.Neg_body[OF step])
next
  fix X Y
  assume step: "compatible_step eta_contract X Y"
  show "compatible_step eta_contract (Neg X) (Neg Y)" by (rule compatible_step.Neg_body[OF step])
qed

lemma C_PC_beta_eta_Conj:
  assumes A: "beta_eta_equiv \<Gamma> Prop A A'" and B: "beta_eta_equiv \<Gamma> Prop B B'"
  shows "beta_eta_equiv \<Gamma> Prop (Conj A B) (Conj A' B')"
proof (rule C_PC_conversion_binary_context[where f=Conj, OF A B])
  show "\<And>X Y. \<Gamma> \<turnstile> X : Prop \<Longrightarrow> \<Gamma> \<turnstile> Y : Prop \<Longrightarrow> \<Gamma> \<turnstile> Conj X Y : Prop"
    by (rule has_type.Conj)
  show "\<And>X X' Y. compatible_step beta_contract X X' \<Longrightarrow> compatible_step beta_contract (Conj X Y) (Conj X' Y)"
    by (rule compatible_step.Conj_left)
  show "\<And>X X' Y. compatible_step eta_contract X X' \<Longrightarrow> compatible_step eta_contract (Conj X Y) (Conj X' Y)"
    by (rule compatible_step.Conj_left)
  show "\<And>X Y Y'. compatible_step beta_contract Y Y' \<Longrightarrow> compatible_step beta_contract (Conj X Y) (Conj X Y')"
    by (rule compatible_step.Conj_right)
  show "\<And>X Y Y'. compatible_step eta_contract Y Y' \<Longrightarrow> compatible_step eta_contract (Conj X Y) (Conj X Y')"
    by (rule compatible_step.Conj_right)
qed

lemma C_PC_beta_eta_Disj:
  assumes A: "beta_eta_equiv \<Gamma> Prop A A'" and B: "beta_eta_equiv \<Gamma> Prop B B'"
  shows "beta_eta_equiv \<Gamma> Prop (Disj A B) (Disj A' B')"
proof (rule C_PC_conversion_binary_context[where f=Disj, OF A B])
  show "\<And>X Y. \<Gamma> \<turnstile> X : Prop \<Longrightarrow> \<Gamma> \<turnstile> Y : Prop \<Longrightarrow> \<Gamma> \<turnstile> Disj X Y : Prop"
    by (rule has_type.Disj)
  show "\<And>X X' Y. compatible_step beta_contract X X' \<Longrightarrow> compatible_step beta_contract (Disj X Y) (Disj X' Y)"
    by (rule compatible_step.Disj_left)
  show "\<And>X X' Y. compatible_step eta_contract X X' \<Longrightarrow> compatible_step eta_contract (Disj X Y) (Disj X' Y)"
    by (rule compatible_step.Disj_left)
  show "\<And>X Y Y'. compatible_step beta_contract Y Y' \<Longrightarrow> compatible_step beta_contract (Disj X Y) (Disj X Y')"
    by (rule compatible_step.Disj_right)
  show "\<And>X Y Y'. compatible_step eta_contract Y Y' \<Longrightarrow> compatible_step eta_contract (Disj X Y) (Disj X Y')"
    by (rule compatible_step.Disj_right)
qed

lemma C_PC_beta_eta_Imp:
  assumes A: "beta_eta_equiv \<Gamma> Prop A A'" and B: "beta_eta_equiv \<Gamma> Prop B B'"
  shows "beta_eta_equiv \<Gamma> Prop (Imp A B) (Imp A' B')"
proof (rule C_PC_conversion_binary_context[where f=Imp, OF A B])
  show "\<And>X Y. \<Gamma> \<turnstile> X : Prop \<Longrightarrow> \<Gamma> \<turnstile> Y : Prop \<Longrightarrow> \<Gamma> \<turnstile> Imp X Y : Prop"
    by (rule has_type.Imp)
  show "\<And>X X' Y. compatible_step beta_contract X X' \<Longrightarrow> compatible_step beta_contract (Imp X Y) (Imp X' Y)"
    by (rule compatible_step.Imp_left)
  show "\<And>X X' Y. compatible_step eta_contract X X' \<Longrightarrow> compatible_step eta_contract (Imp X Y) (Imp X' Y)"
    by (rule compatible_step.Imp_left)
  show "\<And>X Y Y'. compatible_step beta_contract Y Y' \<Longrightarrow> compatible_step beta_contract (Imp X Y) (Imp X Y')"
    by (rule compatible_step.Imp_right)
  show "\<And>X Y Y'. compatible_step eta_contract Y Y' \<Longrightarrow> compatible_step eta_contract (Imp X Y) (Imp X Y')"
    by (rule compatible_step.Imp_right)
qed

subsection \<open>Application at arbitrary argument and result types\<close>

lemma C_PC_beta_eta_App:
  assumes F: "beta_eta_equiv \<Gamma> (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G" and A: "beta_eta_equiv \<Gamma> \<sigma> A B"
  shows "beta_eta_equiv \<Gamma> \<tau> (App F A) (App G B)"
proof (rule C_PC_conversion_binary_context[where f=App, OF F A])
  show "\<And>X Y. \<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Y : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> App X Y : \<tau>"
    by (rule has_type.App)
  show "\<And>X X' Y. compatible_step beta_contract X X' \<Longrightarrow> compatible_step beta_contract (App X Y) (App X' Y)"
    by (rule compatible_step.App_left)
  show "\<And>X X' Y. compatible_step eta_contract X X' \<Longrightarrow> compatible_step eta_contract (App X Y) (App X' Y)"
    by (rule compatible_step.App_left)
  show "\<And>X Y Y'. compatible_step beta_contract Y Y' \<Longrightarrow> compatible_step beta_contract (App X Y) (App X Y')"
    by (rule compatible_step.App_right)
  show "\<And>X Y Y'. compatible_step eta_contract Y Y' \<Longrightarrow> compatible_step eta_contract (App X Y) (App X Y')"
    by (rule compatible_step.App_right)
qed

corollary C_PC_beta_eta_App_left:
  assumes conversion: "beta_eta_equiv \<Gamma> (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G" and argument: "\<Gamma> \<turnstile> A : \<sigma>"
  shows "beta_eta_equiv \<Gamma> \<tau> (App F A) (App G A)"
  by (rule C_PC_beta_eta_App[OF conversion beta_eta_equiv.Refl[OF argument]])

corollary C_PC_beta_eta_App_right:
  assumes operator: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and conversion: "beta_eta_equiv \<Gamma> \<sigma> A B"
  shows "beta_eta_equiv \<Gamma> \<tau> (App F A) (App F B)"
  by (rule C_PC_beta_eta_App[OF beta_eta_equiv.Refl[OF operator] conversion])

text \<open>
  These lemmas lift supplied tuple-projection conversions through the
  Boolean skeleton.  Renaming and capture-avoiding substitution transport
  for arbitrary conversion derivations are not asserted here: their root
  β/η commutation and compatible-context proofs are separate obligations
  in this C-only import spine.
\<close>

end
