theory Bacon_H_Equivalence_Presentations
  imports Bacon_Base.Bacon_Deduction
begin

section \<open>Two independent presentations starting with H alone\<close>

text \<open>
  The Rule of Equivalence permits R =σ̄→t S when R x̄ ↔ S x̄ is a
  theorem of the theory being defined, with x̄ fresh for R,S.  Logical
  Equivalence instead adds R =σ̄→t S only when R x̄ ↔ S x̄ is a theorem
  of H itself.  Source: Bacon, pp.125–127, Logical Equivalence,
  Definition 6.1 and Theorem 6.1(1–2).

  Isabelle representation.  HE_proves closes H under the former rule;
  HLE_proves adds the latter H-certified instances.  Neither definition
  includes C, CE, CEV, Boolean identities, or Classical identities.
  In particular, the LogicalEquivalence constructor below has an H_proves
  premise, not an HLE_proves premise.  Both presentations retain the
  represented Hilbert rules MP, Gen, and Inst.

  Scope.  These are represented full-F/string-stock calculi.  The source
  passage initially discusses relational types R; the identity rule here
  still concludes only at proposition-ending arrow types, although its
  argument types may be arbitrary F types.  Primitive Imp and dedicated
  logical constructors, together with H's explicit IndividualExistence,
  remain source-language/presentation qualifications.  Literal source
  correspondence and equality with the axiom presentation require separate
  bridge theorems; they are not built into these inductive definitions.
\<close>

subsection \<open>Source-order vector syntax independent of the C import chain\<close>

fun H_rule_arrow :: "otype list \<Rightarrow> otype \<Rightarrow> otype" where
  "H_rule_arrow [] \<tau> = \<tau>"
| "H_rule_arrow (\<sigma> # \<sigma>s) \<tau> = \<sigma> \<rightarrow>\<^sub>o H_rule_arrow \<sigma>s \<tau>"

fun H_rule_app_vec :: "oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "H_rule_app_vec F [] = F"
| "H_rule_app_vec F (A # As) = H_rule_app_vec (App F A) As"

fun H_rule_raise :: "nat \<Rightarrow> oterm \<Rightarrow> oterm" where
  "H_rule_raise 0 F = F"
| "H_rule_raise (Suc n) F = rename Suc (H_rule_raise n F)"

definition H_rule_args :: "nat \<Rightarrow> oterm list" where
  "H_rule_args n = rev (map Var [0..<n])"

definition H_rule_body :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "H_rule_body \<Delta> F G =
    (H_rule_app_vec (H_rule_raise (length \<Delta>) F) (H_rule_args (length \<Delta>))
      \<longleftrightarrow>\<^sub>o
     H_rule_app_vec (H_rule_raise (length \<Delta>) G) (H_rule_args (length \<Delta>)))"

text \<open>
  Δ lists de Bruijn slots from innermost to outermost; rev Δ is the
  argument-type order σ̄.  The fresh argument list is [vₙ₋₁,…,v₀].
  Raising ambient R,S through Δ enforces the freshness side condition.
  The empty vector gives the propositional rule.  These small syntax
  operations are local to the H-only layer; a downstream bridge identifies
  them with the earlier vector syntax without importing C here.
\<close>

lemma H_rule_raise_type:
  assumes typed: "\<Gamma> \<turnstile> F : \<tau>"
  shows "\<Delta> @ \<Gamma> \<turnstile> H_rule_raise (length \<Delta>) F : \<tau>"
proof (induction \<Delta>)
  case Nil
  show ?case using typed by simp
next
  case (Cons \<sigma> \<Delta>)
  have shifted: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> shift (H_rule_raise (length \<Delta>) F) : \<tau>"
    by (rule weakening_front[OF Cons.IH])
  show ?case using shifted by (simp only: length_Cons H_rule_raise.simps append_Cons shift_def)
qed

lemma H_rule_args_type:
  "list_all2 (\<lambda>A \<sigma>. \<Delta> @ \<Gamma> \<turnstile> A : \<sigma>) (H_rule_args (length \<Delta>)) (rev \<Delta>)"
proof -
  have ascending: "list_all2 (\<lambda>A \<sigma>. \<Delta> @ \<Gamma> \<turnstile> A : \<sigma>) (map Var [0..<length \<Delta>]) \<Delta>"
  proof (unfold list_all2_conv_all_nth, rule conjI)
    show "length (map Var [0..<length \<Delta>]) = length \<Delta>" by simp
  next
    show "\<forall>i < length (map Var [0..<length \<Delta>]). \<Delta> @ \<Gamma> \<turnstile>
      (map Var [0..<length \<Delta>]) ! i : \<Delta> ! i"
    proof (intro allI impI)
      fix i
      assume bound: "i < length (map Var [0..<length \<Delta>])"
      have i: "i < length \<Delta>" using bound by simp
      have index: "lookup (\<Delta> @ \<Gamma>) i = Some (\<Delta> ! i)" using i by (simp add: lookup_def nth_append)
      have typed: "\<Delta> @ \<Gamma> \<turnstile> Var i : \<Delta> ! i" by (rule has_type.Var[OF index])
      show "\<Delta> @ \<Gamma> \<turnstile> (map Var [0..<length \<Delta>]) ! i : \<Delta> ! i" using typed i by simp
    qed
  qed
  show ?thesis using ascending by (simp only: H_rule_args_def list_all2_rev)
qed

lemma H_rule_app_vec_type:
  assumes function_type: "\<Gamma> \<turnstile> F : H_rule_arrow \<sigma>s \<tau>"
    and arguments: "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) As \<sigma>s"
  shows "\<Gamma> \<turnstile> H_rule_app_vec F As : \<tau>"
  using function_type arguments
proof (induction \<sigma>s arbitrary: F As)
  case Nil
  then show ?case by (cases As) simp_all
next
  case (Cons \<sigma> \<sigma>s)
  from Cons.prems(2) obtain A Bs where args: "As = A # Bs" and A: "\<Gamma> \<turnstile> A : \<sigma>"
    and Bs: "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) Bs \<sigma>s" by (cases As) auto
  have F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o H_rule_arrow \<sigma>s \<tau>" using Cons.prems(1) by simp
  have applied: "\<Gamma> \<turnstile> App F A : H_rule_arrow \<sigma>s \<tau>" by (rule has_type.App[OF F A])
  show ?case using Cons.IH[where F="App F A" and As=Bs, OF applied Bs] by (simp only: args H_rule_app_vec.simps)
qed

lemma H_rule_body_type:
  assumes F: "\<Gamma> \<turnstile> F : H_rule_arrow (rev \<Delta>) Prop"
    and G: "\<Gamma> \<turnstile> G : H_rule_arrow (rev \<Delta>) Prop"
  shows "\<Delta> @ \<Gamma> \<turnstile> H_rule_body \<Delta> F G : Prop"
proof -
  have left: "\<Delta> @ \<Gamma> \<turnstile> H_rule_app_vec (H_rule_raise (length \<Delta>) F) (H_rule_args (length \<Delta>)) : Prop"
    by (rule H_rule_app_vec_type[OF H_rule_raise_type[OF F] H_rule_args_type])
  have right: "\<Delta> @ \<Gamma> \<turnstile> H_rule_app_vec (H_rule_raise (length \<Delta>) G) (H_rule_args (length \<Delta>)) : Prop"
    by (rule H_rule_app_vec_type[OF H_rule_raise_type[OF G] H_rule_args_type])
  show ?thesis unfolding H_rule_body_def
    by (rule has_type.Conj[OF has_type.Imp[OF left right] has_type.Imp[OF right left]])
qed

lemma H_rule_body_empty[simp]: "H_rule_body [] F G = (F \<longleftrightarrow>\<^sub>o G)"
  by (simp add: H_rule_body_def H_rule_args_def)

subsection \<open>H closed under its own Rule of Equivalence\<close>

inductive HE_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  H: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> HE_proves \<Gamma> A"
| Equivalence: "\<Gamma> \<turnstile> F : H_rule_arrow (rev \<Delta>) Prop \<Longrightarrow>
    \<Gamma> \<turnstile> G : H_rule_arrow (rev \<Delta>) Prop \<Longrightarrow>
    HE_proves (\<Delta> @ \<Gamma>) (H_rule_body \<Delta> F G) \<Longrightarrow>
    HE_proves \<Gamma> (Eq (H_rule_arrow (rev \<Delta>) Prop) F G)"
| MP: "HE_proves \<Gamma> A \<Longrightarrow> HE_proves \<Gamma> (Imp A B) \<Longrightarrow> HE_proves \<Gamma> B"
| Gen: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    HE_proves (\<sigma> # \<Gamma>) (Imp (shift P) Q) \<Longrightarrow> HE_proves \<Gamma> (Imp P (Forall \<sigma> Q))"
| Inst: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    HE_proves (\<sigma> # \<Gamma>) (Imp P (shift Q)) \<Longrightarrow> HE_proves \<Gamma> (Imp (Exists \<sigma> P) Q)"

lemma HE_proves_formula:
  "HE_proves \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
proof (induction rule: HE_proves.induct)
  case (H \<Gamma> A)
  show ?case by (rule H_proves_formula[OF H.hyps])
next
  case (Equivalence \<Gamma> F \<Delta> G)
  show ?case by (rule has_type.Eq[OF Equivalence.hyps(1,2)])
next
  case (MP \<Gamma> A B)
  show ?case using MP.IH(2) by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule has_type.Imp[OF Gen.hyps(1) has_type.Forall[OF Gen.hyps(2)]])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule has_type.Imp[OF has_type.Exists[OF Inst.hyps(1)] Inst.hyps(2)])
qed

subsection \<open>H plus only H-certified Logical Equivalence instances\<close>

inductive HLE_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  H: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> HLE_proves \<Gamma> A"
| LogicalEquivalence: "\<Gamma> \<turnstile> F : H_rule_arrow (rev \<Delta>) Prop \<Longrightarrow>
    \<Gamma> \<turnstile> G : H_rule_arrow (rev \<Delta>) Prop \<Longrightarrow>
    \<Delta> @ \<Gamma> \<turnstile>\<^sub>H H_rule_body \<Delta> F G \<Longrightarrow>
    HLE_proves \<Gamma> (Eq (H_rule_arrow (rev \<Delta>) Prop) F G)"
| MP: "HLE_proves \<Gamma> A \<Longrightarrow> HLE_proves \<Gamma> (Imp A B) \<Longrightarrow> HLE_proves \<Gamma> B"
| Gen: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    HLE_proves (\<sigma> # \<Gamma>) (Imp (shift P) Q) \<Longrightarrow> HLE_proves \<Gamma> (Imp P (Forall \<sigma> Q))"
| Inst: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    HLE_proves (\<sigma> # \<Gamma>) (Imp P (shift Q)) \<Longrightarrow> HLE_proves \<Gamma> (Imp (Exists \<sigma> P) Q)"

lemma HLE_proves_formula:
  "HLE_proves \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
proof (induction rule: HLE_proves.induct)
  case (H \<Gamma> A)
  show ?case by (rule H_proves_formula[OF H.hyps])
next
  case (LogicalEquivalence \<Gamma> F \<Delta> G)
  show ?case by (rule has_type.Eq[OF LogicalEquivalence.hyps(1,2)])
next
  case (MP \<Gamma> A B)
  show ?case using MP.IH(2) by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule has_type.Imp[OF Gen.hyps(1) has_type.Forall[OF Gen.hyps(2)]])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule has_type.Imp[OF has_type.Exists[OF Inst.hyps(1)] Inst.hyps(2)])
qed

text \<open>
  Every theorem of H plus Logical Equivalence is a theorem of H closed
  under Equivalence.  Source: Theorem 6.1, inclusion (2) ⊆ (1), p.126.
  The key case first imports the H-certified biconditional into HE.
  No inclusion in the other direction is assumed or proved in this leaf.
\<close>

theorem HLE_proves_to_HE:
  "HLE_proves \<Gamma> A \<Longrightarrow> HE_proves \<Gamma> A"
proof (induction rule: HLE_proves.induct)
  case (H \<Gamma> A)
  show ?case by (rule HE_proves.H[OF H.hyps])
next
  case (LogicalEquivalence \<Gamma> F \<Delta> G)
  have premise_HE: "HE_proves (\<Delta> @ \<Gamma>) (H_rule_body \<Delta> F G)"
    by (rule HE_proves.H[OF LogicalEquivalence.hyps(3)])
  show ?case by (rule HE_proves.Equivalence[OF LogicalEquivalence.hyps(1,2) premise_HE])
next
  case (MP \<Gamma> A B)
  show ?case by (rule HE_proves.MP[OF MP.IH])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule HE_proves.Gen[OF Gen.hyps(1,2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule HE_proves.Inst[OF Inst.hyps(1,2) Inst.IH])
qed

end
