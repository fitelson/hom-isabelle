theory Bacon_Source_Vector_Syntax
  imports Bacon_Source_Variable_Embedding Bacon_Source_Renaming_Conversion
    Bacon_Source_Conversion_Contexts
begin

section \<open>Typed source abstraction and application vectors\<close>

text \<open>
  Close all slots of a finite frame Δ by forming λvₙ₋₁.…λv₀.A.
  The operation has the reversed arrow-type vector, and applying it uses
  the argument order [vₙ₋₁,…,v₀].  Source role: the finite abstraction
  argument for deriving variable-renaming coherence from Bacon–Dorr
  Definition 3.1(ii.a–d), pp.43–44.

  Isabelle representation.  These are source sterm operations over an
  arbitrary logical-type function and signature.  No C-prefixed vector
  operation or C proof is imported.  A term typed in Γ becomes closed
  after sabstract_prefix Γ; this follows from source typing's free-slot
  bound.  The empty frame and mixed F types are included.

  Status: syntax, typing, signature, and closedness only.  Application
  reduction and semantic renaming coherence remain separate proofs.
\<close>

fun sarrow_type :: "otype list \<Rightarrow> otype \<Rightarrow> otype" where
  "sarrow_type [] \<tau> = \<tau>"
| "sarrow_type (\<sigma> # \<sigma>s) \<tau> = Arr \<sigma> (sarrow_type \<sigma>s \<tau>)"

fun slam_vec :: "otype list \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "slam_vec [] A = A"
| "slam_vec (\<sigma> # \<sigma>s) A = SLam \<sigma> (slam_vec \<sigma>s A)"

definition sabstract_prefix :: "ctx \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "sabstract_prefix \<Delta> A = slam_vec (rev \<Delta>) A"

fun sapp_vec :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm list \<Rightarrow> ('c, 'l) sterm" where
  "sapp_vec F [] = F"
| "sapp_vec F (A # As) = sapp_vec (SApp F A) As"

fun sraise :: "nat \<Rightarrow> ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm" where
  "sraise 0 A = A"
| "sraise (Suc n) A = srename Suc (sraise n A)"

definition sfresh_vars :: "nat \<Rightarrow> ('c, 'l) sterm list" where
  "sfresh_vars n = map SVar [0..<n]"

lemma srename_identity: "srename id A = A"
proof -
  have lifts: "lift_ren (\<lambda>n. n) = (\<lambda>n. n)" by (rule ext, rename_tac n, case_tac n) simp_all
  have identity: "srename (\<lambda>n. n) A = A"
    by (induction A) (simp_all only: srename.simps lifts)
  show ?thesis using identity by (simp only: id_def)
qed

lemma srename_closed:
  assumes closed: "sfv A = {}"
  shows "srename r A = A"
proof -
  have "srename r A = srename id A" by (rule srename_fv_agreement) (simp add: closed)
  then show ?thesis by (simp only: srename_identity)
qed

lemma sraise_as_rename: "sraise n A = srename (\<lambda>i. n + i) A"
  by (induction n) (simp_all add: srename_comp comp_def srename_identity[unfolded id_def])

lemma sraise_closed:
  "sfv A = {} \<Longrightarrow> sraise n A = A"
  by (simp only: sraise_as_rename, rule srename_closed, assumption)

lemma slam_vec_append: "slam_vec (\<sigma>s @ \<tau>s) A = slam_vec \<sigma>s (slam_vec \<tau>s A)"
  by (induction \<sigma>s) simp_all

lemma sabstract_prefix_empty[simp]: "sabstract_prefix [] A = A"
  by (simp add: sabstract_prefix_def)

lemma sabstract_prefix_snoc:
  "sabstract_prefix (\<Delta> @ [\<sigma>]) A = SLam \<sigma> (sabstract_prefix \<Delta> A)"
  by (simp add: sabstract_prefix_def)

lemma slam_vec_type:
  assumes typed: "has_stype L (rev \<sigma>s @ \<Gamma>) A \<tau>"
  shows "has_stype L \<Gamma> (slam_vec \<sigma>s A) (sarrow_type \<sigma>s \<tau>)"
  using typed
proof (induction \<sigma>s arbitrary: \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  have body: "has_stype L (rev \<sigma>s @ (\<sigma> # \<Gamma>)) A \<tau>"
    using Cons.prems by (simp add: append_assoc)
  have inner: "has_stype L (\<sigma> # \<Gamma>) (slam_vec \<sigma>s A) (sarrow_type \<sigma>s \<tau>)"
    by (rule Cons.IH[where \<Gamma>="\<sigma> # \<Gamma>", OF body])
  show ?case by (simp only: slam_vec.simps sarrow_type.simps) (rule has_stype.Lam[OF inner])
qed

lemma sabstract_prefix_type:
  "has_stype L (\<Delta> @ \<Gamma>) A \<tau> \<Longrightarrow>
    has_stype L \<Gamma> (sabstract_prefix \<Delta> A) (sarrow_type (rev \<Delta>) \<tau>)"
  unfolding sabstract_prefix_def by (rule slam_vec_type) simp

lemma sabstract_prefix_signature:
  "sterm_in_signature \<Sigma> (sabstract_prefix \<Delta> A) = sterm_in_signature \<Sigma> A"
proof -
  have "sterm_in_signature \<Sigma> (slam_vec \<sigma>s A) = sterm_in_signature \<Sigma> A" for \<sigma>s
    by (induction \<sigma>s) simp_all
  then show ?thesis by (simp only: sabstract_prefix_def)
qed

lemma sabstract_prefix_language:
  assumes language: "sterm_in_language L \<Sigma> (\<Delta> @ \<Gamma>) A \<tau>"
  shows "sterm_in_language L \<Sigma> \<Gamma> (sabstract_prefix \<Delta> A) (sarrow_type (rev \<Delta>) \<tau>)"
proof -
  have typed: "has_stype L (\<Delta> @ \<Gamma>) A \<tau>" and sig: "sterm_in_signature \<Sigma> A"
    using language unfolding sterm_in_language_def by blast+
  have abstract_sig: "sterm_in_signature \<Sigma> (sabstract_prefix \<Delta> A)"
    by (simp only: sabstract_prefix_signature sig)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF sabstract_prefix_type[OF typed] abstract_sig])
qed

lemma sabstract_all_type:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
  shows "has_stype L [] (sabstract_prefix \<Gamma> A) (sarrow_type (rev \<Gamma>) \<tau>)"
  by (rule sabstract_prefix_type) (use typed in simp)

lemma sabstract_all_closed:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
  shows "sfv (sabstract_prefix \<Gamma> A) = {}"
proof -
  have bound: "sfv (sabstract_prefix \<Gamma> A) \<subseteq> {..<length ([] :: ctx)}"
    by (rule source_typed_fv_bound[OF sabstract_all_type[OF typed]])
  show ?thesis using bound by simp
qed

lemma sraise_type:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
  shows "has_stype L (\<Delta> @ \<Gamma>) (sraise (length \<Delta>) A) \<tau>"
proof (induction \<Delta>)
  case Nil
  show ?case using typed by simp
next
  case (Cons \<sigma> \<Delta>)
  have shifted: "has_stype L (\<sigma> # (\<Delta> @ \<Gamma>)) (sshift (sraise (length \<Delta>) A)) \<tau>"
    by (rule sshift_preserves_typing[OF Cons.IH])
  show ?case using shifted by (simp only: length_Cons sraise.simps append_Cons sshift_def)
qed

lemma sraise_signature: "sterm_in_signature \<Sigma> (sraise n A) = sterm_in_signature \<Sigma> A"
  by (simp only: sraise_as_rename srename_signature)

lemma sapp_vec_type:
  assumes ft: "has_stype L \<Gamma> F (sarrow_type \<sigma>s \<tau>)"
    and args: "list_all2 (\<lambda>A \<sigma>. has_stype L \<Gamma> A \<sigma>) As \<sigma>s"
  shows "has_stype L \<Gamma> (sapp_vec F As) \<tau>"
  using ft args
proof (induction \<sigma>s arbitrary: F As)
  case Nil
  then show ?case by (cases As) simp_all
next
  case (Cons \<sigma> \<sigma>s)
  from Cons.prems(2) obtain A Bs where eq: "As = A # Bs" and at: "has_stype L \<Gamma> A \<sigma>"
    and tail: "list_all2 (\<lambda>A \<sigma>. has_stype L \<Gamma> A \<sigma>) Bs \<sigma>s" by (cases As) auto
  have ft: "has_stype L \<Gamma> F (Arr \<sigma> (sarrow_type \<sigma>s \<tau>))" using Cons.prems(1) by simp
  have app: "has_stype L \<Gamma> (SApp F A) (sarrow_type \<sigma>s \<tau>)" by (rule has_stype.App[OF ft at])
  show ?case using Cons.IH[where F="SApp F A" and As=Bs, OF app tail] by (simp only: eq sapp_vec.simps)
qed

lemma sapp_vec_signature:
  "sterm_in_signature \<Sigma> (sapp_vec F As) \<longleftrightarrow>
    sterm_in_signature \<Sigma> F \<and> (\<forall>A \<in> set As. sterm_in_signature \<Sigma> A)"
  by (induction As arbitrary: F) auto

lemma srename_sapp_vec:
  "srename r (sapp_vec F As) = sapp_vec (srename r F) (map (srename r) As)"
  by (induction As arbitrary: F) simp_all

lemma sreverse_fresh_vars_Suc:
  "rev (sfresh_vars (Suc n)) = SVar n # rev (sfresh_vars n)"
  by (simp add: sfresh_vars_def upt_Suc)

lemma sreverse_fresh_vars_type:
  "list_all2 (\<lambda>A \<sigma>. has_stype L (\<Delta> @ \<Gamma>) A \<sigma>)
    (rev (sfresh_vars (length \<Delta>))) (rev \<Delta>)"
proof -
  have ascending: "list_all2 (\<lambda>A \<sigma>. has_stype L (\<Delta> @ \<Gamma>) A \<sigma>)
    (map SVar [0..<length \<Delta>]) \<Delta>"
  proof (unfold list_all2_conv_all_nth, rule conjI)
    show "length (map SVar [0..<length \<Delta>]) = length \<Delta>" by simp
  next
    show "\<forall>i < length (map SVar [0..<length \<Delta>]).
      has_stype L (\<Delta> @ \<Gamma>) ((map SVar [0..<length \<Delta>]) ! i) (\<Delta> ! i)"
    proof (intro allI impI)
      fix i
      assume bound: "i < length (map SVar [0..<length \<Delta>])"
      have i: "i < length \<Delta>" using bound by simp
      have index: "lookup (\<Delta> @ \<Gamma>) i = Some (\<Delta> ! i)" using i by (simp add: lookup_def nth_append)
      have typed: "has_stype L (\<Delta> @ \<Gamma>) (SVar i) (\<Delta> ! i)" by (rule has_stype.Var[OF index])
      show "has_stype L (\<Delta> @ \<Gamma>) ((map SVar [0..<length \<Delta>]) ! i) (\<Delta> ! i)"
        using typed i by simp
    qed
  qed
  show ?thesis using ascending by (simp only: sfresh_vars_def list_all2_rev)
qed

lemma sfresh_vars_signature:
  "A \<in> set (rev (sfresh_vars n)) \<Longrightarrow> sterm_in_signature \<Sigma> A"
  unfolding sfresh_vars_def by auto

lemma sdeabstract_type:
  assumes typed: "has_stype L (\<Delta> @ \<Gamma>) A \<tau>"
  shows "has_stype L (\<Delta> @ \<Gamma>)
    (sapp_vec (sraise (length \<Delta>) (sabstract_prefix \<Delta> A)) (rev (sfresh_vars (length \<Delta>)))) \<tau>"
  by (rule sapp_vec_type[OF sraise_type[OF sabstract_prefix_type[OF typed]] sreverse_fresh_vars_type])

lemma sdeabstract_signature:
  assumes sig: "sterm_in_signature \<Sigma> A"
  shows "sterm_in_signature \<Sigma>
    (sapp_vec (sraise (length \<Delta>) (sabstract_prefix \<Delta> A)) (rev (sfresh_vars (length \<Delta>))))"
proof (unfold sapp_vec_signature, rule conjI)
  show "sterm_in_signature \<Sigma> (sraise (length \<Delta>) (sabstract_prefix \<Delta> A))"
    by (simp only: sraise_signature sabstract_prefix_signature sig)
  show "\<forall>M \<in> set (rev (sfresh_vars (length \<Delta>))). sterm_in_signature \<Sigma> M"
    by (rule ballI, rule sfresh_vars_signature, assumption)
qed

end
