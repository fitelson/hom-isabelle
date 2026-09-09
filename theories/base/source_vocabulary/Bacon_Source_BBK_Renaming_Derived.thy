theory Bacon_Source_BBK_Renaming_Derived
  imports Bacon_Source_BBK_Vector_Congruence Bacon_Source_Vector_Mapped_Beta
begin

section \<open>Renaming coherence follows from the weaker finite-frame clauses\<close>

text \<open>
  Let K := λvₙ₋₁.…λv₀.A close all slots of Γ.  Locality identifies
  ⟦K⟧ at the original and renamed assignments.  Each corresponding
  argument variable has the same value; repeated application congruence
  identifies K applied to the two vectors.  The two guarded β equations
  recover A and its renamed form.
  Source role: Definition 3.1(ii.a–d), Bacon--Dorr pp.43–44.

  Isabelle representation.  The proof is in paper_db_bbk_structure,
  without its optional denote_rename field.  The map r is type-respecting
  but need not be injective.  The complete finite frame is abstracted;
  reversed fresh variables preserve mixed argument types.
  Status.  This discharges the finite-frame coherence redundancy
  obligation only.  Named/α, adequate assignments, and Γ-erasure/tagging
  remain separate.  Full F types are used; no R-only result is asserted.
\<close>

lemma paper_db_argument_languages:
  assumes typed: "list_all2 (\<lambda>A \<sigma>. has_stype paper_logical_type \<Gamma> A \<sigma>) As \<sigma>s"
    and names: "\<And>A. A \<in> set As \<Longrightarrow> sterm_in_signature \<Sigma> A"
  shows "list_all2 (\<lambda>A \<sigma>. sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>) As \<sigma>s"
proof (unfold list_all2_conv_all_nth, rule conjI)
  show "length As = length \<sigma>s" by (rule list_all2_lengthD[OF typed])
next
  show "\<forall>i < length As. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (As ! i) (\<sigma>s ! i)"
  proof (intro allI impI)
    fix i
    assume bound: "i < length As"
    have entry_type: "has_stype paper_logical_type \<Gamma> (As ! i) (\<sigma>s ! i)"
      by (rule list_all2_nthD[OF typed bound])
    have entry_names: "sterm_in_signature \<Sigma> (As ! i)" by (rule names[OF nth_mem[OF bound]])
    show "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (As ! i) (\<sigma>s ! i)"
      unfolding sterm_in_language_def by (rule conjI[OF entry_type entry_names])
  qed
qed

context paper_db_bbk_structure
begin

theorem paper_db_rename_derived:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<tau>"
    and env: "pbbk_env_typed domain \<Delta> g"
    and ren: "\<And>i \<sigma>. lookup \<Gamma> i = Some \<sigma> \<Longrightarrow> lookup \<Delta> (r i) = Some \<sigma>"
  shows "denote g (srename r A) = denote (\<lambda>i. g (r i)) A"
proof -
  let ?h = "\<lambda>i. g (r i)"
  let ?K = "sabstract_prefix \<Gamma> A"
  let ?xs = "rev (sfresh_vars (length \<Gamma>)) :: 'c paper_term list"
  let ?ys = "map (srename r) ?xs"
  have env_h: "pbbk_env_typed domain \<Gamma> ?h"
  proof (unfold pbbk_env_typed_def, intro allI impI)
    fix i \<sigma>
    assume index: "lookup \<Gamma> i = Some \<sigma>"
    show "g (r i) \<in> domain \<sigma>" by (rule pbbk_env_lookup[OF env ren[OF index]])
  qed
  have typed: "has_stype paper_logical_type \<Gamma> A \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have closed: "sfv ?K = {}" by (rule sabstract_all_closed[OF typed])
  have K_source: "sterm_in_language paper_logical_type signature \<Gamma> ?K (sarrow_type (rev \<Gamma>) \<tau>)"
    by (rule sabstract_all_language[OF language])
  have K_target: "sterm_in_language paper_logical_type signature \<Delta> ?K (sarrow_type (rev \<Gamma>) \<tau>)"
    by (rule sabstract_all_language[OF language])
  have same_head: "denote ?h ?K = denote g ?K"
    by (rule denote_locality[OF K_source K_target env_h env]) (simp add: closed)
  have xs_types: "list_all2 (\<lambda>X \<sigma>. has_stype paper_logical_type \<Gamma> X \<sigma>) ?xs (rev \<Gamma>)"
    using sreverse_fresh_vars_type[where L=paper_logical_type and \<Delta>=\<Gamma> and \<Gamma>="[]"] by simp
  have xs_languages: "list_all2 (\<lambda>X \<sigma>. sterm_in_language paper_logical_type signature \<Gamma> X \<sigma>) ?xs (rev \<Gamma>)"
    by (rule paper_db_argument_languages[OF xs_types]) (rule sfresh_vars_signature, assumption)
  have ys_types: "list_all2 (\<lambda>X \<sigma>. has_stype paper_logical_type \<Delta> X \<sigma>) ?ys (rev \<Gamma>)"
    by (rule srenamed_fresh_vars_type[OF ren])
  have ys_languages: "list_all2 (\<lambda>X \<sigma>. sterm_in_language paper_logical_type signature \<Delta> X \<sigma>) ?ys (rev \<Gamma>)"
    by (rule paper_db_argument_languages[OF ys_types]) (rule srenamed_fresh_vars_signature, assumption)
  have same_variable: "denote ?h X = denote g (srename r X)" if member: "X \<in> set ?xs" for X
  proof -
    obtain i where bound: "i < length \<Gamma>" and X: "X = SVar i"
      using member unfolding sfresh_vars_def by auto
    have index: "lookup \<Gamma> i = Some (\<Gamma> ! i)" using bound by (simp add: lookup_def)
    have mapped_index: "lookup \<Delta> (r i) = Some (\<Gamma> ! i)" by (rule ren[OF index])
    have original: "denote ?h (SVar i) = g (r i)" by (rule denote_var[OF index env_h])
    have mapped: "denote g (SVar (r i)) = g (r i)" by (rule denote_var[OF mapped_index env])
    show ?thesis using original mapped by (simp only: X srename.simps)
  qed
  have same_arguments: "list_all2 (\<lambda>X Y. denote ?h X = denote g Y) ?xs ?ys"
  proof (unfold list_all2_conv_all_nth, rule conjI)
    show "length ?xs = length ?ys" by simp
  next
    show "\<forall>i < length ?xs. denote ?h (?xs ! i) = denote g (?ys ! i)"
    proof (intro allI impI)
      fix i
      assume bound: "i < length ?xs"
      have entry: "denote ?h (?xs ! i) = denote g (srename r (?xs ! i))"
        by (rule same_variable[OF nth_mem[OF bound]])
      show "denote ?h (?xs ! i) = denote g (?ys ! i)" using entry bound by simp
    qed
  qed
  have same_application: "denote ?h (sapp_vec ?K ?xs) = denote g (sapp_vec ?K ?ys)"
    by (rule paper_db_vector_application_cong[OF K_source K_target xs_languages ys_languages
      env_h env same_head same_arguments])
  have original_beta: "denote ?h (sapp_vec ?K ?xs) = denote ?h A"
    by (rule denote_beta_eta[OF sabstract_all_application_beta[OF language] env_h])
  have mapped_beta: "denote g (sapp_vec ?K ?ys) = denote g (srename r A)"
    by (rule denote_beta_eta[OF sabstract_all_mapped_beta[OF language ren] env])
  have "denote g (srename r A) = denote g (sapp_vec ?K ?ys)" by (rule sym[OF mapped_beta])
  also have "... = denote ?h (sapp_vec ?K ?xs)" by (rule sym[OF same_application])
  also have "... = denote ?h A" by (rule original_beta)
  finally show ?thesis .
qed

end

corollary paper_db_structure_is_model:
  assumes structure_ok: "paper_db_bbk_structure \<Sigma> D J V"
  shows "paper_db_bbk_model \<Sigma> D J V"
proof -
  interpret S: paper_db_bbk_structure \<Sigma> D J V by (rule structure_ok)
  have coherence: "paper_db_bbk_model_axioms \<Sigma> D J"
    unfolding paper_db_bbk_model_axioms_def
    by (blast intro: S.paper_db_rename_derived)
  show ?thesis unfolding paper_db_bbk_model_def by (rule conjI[OF structure_ok coherence])
qed

text \<open>
  The optional injective-renaming extension therefore adds no finite-frame
  structures: the stronger type-respecting renaming theorem already follows
  from the weaker fields.  This does not remove Γ from a named-model
  interpretation or identify different typings of a raw term.
\<close>

end
