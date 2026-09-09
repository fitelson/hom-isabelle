theory Bacon_C_Zeta_Permutation
  imports "Bacon_C_Equivalence_Development.Bacon_C_Rule_Equivalence"
    "Bacon_Classicism.Bacon_Clean_Canonical_Base"
begin

section \<open>Reconciling the ascending ζ variables with source-order Equivalence\<close>

text \<open>
  The older ζ body applies F,G to ascending de Bruijn slots in σs,Γ.
  Reverse the fresh prefix while fixing every ambient slot.  The resulting
  context is rev σs,Γ and the argument list is descending, exactly as
  required by the source-order Rule of Equivalence.  Thus the represented
  ζ rule is admissible in C, including mixed types and the empty prefix.
  Source comparison: Bacon's Rule of Equivalence and Bacon--Dorr Appendix A.

  Isabelle representation.  CEV_reverse_prefix reverses indices below n
  and fixes indices at least n.  The only reused old-work theorem in the
  logical bridge is C_proves_rename from Bacon_Clean_Canonical_Base:
  its proof is induction on C_proves, with no model or locale premise.
  That historical theory has broader transitive imports; none of its
  semantic or completeness results is a mathematical premise here.
  Status.  This adapter is deliberately outside the C-only reconstruction.
  No CE/CEV theorem is used to prove closure of C.
\<close>

definition CEV_reverse_prefix :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "CEV_reverse_prefix n i = (if i < n then n - Suc i else i)"

lemma CEV_reverse_prefix_involution:
  "CEV_reverse_prefix n (CEV_reverse_prefix n i) = i"
proof (cases "i < n")
  case True
  have bound: "n - Suc i < n" using True by arith
  have twice: "n - Suc (n - Suc i) = i" using True by arith
  show ?thesis by (simp add: CEV_reverse_prefix_def True bound twice)
next
  case False
  show ?thesis by (simp add: CEV_reverse_prefix_def False)
qed

lemma CEV_reverse_prefix_lookup:
  assumes index: "lookup (\<sigma>s @ \<Gamma>) i = Some \<tau>"
  shows "lookup (rev \<sigma>s @ \<Gamma>) (CEV_reverse_prefix (length \<sigma>s) i) = Some \<tau>"
proof (cases "i < length \<sigma>s")
  case True
  let ?n = "length \<sigma>s"
  let ?j = "?n - Suc i"
  have reversed_bound: "?j < ?n" using True by arith
  have total_bound: "?j < ?n + length \<Gamma>" using reversed_bound by arith
  have twice: "?n - Suc ?j = i" using True by arith
  have source_nth: "\<sigma>s ! i = \<tau>"
    using index True by (auto simp: lookup_def nth_append split: if_splits)
  have target_nth: "rev \<sigma>s ! ?j = \<tau>"
    using reversed_bound source_nth by (simp add: rev_nth twice)
  show ?thesis using True reversed_bound total_bound target_nth
    by (auto simp: lookup_def CEV_reverse_prefix_def nth_append split: if_splits)
next
  case False
  show ?thesis using index False
    by (auto simp: lookup_def CEV_reverse_prefix_def nth_append split: if_splits)
qed

lemma CEV_reverse_prefix_arguments:
  "map (rename (CEV_reverse_prefix n)) (fresh_vars n) = rev (fresh_vars n)"
proof (rule nth_equalityI)
  show "length (map (rename (CEV_reverse_prefix n)) (fresh_vars n)) = length (rev (fresh_vars n))"
    by simp
next
  fix i
  assume index: "i < length (map (rename (CEV_reverse_prefix n)) (fresh_vars n))"
  have bound: "i < n" using index by (simp add: fresh_vars_def)
  have reversed_bound: "n - Suc i < n" using bound by arith
  show "map (rename (CEV_reverse_prefix n)) (fresh_vars n) ! i = rev (fresh_vars n) ! i"
    using bound reversed_bound by (simp add: fresh_vars_def CEV_reverse_prefix_def rev_nth)
qed

lemma CEV_shift_ren_zero:
  "shift_ren n 0 = (\<lambda>i. n + i)"
  by (rule ext) (simp add: shift_ren_def add.commute)

lemma CEV_reverse_prefix_shifted:
  "rename (CEV_reverse_prefix n) (shift_by n F) = shift_by n F"
  by (simp only: shift_by_def CEV_shift_ren_zero C_Church_rename_comp;
    simp add: comp_def CEV_reverse_prefix_def)

lemma CEV_shift_by_is_vector_raise:
  "shift_by n F = C_vector_raise n F"
  by (simp only: shift_by_def CEV_shift_ren_zero C_vector_raise_as_rename)

lemma CEV_rename_app_vec:
  "rename r (app_vec F xs) = app_vec (rename r F) (map (rename r) xs)"
  by (induction xs arbitrary: F) simp_all

lemma CEV_zeta_reverse_prefix:
  "rename (CEV_reverse_prefix (length \<sigma>s)) (zeta_body \<sigma>s F G) =
    (app_vec (C_vector_raise (length \<sigma>s) F) (rev (fresh_vars (length \<sigma>s)))
      \<longleftrightarrow>\<^sub>o
     app_vec (C_vector_raise (length \<sigma>s) G) (rev (fresh_vars (length \<sigma>s))))"
  by (simp only: zeta_body_def rename.simps CEV_rename_app_vec CEV_reverse_prefix_shifted
    CEV_reverse_prefix_arguments; simp only: CEV_shift_by_is_vector_raise)

subsection \<open>The sole old-work proof transport and the admissible ζ rule\<close>

lemma C_zeta_source_order_premise:
  assumes premise: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>C zeta_body \<sigma>s F G"
  shows "rev \<sigma>s @ \<Gamma> \<turnstile>\<^sub>C
    (app_vec (C_vector_raise (length (rev \<sigma>s)) F) (rev (fresh_vars (length (rev \<sigma>s))))
      \<longleftrightarrow>\<^sub>o
     app_vec (C_vector_raise (length (rev \<sigma>s)) G) (rev (fresh_vars (length (rev \<sigma>s)))))"
proof -
  have renamed: "rev \<sigma>s @ \<Gamma> \<turnstile>\<^sub>C
    rename (CEV_reverse_prefix (length \<sigma>s)) (zeta_body \<sigma>s F G)"
  proof (rule C_proves_rename[OF premise])
    fix i \<tau>
    assume index: "lookup (\<sigma>s @ \<Gamma>) i = Some \<tau>"
    show "lookup (rev \<sigma>s @ \<Gamma>) (CEV_reverse_prefix (length \<sigma>s) i) = Some \<tau>"
      by (rule CEV_reverse_prefix_lookup[OF index])
  qed
  show ?thesis using renamed by (simp only: CEV_zeta_reverse_prefix length_rev)
qed

theorem C_zeta_rule:
  assumes F: "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G: "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and premise: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>C zeta_body \<sigma>s F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type \<sigma>s Prop) F G"
proof -
  have F_source: "\<Gamma> \<turnstile> F : arrow_type (rev (rev \<sigma>s)) Prop" using F by simp
  have G_source: "\<Gamma> \<turnstile> G : arrow_type (rev (rev \<sigma>s)) Prop" using G by simp
  show ?thesis using C_rule_equivalence[OF F_source G_source C_zeta_source_order_premise[OF premise]]
    by simp
qed

text \<open>
  C_zeta_rule has exactly the typed ζ-body premise used by the existing
  vector presentation.  A separate induction on that presentation's
  derivations can now replace its Equivalence constructor by this C rule.
  This file supplies the permutation and admissible rule only; it does
  not itself claim equality of the C and CEV derivability judgments.
\<close>

end
