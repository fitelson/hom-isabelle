theory Goodman_T9_Native_Conclusion
  imports Goodman_T9_L2_Semantics Goodman_T9_Cardinal
begin

unbundle cardinal_syntax

section \<open>Extract a typed witness from the actual existential formula\<close>

lemma gi_T9_exists_fun_prime_vocabulary:
  "consts_of pp_exists_fun_prime \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_exists_fun_prime_def pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_by_def consts_of_rename)

lemma gi_T9_native_exists_fun_prime_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "book_theory_formula gb_signature G (gi_to_book G [] k pp_exists_fun_prime)"
  by (rule gi_to_book_language[OF rich typed_pp_exists_fun_prime _ gi_exists_fun_prime_admitted[OF names]]; simp)

context pp_e_constants
begin

theorem gi_T9_exists_fun_prime_formula_root_iff:
  "pp_e_holds (pp_e_eval C \<rho> pp_exists_fun_prime) [] \<longleftrightarrow>
    (\<exists>r. Elem r (pp_e_domain Prop) \<and> pp_e_holds (gi_T9_J_value C \<acute> r) [])"
proof -
  have clause: "pp_e_holds (pp_e_eval C (extend_env r \<rho>) (pp_fun_prime (Var 0))) []
      \<longleftrightarrow> pp_e_holds (gi_T9_J_value C \<acute> r) []"
    if rm: "Elem r (pp_e_domain Prop)" for r
  proof -
    have environment: "pp_e_env_typed [Prop] (extend_env r \<rho>)"
      by (rule pp_e_env_typed_extend[OF pp_e_empty_env_typed rm])
    have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
    show ?thesis using gi_T9_fun_prime_formula_holds[OF typed environment, where w="[]"] by simp
  qed
  show ?thesis
  proof
    assume truth: "pp_e_holds (pp_e_eval C \<rho> pp_exists_fun_prime) []"
    have original: "\<exists>r. Elem r (pp_e_domain Prop) \<and>
      pp_e_holds (pp_e_eval C (extend_env r \<rho>) (pp_fun_prime (Var 0))) []"
      using truth by (simp only: pp_exists_fun_prime_def pp_e_eval_Exists_holds)
    then obtain r where rm: "Elem r (pp_e_domain Prop)"
      and body: "pp_e_holds (pp_e_eval C (extend_env r \<rho>) (pp_fun_prime (Var 0))) []" by blast
    have jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []" using body clause[OF rm] by blast
    show "\<exists>r. Elem r (pp_e_domain Prop) \<and> pp_e_holds (gi_T9_J_value C \<acute> r) []"
      by (rule exI[where x=r], rule conjI[OF rm jr])
  next
    assume witness: "\<exists>r. Elem r (pp_e_domain Prop) \<and> pp_e_holds (gi_T9_J_value C \<acute> r) []"
    then obtain r where rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []" by blast
    have body: "pp_e_holds (pp_e_eval C (extend_env r \<rho>) (pp_fun_prime (Var 0))) []"
      using jr clause[OF rm] by blast
    have original: "\<exists>r. Elem r (pp_e_domain Prop) \<and>
      pp_e_holds (pp_e_eval C (extend_env r \<rho>) (pp_fun_prime (Var 0))) []"
      by (rule exI[where x=r], rule conjI[OF rm body])
    show "pp_e_holds (pp_e_eval C \<rho> pp_exists_fun_prime) []"
      using original by (simp only: pp_exists_fun_prime_def pp_e_eval_Exists_holds)
  qed
qed

theorem gi_T9_native_exists_fun_prime_root_witness:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and truth: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "\<exists>r. Elem r (pp_e_domain Prop) \<and> pp_e_holds (gi_T9_J_value C \<acute> r) []"
proof -
  have denotation: "gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime) =
    pp_e_eval C pp_e_closed_env pp_exists_fun_prime"
    by (rule gi_exact_goodman_closed_denotation_translation[OF rich typed_pp_exists_fun_prime typed
      names gi_T9_exists_fun_prime_vocabulary])
  have source: "pp_e_holds (pp_e_eval C pp_e_closed_env pp_exists_fun_prime) []"
    using truth by (simp only: denotation gi_exact_valuation_def)
  show ?thesis using source by (simp only: gi_T9_exists_fun_prime_formula_root_iff)
qed

end

section \<open>T9 with native formula inputs and no abstract coding assumptions\<close>

context gi_T9_native_purity
begin

theorem gi_T9_native_formula_counting_chain:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_pure C gb_unary|"
    and "|gi_T9_root_pure C gb_unary| \<le>o |gi_T9_kinds C \<times> gi_T9_root_group C|"
proof -
  have semantic_l2: "gi_T9_root_L2 C" by (rule gi_T9_native_L2_implies_root_L2[OF rich names typed l2])
  obtain r where rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    using gi_T9_native_exists_fun_prime_root_witness[OF rich names typed exists_fp] by blast
  show "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_pure C gb_unary|"
    by (rule gi_T9_powerset_kinds_le_pure[OF pc semantic_l2 rm jr])
  show "|gi_T9_root_pure C gb_unary| \<le>o |gi_T9_kinds C \<times> gi_T9_root_group C|"
    by (rule gi_T9_pure_le_kinds_times_group)
qed

theorem gi_T9_native_formula_counting_bound:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_kinds C \<times> gi_T9_root_group C|"
  by (rule ordLeq_transitive[OF gi_T9_native_formula_counting_chain(1)[OF assms]
    gi_T9_native_formula_counting_chain(2)[OF assms]])

theorem gi_T9_native_formula_cardinal_dichotomy:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "finite (gi_T9_kinds C) \<or> |Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  by (rule gi_T9_product_power_dichotomy[OF gi_T9_native_formula_counting_bound[OF assms]])

corollary gi_T9_native_formula_infinite_kinds_bound:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
    and infinite_kinds: "infinite (gi_T9_kinds C)"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  using gi_T9_native_formula_cardinal_dichotomy[OF pc names typed l2 exists_fp] infinite_kinds by blast

end

text \<open>
  The conclusion concerns the actual root-pure exact unary values, their
  right-composition equivalence classes and their pure two-sided inverses.
  L2 and ∃fun′ are inputs as actual translated native formulas, rather than
  unattached semantic postulates. The locale retains a typed C on Bacon's
  exact carriers, richness, and global validity of the native logical
  purity/application/PP core.

  Full external unary PC remains explicit: its selectors cover every HOL
  subset of the root-pure unary values. No replacement by merely definable
  or Henkin-representable subsets is made. This is a conditional theorem
  for the stated exact-carrier interpretation class, not a claim about all
  arbitrary Henkin model interfaces, a PC derivation, or model existence.
  The fixed generic interpretation is not asserted to satisfy the extra
  L2/PP/PC assumptions. The last corollary additionally assumes infinite
  kinds; it does not infer infinitude from the counting inequality alone.
\<close>

end
