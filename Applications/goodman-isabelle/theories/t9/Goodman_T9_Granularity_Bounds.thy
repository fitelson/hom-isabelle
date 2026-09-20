theory Goodman_T9_Granularity_Bounds
  imports Goodman_T9_Infinitude "HOL-Library.Countable_Set_Type"
begin
unbundle cardinal_syntax
context gi_T9_native_purity
begin

theorem gi_T9_kind_sized_group_impossible:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
    and ceiling: "|gi_T9_root_group C| \<le>o |gi_T9_kinds C|"
  shows False
proof -
  have lower: "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
    by (rule gi_T9_native_formula_exponential_group_bound[OF pc names typed l2 fp])
  have impossible: "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_kinds C|"
    by (rule ordLeq_transitive[OF lower ceiling])
  show False using card_of_Pow[of "gi_T9_kinds C"] impossible not_ordLess_ordLeq by blast
qed

theorem gi_T9_kind_bounded_descriptions_impossible:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
    and injective: "inj_on describe (gi_T9_root_group C)"
    and range: "image describe (gi_T9_root_group C) \<subseteq> D"
    and ceiling: "|D| \<le>o |gi_T9_kinds C|"
  shows False
proof -
  have description_bound: "|gi_T9_root_group C| \<le>o |D|" using injective range card_of_ordLeq by blast
  have group_bound: "|gi_T9_root_group C| \<le>o |gi_T9_kinds C|"
    by (rule ordLeq_transitive[OF description_bound ceiling])
  show False by (rule gi_T9_kind_sized_group_impossible[OF pc names typed l2 fp group_bound])
qed

theorem gi_T9_countable_group_impossible:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and fp: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
    and countable: "countable (gi_T9_root_group C)"
  shows False
proof -
  have many: "infinite (gi_T9_kinds C)" by (rule gi_T9_native_formula_infinitely_many_kinds[OF pc names typed l2 fp])
  have group_nat: "|gi_T9_root_group C| \<le>o |UNIV :: nat set|"
    using countable unfolding countable_card_of_nat .
  have nat_kinds: "|UNIV :: nat set| \<le>o |gi_T9_kinds C|"
    using many unfolding infinite_iff_card_of_nat .
  have bound: "|gi_T9_root_group C| \<le>o |gi_T9_kinds C|"
    by (rule ordLeq_transitive[OF group_nat nat_kinds])
  show False by (rule gi_T9_kind_sized_group_impossible[OF pc names typed l2 fp bound])
qed

end
text \<open>
  Attack 2's cardinal ceilings now concern the actual exact pure group
  and kinds. No ceiling or countability is derived from the background.
  Full external PC and the native PP core remain assumptions, alongside
  actual L2 and ∃fun′ inputs. This does not settle PP consistency.
\<close>
end
