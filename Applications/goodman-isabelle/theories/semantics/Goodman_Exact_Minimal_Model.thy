theory Goodman_Exact_Minimal_Model
  imports Goodman_Exact_Logical_Values Goodman_Exact_Named_Conversion
    "Bacon_Book_Environment_Development.Bacon_Book_H_Soundness"
begin

section \<open>Bacon's exact carriers form an independent minimal-language model\<close>

context pp_e_constants
begin

theorem gi_exact_book_minimal_model:
  assumes rich: "sg_rich G"
  shows "book_full_minimal_model gi_exact_domain gi_exact_app \<Sigma> G
    (gi_exact_named_denote C G) (gi_exact_valuation w) gi_exact_logical_value"
proof -
  interpret Book: book_full_environment gi_exact_domain gi_exact_app
      book_minimal_logical_type UNIV \<Sigma> G "gi_exact_named_denote C G"
    by (rule gi_exact_book_full_environment[OF rich])
  have logicals: "Book.book_closed_value (book_minimal_logical_type l)
    (NLogical l) (gi_exact_logical_value l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
      (NLogical l :: string book_named_term) (book_minimal_logical_type l)"
      by (rule book_language_Logical; simp)
    have witness: "\<exists>g. book_env_typed gi_exact_domain G g \<and>
      gi_exact_named_denote C G g (NLogical l) = gi_exact_logical_value l"
      by (rule gi_exact_logical_value_witness)
    show ?thesis unfolding Book.book_closed_value_def using language witness by simp
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def,
      rule conjI[OF Book.book_full_environment_axioms], unfold_locales)
    fix l
    show "Book.book_closed_value (book_minimal_logical_type l) (NLogical l) (gi_exact_logical_value l)"
      by (rule logicals)
  next
    fix p q assume p: "p \<in> gi_exact_domain Prop" and q: "q \<in> gi_exact_domain Prop"
    show "gi_exact_valuation w
      (gi_exact_app Prop Prop (gi_exact_app Prop (Arr Prop Prop) (gi_exact_logical_value SImp) p) q)
      = (gi_exact_valuation w p \<longrightarrow> gi_exact_valuation w q)"
      by (rule gi_exact_implication_truth[OF p q])
  next
    fix \<sigma> f assume f: "f \<in> gi_exact_domain (Arr \<sigma> Prop)"
    show "gi_exact_valuation w (gi_exact_app (Arr \<sigma> Prop) Prop (gi_exact_logical_value (SBAll \<sigma>)) f)
      = (\<forall>a\<in>gi_exact_domain \<sigma>. gi_exact_valuation w (gi_exact_app \<sigma> Prop f a))"
      by (rule gi_exact_forall_truth[OF f])
  next
    show "\<exists>p\<in>gi_exact_domain Prop. \<not> gi_exact_valuation w p"
      by (rule gi_exact_false_proposition)
  qed
qed

theorem gi_exact_book_H_sound:
  assumes rich: "sg_rich G" and derivation: "book_H \<Sigma> G A"
  shows "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) A"
  by (rule book_full_minimal_model.book_H_soundness[OF gi_exact_book_minimal_model[OF rich] rich derivation])

corollary gi_exact_book_H_at_world:
  assumes rich: "sg_rich G" and derivation: "book_H \<Sigma> G A"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_holds (gi_exact_named_denote C G g A) w"
  using book_formula_validE[OF gi_exact_book_H_sound[OF rich derivation] typed]
  by (simp only: gi_exact_valuation_def)

end

text \<open>
  The result is the independent full minimal-language general model at
  each arbitrary world, on Bacon's exact restricted carriers. It is not
  yet the Chapter 18 future-pair graph representation. H soundness follows
  from its checked general theorem. Full-C/CEV+ global soundness still
  needs native MF and global PE; closed-logical-stock correspondence also
  remains separate. The pp_e_constants and HOL–ZF qualifications remain.
\<close>

end
