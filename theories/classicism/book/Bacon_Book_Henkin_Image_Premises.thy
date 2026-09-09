theory Bacon_Book_Henkin_Image_Premises
  imports Bacon_Book_Typed_Witness_Transport
begin

section \<open>The exact image language retains every conditional witness\<close>

definition book_henkin_image_premises where
  "book_henkin_image_premises \<rho> \<Sigma> G S =
    book_typed_name_map \<rho> ` book_henkin_closed_premises \<Sigma> G S"

lemma book_henkin_image_premises_closed:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
  shows "book_closed_formula_set (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G
    (book_henkin_image_premises \<rho> \<Sigma> G S)"
proof (unfold book_closed_formula_set_def, rule ballI)
  fix A
  assume member: "A \<in> book_henkin_image_premises \<rho> \<Sigma> G S"
  obtain B where bm: "B \<in> book_henkin_closed_premises \<Sigma> G S"
    and shape: "A = book_typed_name_map \<rho> B"
    using member unfolding book_henkin_image_premises_def by blast
  have data: "book_theory_formula (book_henkin_full_signature \<Sigma> G) G B \<and> named_fv B = {}"
    by (rule book_closed_formula_set_member[OF book_henkin_closed_premises_closed_set[OF rich language] bm])
  have al: "book_theory_formula (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G A"
    by (simp only: shape; rule book_typed_name_map_language[OF conjunct1[OF data]];
      rule book_typed_image_maps; assumption)
  have closed: "named_fv A = {}" by (simp only: shape book_typed_name_map_fv; rule conjunct2[OF data])
  show "book_theory_formula (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G A \<and>
    named_fv A = {}" by (rule conjI[OF al closed])
qed

lemma book_C_henkin_image_premises_consistent:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
    and injective: "\<And>\<tau>. inj_on (\<rho> \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)"
  shows "book_C_theory_consistent (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G
    (book_henkin_image_premises \<rho> \<Sigma> G S)"
proof -
  have pl: "book_theory_formula (book_henkin_full_signature \<Sigma> G) G A"
    if "A \<in> book_henkin_closed_premises \<Sigma> G S" for A
    by (rule conjunct1[OF book_closed_formula_set_member[
      OF book_henkin_closed_premises_closed_set[OF rich language] that]])
  have pc: "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (book_henkin_closed_premises \<Sigma> G S)"
    by (rule book_C_henkin_closed_premises_consistent[OF rich language consistent])
  show ?thesis unfolding book_henkin_image_premises_def
    using pc book_C_consistent_typed_image_iff[where \<rho>=\<rho>, OF rich injective pl] by blast
qed

lemma book_henkin_image_conditional_witness:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV
      (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "\<exists>d\<in>book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G) \<sigma>.
    book_witness_axiom G \<sigma> F d \<in> book_henkin_image_premises \<rho> \<Sigma> G S"
proof -
  let ?H = "book_henkin_full_signature \<Sigma> G"
  let ?\<Omega> = "book_typed_image_signature \<rho> ?H"
  let ?\<pi> = "book_typed_name_inverse \<rho> ?H"
  let ?F = "book_typed_name_map ?\<pi> F"
  have maps: "\<And>\<tau> d. d \<in> ?\<Omega> \<tau> \<Longrightarrow> ?\<pi> \<tau> d \<in> ?H \<tau>"
    by (rule book_typed_inverse_maps)
  have fl: "book_in_language book_minimal_logical_type UNIV ?H G ?F (Arr \<sigma> Prop)"
    by (rule book_typed_name_map_language[OF predicate maps])
  have fc: "named_fv ?F = {}" by (simp only: book_typed_name_map_fv closed)
  have right: "\<And>\<tau> d. d \<in> ?\<Omega> \<tau> \<Longrightarrow> \<rho> \<tau> (?\<pi> \<tau> d) = d"
    by (rule book_typed_inverse_right)
  have restored: "book_typed_name_map \<rho> ?F = F"
    by (rule book_typed_name_map_roundtrip[where \<rho>="?\<pi>" and \<pi>=\<rho> and \<Sigma>="?\<Omega>",
      OF book_language_signature[OF predicate] right])
  obtain c where cm: "c \<in> ?H \<sigma>"
    and wm: "book_witness_axiom G \<sigma> ?F c \<in> book_henkin_full_premises \<Sigma> G S"
    using book_henkin_full_premises_witness[where S=S, OF fl fc] by blast
  have wc: "named_fv (book_witness_axiom G \<sigma> ?F c) = {}" by (rule book_witness_axiom_closed[OF fc])
  have wclosed: "book_witness_axiom G \<sigma> ?F c \<in> book_henkin_closed_premises \<Sigma> G S"
    using imageI[where f="book_universal_closure G", OF wm]
    by (simp only: book_henkin_closed_premises_def book_universal_closure_of_closed[OF wc])
  have mapped: "book_typed_name_map \<rho> (book_witness_axiom G \<sigma> ?F c) \<in>
    book_henkin_image_premises \<rho> \<Sigma> G S"
    unfolding book_henkin_image_premises_def by (rule imageI[OF wclosed])
  have witness: "book_witness_axiom G \<sigma> F (\<rho> \<sigma> c) \<in> book_henkin_image_premises \<rho> \<Sigma> G S"
    using mapped by (simp only: book_typed_name_map_witness_axiom restored)
  have declared: "\<rho> \<sigma> c \<in> ?\<Omega> \<sigma>" by (rule book_typed_image_maps; rule cm)
  show ?thesis by (rule bexI[where x="\<rho> \<sigma> c"], rule witness, rule declared)
qed

text \<open>
  Every closed predicate in the image language has a preimage obtained
  by choosing inverse names at its occurrence types. The source Henkin
  premises already contain its conditional witness. Mapping that literal
  formula supplies the target witness. This coverage lemma itself needs
  no injectivity; injectivity is used separately to preserve consistency.
\<close>

end
