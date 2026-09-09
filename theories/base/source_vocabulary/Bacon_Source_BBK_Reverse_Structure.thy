theory Bacon_Source_BBK_Reverse_Structure
  imports Bacon_Source_BBK_Renaming_Derived Bacon_Source_Reverse_Guarded_Conversion
    Bacon_Source_Reverse_Binding
begin

section \<open>Interpreting expanded target terms in a weak source structure\<close>

text \<open>
  Define ⟦M⟧T,g := ⟦back(M)⟧S,g, keeping D and V unchanged.
  Source structural clauses: Bacon–Dorr Definition 3.1(ii.a–d),
  pp.43–44, in the independently specified finite-frame representation.

  Isabelle representation: this context is paper_db_bbk_structure, not
  its renaming-coherent extension. Reverse syntax preserves typing,
  signatures, application, free slots, and guarded conversion. The proved
  paper_db_rename_derived supplies assignment renaming without an extra
  coherence assumption.

  Status: structural fields only; target truth clauses and pbbk_model
  assembly are separate. This is not a named-model equivalence or an
  assertion that an arbitrary target model identifies primitive Imp with
  its material definition. The new target denotation is defined through
  the literal reverse interpretation.
\<close>

context paper_db_bbk_structure
begin

definition paper_reverse_denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c pterm \<Rightarrow> 'v" where
  "paper_reverse_denote g M = denote g (pterm_to_paper M)"

lemma paper_reverse_source_language:
  assumes typed: "has_ptype \<Gamma> M \<sigma>"
    and names: "pterm_in_signature signature M"
  shows "sterm_in_language paper_logical_type signature \<Gamma> (pterm_to_paper M) \<sigma>"
proof -
  have language: "pterm_in_language signature \<Gamma> M \<sigma>"
    unfolding pterm_in_language_def by (rule conjI[OF typed names])
  show ?thesis by (rule pterm_to_paper_language[OF language])
qed

lemma paper_reverse_domain_nonempty:
  "domain \<sigma> \<noteq> {}"
  by (rule domain_nonempty)

lemma paper_reverse_denote_type:
  assumes typed: "has_ptype \<Gamma> M \<sigma>"
    and names: "pterm_in_signature signature M"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_reverse_denote g M \<in> domain \<sigma>"
  unfolding paper_reverse_denote_def
  by (rule denote_type[OF paper_reverse_source_language[OF typed names] env])

lemma paper_reverse_denote_var:
  assumes index: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_reverse_denote g (PVar n) = g n"
  unfolding paper_reverse_denote_def pterm_to_paper.simps
  by (rule denote_var[OF index env])

lemma paper_reverse_denote_application_cong:
  fixes F A H B :: "'c pterm"
  assumes F: "has_ptype \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "has_ptype \<Gamma> A \<sigma>"
    and H: "has_ptype \<Delta> H (Arr \<sigma> \<tau>)"
    and B: "has_ptype \<Delta> B \<sigma>"
    and left_names: "pterm_in_signature signature (PApp F A)"
    and right_names: "pterm_in_signature signature (PApp H B)"
    and env_g: "pbbk_env_typed domain \<Gamma> g"
    and env_h: "pbbk_env_typed domain \<Delta> h"
    and function_eq: "paper_reverse_denote g F = paper_reverse_denote h H"
    and argument_eq: "paper_reverse_denote g A = paper_reverse_denote h B"
  shows "paper_reverse_denote g (PApp F A) = paper_reverse_denote h (PApp H B)"
proof -
  have fs: "pterm_in_signature signature F" using left_names by simp
  have asig: "pterm_in_signature signature A" using left_names by simp
  have hs: "pterm_in_signature signature H" using right_names by simp
  have bs: "pterm_in_signature signature B" using right_names by simp
  note fl = paper_reverse_source_language[OF F fs]
  note al = paper_reverse_source_language[OF A asig]
  note hl = paper_reverse_source_language[OF H hs]
  note bl = paper_reverse_source_language[OF B bs]
  show ?thesis unfolding paper_reverse_denote_def pterm_to_paper.simps
    by (rule denote_application_cong[OF fl al hl bl env_g env_h
      function_eq[unfolded paper_reverse_denote_def] argument_eq[unfolded paper_reverse_denote_def]])
qed

lemma paper_reverse_denote_locality:
  assumes first: "has_ptype \<Gamma> M \<sigma>" and second: "has_ptype \<Delta> M \<sigma>"
    and names: "pterm_in_signature signature M"
    and env_g: "pbbk_env_typed domain \<Gamma> g"
    and env_h: "pbbk_env_typed domain \<Delta> h"
    and agrees: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> g n = h n"
  shows "paper_reverse_denote g M = paper_reverse_denote h M"
proof -
  have source_agreement: "\<And>n. n \<in> sfv (pterm_to_paper M) \<Longrightarrow> g n = h n"
  proof -
    fix n
    assume member: "n \<in> sfv (pterm_to_paper M)"
    have target_member: "n \<in> pbbk_fv M" using member by (simp only: pterm_to_paper_fv)
    show "g n = h n" by (rule agrees[OF target_member])
  qed
  show ?thesis unfolding paper_reverse_denote_def
    by (rule denote_locality[OF paper_reverse_source_language[OF first names]
      paper_reverse_source_language[OF second names] env_g env_h source_agreement])
qed

lemma paper_reverse_denote_beta_eta:
  assumes conversion: "pbeta_eta_equiv_in_signature signature \<Gamma> \<sigma> M N"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_reverse_denote g M = paper_reverse_denote g N"
proof -
  have source: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<sigma>
    (pterm_to_paper M) (pterm_to_paper N)"
    by (rule pterm_to_paper_guarded_conversion[OF conversion])
  show ?thesis unfolding paper_reverse_denote_def by (rule denote_beta_eta[OF source env])
qed

subsection \<open>Target renaming is inherited from a proved weak-structure theorem\<close>

text \<open>
  The target clause asks for injective type-respecting renamings.
  The source structural theorem actually covers all type-respecting maps,
  so the stronger result below requires no injectivity premise.

  Status: a derived property, not use of an assumed denote_rename field.
  Endpoint signatures in the preceding βη lemma are already carried by
  the indexed conversion derivation; no raw unrestricted chain is used.
\<close>

lemma paper_reverse_denote_rename:
  assumes typed: "has_ptype \<Gamma> M \<sigma>" and names: "pterm_in_signature signature M"
    and env: "pbbk_env_typed domain \<Delta> g"
    and types: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "paper_reverse_denote g (prename r M) = paper_reverse_denote (\<lambda>n. g (r n)) M"
proof -
  have source: "sterm_in_language paper_logical_type signature \<Gamma> (pterm_to_paper M) \<sigma>"
    by (rule paper_reverse_source_language[OF typed names])
  have renamed: "denote g (srename r (pterm_to_paper M)) =
    denote (\<lambda>n. g (r n)) (pterm_to_paper M)"
    by (rule paper_db_rename_derived[where \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and r=r and g=g
      and A="pterm_to_paper M", OF source env types])
  show ?thesis using renamed by (simp only: paper_reverse_denote_def pterm_to_paper_rename)
qed

end

end
