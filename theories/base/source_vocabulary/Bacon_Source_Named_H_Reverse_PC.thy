theory Bacon_Source_Named_H_Reverse_PC
  imports Bacon_Source_Named_H Bacon_Source_Named_Representation_Reflection
    Bacon_Source_Propositional_Typing Bacon_Source_Propositional_Reindexing
    Bacon_Source_Global_Connective_Language
begin

section \<open>Recovering the languages of occurring propositional atoms\<close>

text \<open>
  If a literal propositional instance P[v] belongs to ℒ(Σ) at type t,
  each atom v(a) occurring in P belongs to that same language at type t.
  Source: PC in Bacon–Dorr Figure 2, p.8, using the literal Figure 1
  connective operators.

  Isabelle representation. The complete instance is typed in one finite
  prefix. The existing finite-instance inversion supplies each occurring
  atom's language there, and the prefix-to-global lemma returns it to G.
  No condition is inferred or imposed on unused values of v.
\<close>

lemma paper_global_prop_instance_atoms:
  assumes language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_prop_instance v P) Prop"
    and member: "a \<in> sprop_atoms P"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (v a) Prop"
proof -
  let ?m = "source_free_bound (paper_prop_instance v P)"
  have finite_language: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m)
    (paper_prop_instance v P) Prop"
    by (rule source_language_in_prefix[OF language order_refl])
  have atoms: "\<forall>b\<in>sprop_atoms P.
    sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) (v b) Prop"
    by (rule iffD1[OF paper_prop_instance_language_iff finite_language])
  have atom_language: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) (v a) Prop"
    by (rule bspec[OF atoms member])
  show ?thesis by (rule source_prefix_language_to_global[OF atom_language])
qed

section \<open>A source PC instance has a native named PC preimage\<close>

text \<open>
  If M is a PC instance, there is a native named H theorem N with
  enc(N) = M. Source: the PC rule alone, Bacon–Dorr Figure 2, p.8.

  Isabelle representation. Keep the same finite Boolean template and
  choose a typed named representative for each occurring atom. Template
  congruence needs encoding agreement only on those atoms. The native
  instance then encodes literally to M; checked language reflection gives
  its whole-formula guard, and native PC yields its theoremhood.

  Status. This is the PC case of reverse proof preservation only.
  It assumes rich G but no countability of nonlogical names, named
  completeness, semantic model, or source H theoremhood beyond the
  independently defined PC predicate.
\<close>

theorem paper_named_PC_preimage:
  assumes pc: "paper_global_PC \<Sigma> G M" and rich: "sg_rich G"
  shows "\<exists>N. paper_named_H \<Sigma> G N \<and> named_to_source G [] N = M"
proof -
  have language: "sgterm_in_language paper_logical_type \<Sigma> G M Prop"
    using pc unfolding paper_global_PC_def by (rule conjunct1)
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and source_eq: "M = paper_prop_instance v P"
    using conjunct2[OF pc[unfolded paper_global_PC_def]] by (elim exE conjE)
  have instance_language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_prop_instance v P) Prop"
    using language by (simp only: source_eq)
  let ?w = "\<lambda>a. SOME N. named_in_language paper_logical_type \<Sigma> G N Prop \<and>
    named_to_source G [] N = v a"
  have representatives: "named_in_language paper_logical_type \<Sigma> G (?w a) Prop \<and>
    named_to_source G [] (?w a) = v a" if member: "a \<in> sprop_atoms P" for a
  proof (rule someI_ex)
    have atom_language: "sgterm_in_language paper_logical_type \<Sigma> G (v a) Prop"
      by (rule paper_global_prop_instance_atoms[OF instance_language member])
    show "\<exists>N. named_in_language paper_logical_type \<Sigma> G N Prop \<and>
      named_to_source G [] N = v a"
      by (rule source_named_representation_exists[OF atom_language rich])
  qed
  let ?N = "named_paper_prop_instance G ?w P"
  have atom_encoding: "named_to_source G [] (?w a) = v a"
    if "a \<in> sprop_atoms P" for a
    by (rule conjunct2[OF representatives[OF that]])
  have instances_agree: "paper_prop_instance (\<lambda>a. named_to_source G [] (?w a)) P =
    paper_prop_instance v P"
    by (rule paper_prop_instance_cong[where P=P
      and v="\<lambda>a. named_to_source G [] (?w a)" and w=v, OF atom_encoding])
  have encoded: "named_to_source G [] ?N = M"
    by (rule trans[OF named_paper_prop_instance_encoding[where ns="[]" and v="?w" and P=P, OF rich]
      trans[OF instances_agree sym[OF source_eq]]])
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] ?N) Prop"
    using language by (simp only: encoded)
  have native_language: "named_in_language paper_logical_type \<Sigma> G ?N Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have native_pc: "named_PC \<Sigma> G ?N" by (rule named_PC_instance[OF taut native_language])
  have native: "paper_named_H \<Sigma> G ?N" by (rule paper_named_H.PC[OF native_pc])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF native encoded])
qed

end
