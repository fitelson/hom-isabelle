theory Bacon_Source_BBK_Interface
  imports Bacon_Source_Propositional
begin

section \<open>Independent first-class BBK clauses in finite variable frames\<close>

text \<open>
  M = ⟨D, ⟦·⟧, V⟩ interprets the first-class paper language. The domains
  Dσ are nonempty, application respects denotation, βη conversion preserves
  denotation, and V supplies the truth clauses for ¬, ∧, ∨, ∀σ, ∃σ, and =σ.
  Source: Bacon–Dorr Definition 3.1, pp.43–44. In its quantifier clauses
  the printed Aσ is read as the previously specified model domain Mσ.

  Representation: terms are paper_term, not pterm. The interpretation and
  truth predicates below are independently declared, not defined by syntax
  translation or target validity. A finite frame Γ specifies the types of
  free de Bruijn slots; pbbk_env_typed is only the shared assignment predicate.
  Quantification applies an arbitrary predicate F to a fresh slot zero.

  Scope: these are the finite-frame counterparts of Definition 3.1's
  clauses. The paper uses adequate assignments to named variables. Their
  equivalence to this representation remains a separate obligation. In
  particular, the renaming-coherence extension below is not silently included
  among the paper's listed clauses. Neither locale asserts model existence,
  Functionality, full function spaces, or the book's Leibniz-identity semantics.
  The subsequent Bacon_Source_BBK_Renaming_Derived theorem proves that
  coherence follows from the weaker structure fields, even for noninjective
  type-respecting maps. Thus the extension imposes no additional finite-frame
  model condition; the named/adequate-assignment and Γ-erasure bridges remain
  separate obligations.
\<close>

locale paper_db_bbk_structure =
  fixes signature :: "'c ssignature"
    and domain :: "otype \<Rightarrow> 'v set"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool"
  assumes domain_nonempty: "domain \<sigma> \<noteq> {}"
    and denote_type:
      "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma> \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g A \<in> domain \<sigma>"
    and denote_var:
      "lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       denote g (SVar n) = g n"
    and denote_application_cong:
      "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> \<tau>) \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Gamma> A \<sigma> \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Delta> H (Arr \<sigma> \<tau>) \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Delta> B \<sigma> \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow> pbbk_env_typed domain \<Delta> h \<Longrightarrow>
       denote g F = denote h H \<Longrightarrow> denote g A = denote h B \<Longrightarrow>
       denote g (SApp F A) = denote h (SApp H B)"
    and denote_locality:
      "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma> \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Delta> A \<sigma> \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow> pbbk_env_typed domain \<Delta> h \<Longrightarrow>
       (\<And>n. n \<in> sfv A \<Longrightarrow> g n = h n) \<Longrightarrow> denote g A = denote h A"
    and denote_beta_eta:
      "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<sigma> A B \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g A = denote g B"
    and valuation_neg:
      "sterm_in_language paper_logical_type signature \<Gamma> A Prop \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (paper_not A)) = (\<not> valuation (denote g A))"
    and valuation_conj:
      "sterm_in_language paper_logical_type signature \<Gamma> A Prop \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Gamma> B Prop \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (paper_and A B)) =
         (valuation (denote g A) \<and> valuation (denote g B))"
    and valuation_disj:
      "sterm_in_language paper_logical_type signature \<Gamma> A Prop \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Gamma> B Prop \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (paper_or A B)) =
         (valuation (denote g A) \<or> valuation (denote g B))"
    and valuation_forall:
      "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop) \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (SApp (SLogical (SAll \<sigma>)) F)) =
         (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (SApp (sshift F) (SVar 0))))"
    and valuation_exists:
      "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop) \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (SApp (SLogical (SEx \<sigma>)) F)) =
         (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (SApp (sshift F) (SVar 0))))"
    and valuation_identity:
      "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma> \<Longrightarrow>
       sterm_in_language paper_logical_type signature \<Gamma> B \<sigma> \<Longrightarrow>
       pbbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) =
         (denote g A = denote g B)"
begin

definition paper_db_satisfies :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_db_satisfies g A \<longleftrightarrow> valuation (denote g A)"

definition paper_db_valid :: "ctx \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_db_valid \<Gamma> A \<longleftrightarrow>
    sterm_in_language paper_logical_type signature \<Gamma> A Prop \<and>
    (\<forall>g. pbbk_env_typed domain \<Gamma> g \<longrightarrow> paper_db_satisfies g A)"

lemma paper_db_closed_denotation:
  assumes language: "sterm_in_language paper_logical_type signature [] A \<sigma>"
    and closed: "sfv A = {}"
  shows "denote g A = denote h A"
  by (rule denote_locality[OF language language pbbk_env_empty pbbk_env_empty])
    (simp add: closed)

end

section \<open>The separate de Bruijn coherence obligation\<close>

locale paper_db_bbk_model = paper_db_bbk_structure +
  assumes denote_rename:
    "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma> \<Longrightarrow>
     inj r \<Longrightarrow> pbbk_env_typed domain \<Delta> g \<Longrightarrow>
     (\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>) \<Longrightarrow>
     denote g (srename r A) = denote (\<lambda>n. g (r n)) A"

end
