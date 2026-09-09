theory Bacon_Source_Named_BBK_Interface
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
begin

section \<open>Independent BBK clauses for named terms and adequate assignments\<close>

text \<open>
  M = ⟨D, ⟦·⟧, V⟩ assigns denotations to named terms under typed
  partial assignments adequate for those terms. The variable stock G has
  infinitely many names of each type, as in Bacon–Dorr §1.1, p.5.
  The model fields transcribe Definition 3.1(i–iii), pp.43–44, for the
  first-class paper basis and full F types. In (iii.d–e), the printed Aσ
  is read as the domain Mσ introduced by the definition.

  No finite-frame model predicate or translation occurs in this definition.
  In particular, no free-renaming or α-invariance field is added. The
  βη field uses literal capture-free β and fresh η under contexts; its
  relation to generated α is a separate proof, not an extra constructor.
  An assignment need only be adequate for the two conversion endpoints,
  not for every intermediate expression in a conversion derivation.
  Conversion may use the universal nonlogical signature internally;
  only its two interpreted endpoints must belong to Σ. A separate
  signature-retraction theorem is required to reuse signature-relative
  conversion when constructing a model.

  Application congruence retains the literal heterogeneous reading of
  (ii.b): the two applications may have different argument and result
  types. No unprinted same-type convention or domain-disjointness premise
  is imposed. Constructions from a same-type applicative interface must
  therefore prove a type-tagging bridge, not merely reuse its field.

  Status: an independent named-model interface, not a model-existence or
  soundness theorem. Its construction from finite-frame models, converse
  interpretation with typed carriers, and named-H correspondence require
  separate proofs. The book's Leibniz-identity general models are distinct.
\<close>

locale paper_named_bbk_model =
  fixes signature :: "'c ssignature" and stock :: sgcontext
    and domain :: "otype \<Rightarrow> 'v set"
    and denote :: "'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool"
  assumes stock_rich: "sg_rich stock"
    and domain_nonempty: "domain \<sigma> \<noteq> {}"
    and denote_type:
      "named_in_language paper_logical_type signature stock A \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       denote g A \<in> domain \<sigma>"
    and denote_var:
      "named_env_typed domain stock g \<Longrightarrow> g n = Some a \<Longrightarrow> denote g (NVar n) = a"
    and denote_application_cong:
      "named_in_language paper_logical_type signature stock F (Arr \<sigma> \<tau>) \<Longrightarrow>
       named_in_language paper_logical_type signature stock A \<sigma> \<Longrightarrow>
       named_in_language paper_logical_type signature stock H (Arr \<upsilon> \<rho>) \<Longrightarrow>
       named_in_language paper_logical_type signature stock B \<upsilon> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_env_typed domain stock h \<Longrightarrow>
       named_adequate g (NApp F A) \<Longrightarrow> named_adequate h (NApp H B) \<Longrightarrow>
       denote g F = denote h H \<Longrightarrow> denote g A = denote h B \<Longrightarrow>
       denote g (NApp F A) = denote h (NApp H B)"
    and denote_locality:
      "named_in_language paper_logical_type signature stock A \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_env_typed domain stock h \<Longrightarrow>
       named_adequate g A \<Longrightarrow> named_adequate h A \<Longrightarrow>
       (\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n) \<Longrightarrow> denote g A = denote h A"
    and denote_beta_eta:
      "named_raw_beta_eta paper_logical_type stock \<sigma> A B \<Longrightarrow>
       named_in_language paper_logical_type signature stock A \<sigma> \<Longrightarrow>
       named_in_language paper_logical_type signature stock B \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> denote g A = denote g B"
    and valuation_neg:
      "named_in_language paper_logical_type signature stock A Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       valuation (denote g (NApp (NLogical SNot) A)) = (\<not> valuation (denote g A))"
    and valuation_conj:
      "named_in_language paper_logical_type signature stock A Prop \<Longrightarrow>
       named_in_language paper_logical_type signature stock B Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> valuation (denote g (NApp (NApp (NLogical SAnd) A) B)) =
       (valuation (denote g A) \<and> valuation (denote g B))"
    and valuation_disj:
      "named_in_language paper_logical_type signature stock A Prop \<Longrightarrow>
       named_in_language paper_logical_type signature stock B Prop \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow> valuation (denote g (NApp (NApp (NLogical SOr) A) B)) =
       (valuation (denote g A) \<or> valuation (denote g B))"
    and valuation_forall:
      "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop) \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g F \<Longrightarrow>
       stock n = \<sigma> \<Longrightarrow> n \<notin> named_fv F \<Longrightarrow>
       valuation (denote g (NApp (NLogical (SAll \<sigma>)) F)) =
       (\<forall>a \<in> domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    and valuation_exists:
      "named_in_language paper_logical_type signature stock F (Arr \<sigma> Prop) \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g F \<Longrightarrow>
       stock n = \<sigma> \<Longrightarrow> n \<notin> named_fv F \<Longrightarrow>
       valuation (denote g (NApp (NLogical (SEx \<sigma>)) F)) =
       (\<exists>a \<in> domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    and valuation_identity:
      "named_in_language paper_logical_type signature stock A \<sigma> \<Longrightarrow>
       named_in_language paper_logical_type signature stock B \<sigma> \<Longrightarrow>
       named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
       named_adequate g B \<Longrightarrow>
       valuation (denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (denote g A = denote g B)"
begin

definition named_satisfies :: "'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "named_satisfies g A \<longleftrightarrow> valuation (denote g A)"

definition named_valid :: "'c paper_named_term \<Rightarrow> bool" where
  "named_valid A \<longleftrightarrow>
    named_in_language paper_logical_type signature stock A Prop \<and>
    (\<forall>g. named_env_typed domain stock g \<longrightarrow> named_adequate g A \<longrightarrow> named_satisfies g A)"

end

end
