theory Bacon_Source_ZF_Logical_Values
  imports Bacon_Source_ZF_Powerset_Coding
    Bacon_Source_Vocabulary_Development.Bacon_Source_Syntax
begin

section \<open>The six literal logical values of Definition 3.19\<close>

text \<open>
  At W, the value of ¬ sends ⟨i,p⟩ to out(target i)−p.
  The values of ∧ and ∨ send ⟨i,p⟩, then ⟨j,q⟩, to
  jₜ(p)∩q and jₜ(p)∪q. Quantifiers test 1target(j) in
  α⟨j,a⟩ for every or some a in the target σ-domain.
  Identity sends ⟨i,a⟩, then ⟨j,b⟩, to
  {k:target(j)→V | kσ(jσ(a))=kσ(b)}.
  Source: Definition 3.19 and footnotes 77–78, p.56.

  Representation: these are actual Lambda graphs and separated sets.
  Dρ(W) is a set code and Tρ(i) is transport. compose remains a
  parameter of the common semantic interface, but the six displayed
  clauses do not directly apply it. The first arrow affects the
  relevant target domain, not the choice of a parallel arrow (footnote 77).

  Status: literal values only, without a BBK/action-model premise,
  stock membership, coherence, or soundness assertion. Raw graph app
  is a total HOL operation; meaningful quantifier tests require the
  argument's actual dependent-function graph and legitimate pair inputs.
  We do not change the printed set with an extra graph-validity filter.
  Definition 3.20 totality and footnote 78(ii) logical-stock closure
  remain separate obligations. All results are relative to HOL-ZF.
\<close>

definition paper_ZF_pair_lambda ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    'o \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "paper_ZF_pair_lambda A source target X W b =
    Lambda (paper_ZF_pair_code A source target X W) (\<lambda>z. b (Fst z) (Snd z))"

lemma paper_ZF_pair_lambda_apply:
  assumes pair: "Elem (Opair h x) (paper_ZF_pair_code A source target X W)"
  shows "app (paper_ZF_pair_lambda A source target X W b) (Opair h x) = b h x"
  by (simp only: paper_ZF_pair_lambda_def Lambda_app[OF pair] Fst Snd)

fun paper_ZF_logical_value ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    ('o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> paper_logical \<Rightarrow> ZF" where
  "paper_ZF_logical_value A source target compose identity D T W SNot =
    paper_ZF_pair_lambda A source target (D Prop) W
      (\<lambda>i p. Sep (paper_ZF_outgoing_code A source (target i)) (\<lambda>j. \<not> Elem j p))"
| "paper_ZF_logical_value A source target compose identity D T W SAnd =
    paper_ZF_pair_lambda A source target (D Prop) W
      (\<lambda>i p. paper_ZF_pair_lambda A source target (D Prop) (target i)
        (\<lambda>j q. Sep (T Prop j p) (\<lambda>k. Elem k q)))"
| "paper_ZF_logical_value A source target compose identity D T W SOr =
    paper_ZF_pair_lambda A source target (D Prop) W
      (\<lambda>i p. paper_ZF_pair_lambda A source target (D Prop) (target i)
        (\<lambda>j q. union (T Prop j p) q))"
| "paper_ZF_logical_value A source target compose identity D T W (SAll \<sigma>) =
    paper_ZF_pair_lambda A source target (D (Arr \<sigma> Prop)) W
      (\<lambda>i F. Sep (paper_ZF_outgoing_code A source (target i))
        (\<lambda>j. \<forall>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a))))"
| "paper_ZF_logical_value A source target compose identity D T W (SEx \<sigma>) =
    paper_ZF_pair_lambda A source target (D (Arr \<sigma> Prop)) W
      (\<lambda>i F. Sep (paper_ZF_outgoing_code A source (target i))
        (\<lambda>j. \<exists>a\<in>explode (D \<sigma> (target j)). Elem (identity (target j)) (app F (Opair j a))))"
| "paper_ZF_logical_value A source target compose identity D T W (SEq \<sigma>) =
    paper_ZF_pair_lambda A source target (D \<sigma>) W
      (\<lambda>i a. paper_ZF_pair_lambda A source target (D \<sigma>) (target i)
        (\<lambda>j b. Sep (paper_ZF_outgoing_code A source (target j))
          (\<lambda>k. T \<sigma> k (T \<sigma> j a) = T \<sigma> k b)))"

end
