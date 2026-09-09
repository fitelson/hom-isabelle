theory Bacon_Source_Relational_Henkin_Name_Stages
  imports Bacon_Source_Relational_Syntax
begin

section \<open>A fixed name carrier supplies every later R witness stage\<close>

text \<open>
  Embed each old name c as Original(c). At stage k+1 add
  Witness(k,σ,F) for every CLOSED R predicate F:σ→t in stage k.
  Source: the expanded Henkin language of Theorem 3.2, footnote 64,
  p.45. The stage number counts rounds, not individual predicates;
  a round need not be countable.

  The nested datatype is strictly positive through the named-term BNF.
  Its F payload belongs to an opaque NONLOGICAL NAME. An occurrence
  NConst(Witness(k,σ,F),σ) remains an atomic object-language constant:
  this construction adds no quotation or object-language term former.
  Names and signatures only are constructed here. No consistency,
  witness-complete theory, interpretation, or model is asserted.
\<close>

datatype 'c paper_R_henkin_name =
    ROriginal 'c
  | RWitness nat otype "('c paper_R_henkin_name) paper_named_term"

primrec paper_R_henkin_signature ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c paper_R_henkin_name) ssignature" where
  "paper_R_henkin_signature \<Sigma> G 0 = (\<lambda>\<sigma>. image ROriginal (\<Sigma> \<sigma>))"
| "paper_R_henkin_signature \<Sigma> G (Suc k) = (\<lambda>\<sigma>.
    paper_R_henkin_signature \<Sigma> G k \<sigma> \<union>
      {RWitness k \<sigma> F |F. named_fv F = {} \<and>
        paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<sigma> Prop)})"

section \<open>Increasing stages preserve exactly the original name declarations\<close>

lemma paper_R_henkin_signature_step:
  "paper_R_henkin_signature \<Sigma> G k \<sigma> \<subseteq> paper_R_henkin_signature \<Sigma> G (Suc k) \<sigma>"
  by (simp only: paper_R_henkin_signature.simps; rule Un_upper1)

theorem paper_R_henkin_signature_mono:
  assumes order: "j \<le> k"
  shows "paper_R_henkin_signature \<Sigma> G j \<sigma> \<subseteq> paper_R_henkin_signature \<Sigma> G k \<sigma>"
  using order
proof (induction k rule: nat.induct[case_names zero Suc])
  case zero
  have same: "j = 0" using zero.prems by simp
  show ?case by (simp only: same; rule subset_refl)
next
  case (Suc k)
  show ?case
  proof (cases "j = Suc k")
    case True
    show ?thesis by (simp only: True; rule subset_refl)
  next
    case False
    have previous: "j \<le> k" using Suc.prems False by arith
    have inclusion: "paper_R_henkin_signature \<Sigma> G j \<sigma> \<subseteq> paper_R_henkin_signature \<Sigma> G k \<sigma>"
      by (rule Suc.IH[OF previous])
    show ?thesis by (rule subset_trans[OF inclusion paper_R_henkin_signature_step])
  qed
qed

theorem paper_R_henkin_signature_original_iff:
  "ROriginal c \<in> paper_R_henkin_signature \<Sigma> G k \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
  by (induction k) auto

corollary paper_R_henkin_signature_original:
  assumes declared: "c \<in> \<Sigma> \<sigma>"
  shows "ROriginal c \<in> paper_R_henkin_signature \<Sigma> G k \<sigma>"
  by (simp only: paper_R_henkin_signature_original_iff; rule declared)

lemma paper_R_henkin_signature_original_inclusion:
  "image ROriginal (\<Sigma> \<sigma>) \<subseteq> paper_R_henkin_signature \<Sigma> G k \<sigma>"
  by (rule image_subsetI; rule paper_R_henkin_signature_original; assumption)

lemma paper_R_henkin_signature_witness:
  assumes closed: "named_fv F = {}"
    and predicate: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<sigma> Prop)"
  shows "RWitness k \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G (Suc k) \<sigma>"
  using closed predicate by auto

section \<open>The outer witness index proves actual stage freshness\<close>

theorem paper_R_henkin_signature_witness_index:
  assumes member: "RWitness j \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G k \<tau>"
  shows "j < k"
  using member
proof (induction k rule: nat.induct[case_names zero Suc])
  case zero
  then show ?case by auto
next
  case (Suc k)
  show ?case
  proof (cases "RWitness j \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G k \<tau>")
    case True
    have previous: "j < k" by (rule Suc.IH[OF True])
    show ?thesis by (rule less_SucI[OF previous])
  next
    case False
    have current: "j = k" using Suc.prems False by auto
    show ?thesis by (simp only: current; rule lessI)
  qed
qed

corollary paper_R_henkin_signature_witness_fresh:
  "RWitness k \<sigma> F \<notin> paper_R_henkin_signature \<Sigma> G k \<tau>"
proof
  assume member: "RWitness k \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G k \<tau>"
  have impossible: "k < k" by (rule paper_R_henkin_signature_witness_index[OF member])
  show False using impossible by simp
qed

corollary paper_R_henkin_signature_future_witness_fresh:
  assumes future: "k \<le> j"
  shows "RWitness j \<sigma> F \<notin> paper_R_henkin_signature \<Sigma> G k \<tau>"
proof
  assume member: "RWitness j \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G k \<tau>"
  have previous: "j < k" by (rule paper_R_henkin_signature_witness_index[OF member])
  show False using future previous by arith
qed

end
