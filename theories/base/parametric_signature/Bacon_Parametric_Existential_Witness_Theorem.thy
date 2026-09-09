theory Bacon_Parametric_Existential_Witness_Theorem
  imports Bacon_Parametric_Fresh_Constant
begin

section \<open>An existential witness for an existential implication\<close>

text \<open>
  ⊢ₕ ∃xσ. ((∃yσ. A(y)) → A(x)).
  Source: the witness-extension argument in Bacon, Proposition 15.4,
  p. 319, and Bacon–Dorr, Theorem 3.2, p. 45 n. 64.

  Isabelle representation: the body is PImp (pshift (PExists σ A)) A.
  The shift ensures that the antecedent does not acquire the new free slot.
  We split on ∃y A(y), use EG and Inst, and finish by PC.  The case where
  no A exists still needs an inhabited type.  We derive that for every F
  type from IndividualExistence, rather than assume a default constant is
  in the signature.  The slot-restoration equation is syntactic β bookkeeping.

  Status: an object-language theorem with typing/signature hypotheses only.
  No witness, consistency assertion, or Henkin-model existence is assumed.
\<close>

lemma pH_witness_PC:
  assumes ty: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature \<Sigma> A"
    and truth: "\<forall>v. pprop_eval v A"
  shows "pH_proves \<Sigma> \<Gamma> A"
proof -
  have taut: "pprop_tautology \<Gamma> A"
    unfolding pprop_tautology_def by (rule conjI[OF ty truth])
  show ?thesis by (rule pH_proves.PC[OF taut sig])
qed

lemma pH_witness_PC_two:
  assumes a: "pH_proves \<Sigma> \<Gamma> A" and b: "pH_proves \<Sigma> \<Gamma> B"
    and ct: "has_ptype \<Gamma> C Prop" and cs: "pterm_in_signature \<Sigma> C"
    and truth: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v B \<longrightarrow> pprop_eval v C"
  shows "pH_proves \<Sigma> \<Gamma> C"
proof -
  have at: "has_ptype \<Gamma> A Prop" by (rule pH_proves_formula[OF a])
  have bt: "has_ptype \<Gamma> B Prop" by (rule pH_proves_formula[OF b])
  have sa: "pterm_in_signature \<Sigma> A" by (rule pH_proves_in_signature[OF a])
  have sb: "pterm_in_signature \<Sigma> B" by (rule pH_proves_in_signature[OF b])
  have ty: "has_ptype \<Gamma> (PImp A (PImp B C)) Prop"
    by (intro has_ptype.PImp at bt ct)
  have sig: "pterm_in_signature \<Sigma> (PImp A (PImp B C))" using sa sb cs by simp
  have valid: "\<forall>v. pprop_eval v (PImp A (PImp B C))"
    using truth by (simp only: pprop_eval.simps)
  have ax: "pH_proves \<Sigma> \<Gamma> (PImp A (PImp B C))" by (rule pH_witness_PC[OF ty sig valid])
  have bc: "pH_proves \<Sigma> \<Gamma> (PImp B C)"
    by (rule pH_proves.MP[OF a ax sa]) (simp only: pterm_in_signature.simps sb cs)
  show ?thesis by (rule pH_proves.MP[OF b bc sb cs])
qed

fun pH_type_witness :: "otype \<Rightarrow> 'c pterm" where
  "pH_type_witness Ind = PVar 0"
| "pH_type_witness Prop = PObjTrue"
| "pH_type_witness (Arr \<sigma> \<tau>) = PLam \<sigma> (pshift (pH_type_witness \<tau>))"

lemma pH_type_witness_typed:
  "has_ptype (Ind # \<Gamma>) (pH_type_witness \<tau> :: 'c pterm) \<tau>"
proof (induction \<tau>)
  case Ind
  show ?case by (simp only: pH_type_witness.simps; rule has_ptype.PVar) simp
next
  case Prop
  show ?case unfolding pH_type_witness.simps PObjTrue_def
    by (intro has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all
next
  case (Arr \<sigma> \<tau>)
  have body: "has_ptype (\<sigma> # Ind # \<Gamma>)
      (pshift (pH_type_witness \<tau> :: 'c pterm)) \<tau>"
    by (rule pshift_preserves_typing[where \<sigma>=\<sigma> and \<Gamma>="Ind # \<Gamma>", OF Arr.IH(2)])
  show ?case by (simp only: pH_type_witness.simps; rule has_ptype.PLam[OF body])
qed

lemma pH_type_witness_signature:
  "pterm_in_signature \<Sigma> (pH_type_witness \<tau>)"
  by (induction \<tau>) (simp_all add: PObjTrue_def pshift_def)

lemma pH_all_type_existence:
  "pH_proves \<Sigma> \<Gamma> (PExists \<sigma> (PEq \<sigma> (PVar 0) (PVar 0)))"
proof -
  let ?K = "pH_type_witness \<sigma>"
  let ?R = "PEq \<sigma> (PVar 0) (PVar 0)"
  let ?X = "PExists \<sigma> ?R"
  let ?I = "PEq Ind (PVar 0) (PVar 0)"
  have kt: "has_ptype (Ind # \<Gamma>) ?K \<sigma>" by (rule pH_type_witness_typed)
  have ks: "pterm_in_signature \<Sigma> ?K" by (rule pH_type_witness_signature)
  have rt: "has_ptype (\<sigma> # Ind # \<Gamma>) ?R Prop"
    by (intro has_ptype.PEq has_ptype.PVar) simp_all
  have rs: "pterm_in_signature \<Sigma> ?R" by simp
  have ref: "pH_proves \<Sigma> (Ind # \<Gamma>) (PEq \<sigma> ?K ?K)" by (rule pH_proves.Ref[OF kt ks])
  have eg: "pH_proves \<Sigma> (Ind # \<Gamma>) (PImp (psubst0 ?K ?R) ?X)"
    by (rule pH_proves.EG[OF rt kt rs ks])
  have eg': "pH_proves \<Sigma> (Ind # \<Gamma>) (PImp (PEq \<sigma> ?K ?K) ?X)"
    using eg by (simp add: psubst0_def)
  have refsig: "pterm_in_signature \<Sigma> (PEq \<sigma> ?K ?K)" using ks by simp
  have xs: "pterm_in_signature \<Sigma> ?X" by simp
  have x: "pH_proves \<Sigma> (Ind # \<Gamma>) ?X" by (rule pH_proves.MP[OF ref eg' refsig xs])
  have it: "has_ptype (Ind # \<Gamma>) ?I Prop" by (intro has_ptype.PEq has_ptype.PVar) simp_all
  have xt: "has_ptype \<Gamma> ?X Prop" by (intro has_ptype.PExists has_ptype.PEq has_ptype.PVar) simp_all
  have sxt: "has_ptype (Ind # \<Gamma>) (pshift ?X) Prop" by (rule pshift_preserves_typing[OF xt])
  have sx: "pshift ?X = ?X" by (simp add: pshift_def)
  have imp_t: "has_ptype (Ind # \<Gamma>) (PImp ?I (pshift ?X)) Prop"
    by (rule has_ptype.PImp[OF it sxt])
  have imp_s: "pterm_in_signature \<Sigma> (PImp ?I (pshift ?X))" by (simp add: pshift_def)
  have imp: "pH_proves \<Sigma> (Ind # \<Gamma>) (PImp ?I (pshift ?X))"
  proof (rule pH_witness_PC_two[OF x x imp_t imp_s])
    show "\<forall>v. pprop_eval v ?X \<longrightarrow> pprop_eval v ?X \<longrightarrow>
      pprop_eval v (PImp ?I (pshift ?X))" by (simp only: sx pprop_eval.simps) simp
  qed
  have i_sig: "pterm_in_signature \<Sigma> ?I" by simp
  have down: "pH_proves \<Sigma> \<Gamma> (PImp (PExists Ind ?I) ?X)"
    by (rule pH_proves.Inst[OF it xt i_sig xs imp])
  have base: "pH_proves \<Sigma> \<Gamma> (PExists Ind ?I)" by (rule pH_proves.IndividualExistence)
  have bases: "pterm_in_signature \<Sigma> (PExists Ind ?I)" by simp
  show ?thesis by (rule pH_proves.MP[OF base down bases xs])
qed

lemma pH_witness_slot_restore:
  "psubst0 (PVar 0) (prename (lift_ren Suc) A) = A"
  unfolding psubst0_def
  by (rule psubst_prename_inverse) (case_tac n; simp)

theorem pH_exists_imp_shift_exists:
  assumes at: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sa: "pterm_in_signature \<Sigma> A"
  shows "pH_proves \<Sigma> \<Gamma> (PExists \<sigma> (PImp (pshift (PExists \<sigma> A)) A))"
proof -
  let ?E = "PExists \<sigma> A"
  let ?B = "PImp (pshift ?E) A"
  let ?Q = "PExists \<sigma> ?B"
  have et: "has_ptype \<Gamma> ?E Prop" by (rule has_ptype.PExists[OF at])
  have shift_et: "has_ptype (\<sigma> # \<Gamma>) (pshift ?E) Prop" by (rule pshift_preserves_typing[OF et])
  have bt: "has_ptype (\<sigma> # \<Gamma>) ?B Prop" by (rule has_ptype.PImp[OF shift_et at])
  have qt: "has_ptype \<Gamma> ?Q Prop" by (rule has_ptype.PExists[OF bt])
  have sqt: "has_ptype (\<sigma> # \<Gamma>) (pshift ?Q) Prop" by (rule pshift_preserves_typing[OF qt])
  have es: "pterm_in_signature \<Sigma> ?E" using sa by simp
  have bs: "pterm_in_signature \<Sigma> ?B" using sa by (simp add: pshift_def)
  have qs: "pterm_in_signature \<Sigma> ?Q" using bs by simp
  have sset: "pterm_in_signature \<Sigma> (pshift ?E)" using es by (simp add: pshift_def)
  have sqs: "pterm_in_signature \<Sigma> (pshift ?Q)" using qs by (simp add: pshift_def)

  have ab_t: "has_ptype (\<sigma> # \<Gamma>) (PImp A ?B) Prop" by (rule has_ptype.PImp[OF at bt])
  have ab_s: "pterm_in_signature \<Sigma> (PImp A ?B)" using sa bs by simp
  have ab: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp A ?B)"
    by (rule pH_witness_PC[OF ab_t ab_s]) (simp only: pprop_eval.simps; simp)
  have lifted: "has_ptype (\<sigma> # \<sigma> # \<Gamma>) (prename (lift_ren Suc) ?B) Prop"
    by (rule prename_preserves_typing[OF bt]) (case_tac n; simp)
  have zero: "has_ptype (\<sigma> # \<Gamma>) (PVar 0) \<sigma>" by (rule has_ptype.PVar) simp
  have ls: "pterm_in_signature \<Sigma> (prename (lift_ren Suc) ?B)" using bs by simp
  have zs: "pterm_in_signature \<Sigma> (PVar 0)" by simp
  have eg: "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
      (PImp (psubst0 (PVar 0) (prename (lift_ren Suc) ?B))
        (PExists \<sigma> (prename (lift_ren Suc) ?B)))"
    by (rule pH_proves.EG[OF lifted zero ls zs])
  have restore: "psubst0 (PVar 0) (prename (lift_ren Suc) ?B) = ?B"
    by (rule pH_witness_slot_restore)
  have shift_q: "pshift ?Q = PExists \<sigma> (prename (lift_ren Suc) ?B)"
    by (simp only: pshift_def prename.simps)
  have bq: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp ?B (pshift ?Q))"
    using eg by (simp only: restore shift_q)
  have aq_t: "has_ptype (\<sigma> # \<Gamma>) (PImp A (pshift ?Q)) Prop"
    by (rule has_ptype.PImp[OF at sqt])
  have aq_s: "pterm_in_signature \<Sigma> (PImp A (pshift ?Q))" using sa sqs by simp
  have aq: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp A (pshift ?Q))"
    by (rule pH_witness_PC_two[OF ab bq aq_t aq_s]) (simp only: pprop_eval.simps; blast)
  have eq: "pH_proves \<Sigma> \<Gamma> (PImp ?E ?Q)"
    by (rule pH_proves.Inst[OF at qt sa qs aq])

  have net: "has_ptype (\<sigma> # \<Gamma>) (PNeg (pshift ?E)) Prop" by (rule has_ptype.PNeg[OF shift_et])
  have nb_t: "has_ptype (\<sigma> # \<Gamma>) (PImp (PNeg (pshift ?E)) ?B) Prop"
    by (rule has_ptype.PImp[OF net bt])
  have nb_s: "pterm_in_signature \<Sigma> (PImp (PNeg (pshift ?E)) ?B)" using sset bs by simp
  have nb: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (PNeg (pshift ?E)) ?B)"
    by (rule pH_witness_PC[OF nb_t nb_s]) (simp only: pprop_eval.simps; simp)
  have nq_t: "has_ptype (\<sigma> # \<Gamma>) (PImp (PNeg (pshift ?E)) (pshift ?Q)) Prop"
    by (rule has_ptype.PImp[OF net sqt])
  have nq_s: "pterm_in_signature \<Sigma> (PImp (PNeg (pshift ?E)) (pshift ?Q))"
    using sset sqs by simp
  have nq: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (PNeg (pshift ?E)) (pshift ?Q))"
    by (rule pH_witness_PC_two[OF nb bq nq_t nq_s]) (simp only: pprop_eval.simps; blast)

  let ?R = "PEq \<sigma> (PVar 0) (PVar 0)"
  let ?C = "PImp (PNeg ?E) ?Q"
  have ct: "has_ptype \<Gamma> ?C Prop" by (rule has_ptype.PImp[OF has_ptype.PNeg[OF et] qt])
  have cs: "pterm_in_signature \<Sigma> ?C" using es qs by simp
  have rt: "has_ptype (\<sigma> # \<Gamma>) ?R Prop" by (intro has_ptype.PEq has_ptype.PVar) simp_all
  have rs: "pterm_in_signature \<Sigma> ?R" by simp
  have shifted_c: "pshift ?C = PImp (PNeg (pshift ?E)) (pshift ?Q)" by (simp add: pshift_def)
  have sc_t: "has_ptype (\<sigma> # \<Gamma>) (pshift ?C) Prop" by (rule pshift_preserves_typing[OF ct])
  have rc_t: "has_ptype (\<sigma> # \<Gamma>) (PImp ?R (pshift ?C)) Prop"
    by (rule has_ptype.PImp[OF rt sc_t])
  have rc_s: "pterm_in_signature \<Sigma> (PImp ?R (pshift ?C))" using rs cs by (simp add: pshift_def)
  have rc: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp ?R (pshift ?C))"
    by (rule pH_witness_PC_two[OF nq nq rc_t rc_s])
      (simp only: shifted_c pprop_eval.simps; blast)
  have down: "pH_proves \<Sigma> \<Gamma> (PImp (PExists \<sigma> ?R) ?C)"
    by (rule pH_proves.Inst[OF rt ct rs cs rc])
  have inhabited: "pH_proves \<Sigma> \<Gamma> (PExists \<sigma> ?R)" by (rule pH_all_type_existence)
  have inhabited_sig: "pterm_in_signature \<Sigma> (PExists \<sigma> ?R)" by simp
  have neq: "pH_proves \<Sigma> \<Gamma> ?C" by (rule pH_proves.MP[OF inhabited down inhabited_sig cs])
  show ?thesis by (rule pH_witness_PC_two[OF eq neq qt qs]) (simp only: pprop_eval.simps; blast)
qed

end
