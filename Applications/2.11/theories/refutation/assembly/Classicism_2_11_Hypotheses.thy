theory Classicism_2_11_Hypotheses
  imports "Classicism_2_11_Semantics.Classicism_2_11_Order_Semantics"
    "Classicism_2_11_Formulas.Classicism_2_11_Hypotheses_Def"
    "Classicism_2_11_Transfer.Classicism_2_11_Transfer"
    "Classicism_2_11_Raw_Lattice.Classicism_2_11_Raw_Lattice"
    "Classicism_2_11_Barcan.Classicism_2_11_BF"
begin

section \<open>Every hypothesis of Proposition 2.11 holds in the concrete model\<close>

text \<open>
  □Atomicity and Boolean Completeness (with the intended lower-bound
  clause) at every relational type, and every BF instance, are valid in
  the concrete action model in the sense of Definition 3.20: true at the
  root identity arrow under every typed adequate assignment.
  The order-theoretic content comes from the raw lattice theorems at
  every world, transferred through the arrow-coded encoding.
\<close>

abbreviation c211_concrete_valid :: "'c ssignature \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "c211_concrete_valid S A \<equiv>
    c211_valid S c211_G pa_Ar Fst Snd pa_compose pa_id raw_root paper_D paper_T paper_I A"

lemma c211_relational_vector:
  "paper_R_relational \<tau> \<Longrightarrow> \<exists>\<sigma>s. \<tau> = paper_type_vector \<sigma>s Prop"
proof (induction \<tau>)
  case Ind then show ?case by (simp add: paper_R_relational_def)
next
  case Prop show ?case by (rule exI[of _ "[]"]) simp
next
  case (Arr \<sigma> \<rho>)
  obtain \<sigma>s where "\<rho> = paper_type_vector \<sigma>s Prop"
    using Arr.IH(2)[OF c211_relational_Arr(2)[OF Arr.prems]] by blast
  then show ?case by (intro exI[of _ "\<sigma> # \<sigma>s"]) simp
qed

lemma c211_concrete_sem:
  "c211_sem S (explode raw_W) pa_Ar Fst Snd pa_compose pa_id raw_root paper_D paper_T paper_I"
  by (unfold_locales) (rule concrete_paper_standard_model)

lemma c211_concrete_atomic:
  assumes rel: "paper_R_relational \<tau>" and w: "Elem w raw_W"
  shows "c211_patomic pa_Ar Fst Snd paper_D \<tau> w"
proof -
  obtain \<sigma>s where tv: "\<tau> = paper_type_vector \<sigma>s Prop" using c211_relational_vector[OF rel] by blast
  show ?thesis using c211_transfer_atomic[OF w] c211_raw_atomic[OF w, of \<sigma>s] by (simp add: tv)
qed

lemma c211_concrete_complete:
  assumes rel: "paper_R_relational \<tau>"
  shows "c211_pcomplete pa_Ar Fst Snd paper_D \<tau> raw_root"
proof -
  obtain \<sigma>s where tv: "\<tau> = paper_type_vector \<sigma>s Prop" using c211_relational_vector[OF rel] by blast
  show ?thesis using c211_transfer_complete[OF raw_worlds(1)] c211_raw_complete_root[of \<sigma>s]
    by (simp add: tv)
qed

theorem c211_box_atomicity_concrete:
  assumes rel: "paper_R_relational \<tau>"
  shows "c211_concrete_valid S (c211_box_atomicity \<tau>)"
proof -
  interpret M: c211_sem S "explode raw_W" pa_Ar Fst Snd pa_compose pa_id raw_root paper_D paper_T paper_I
    by (rule c211_concrete_sem)
  have "\<forall>h. h \<in> explode pa_Ar \<longrightarrow> Fst h = raw_root \<longrightarrow> c211_patomic pa_Ar Fst Snd paper_D \<tau> (Snd h)"
    using c211_concrete_atomic[OF rel] c211_arrow_split(3) by blast
  then show ?thesis by (rule M.box_atomicity_valid[OF rel])
qed

theorem c211_BC_concrete:
  assumes rel: "paper_R_relational \<tau>"
  shows "c211_concrete_valid S (c211_BC \<tau>)"
proof -
  interpret M: c211_sem S "explode raw_W" pa_Ar Fst Snd pa_compose pa_id raw_root paper_D paper_T paper_I
    by (rule c211_concrete_sem)
  show ?thesis by (rule M.BC_valid[OF rel c211_concrete_complete[OF rel]])
qed

theorem c211_hypotheses_valid:
  "A \<in> c211_hypotheses S \<Longrightarrow> c211_concrete_valid S A"
  by (erule c211_hypotheses_cases)
    (simp_all add: c211_box_atomicity_concrete c211_BC_concrete c211_BF_concrete)

ML \<open>
  val _ = ["c211_relational_vector", "c211_concrete_atomic", "c211_concrete_complete",
      "c211_box_atomicity_concrete", "c211_BC_concrete", "c211_hypotheses_valid"]
    |> List.app (fn name =>
      let val th = Proof_Context.get_thm \<^context> name
      in if null (Thm_Deps.all_oracles [th]) andalso null (Thm.hyps_of th)
           andalso null (Thm.tpairs_of th) then () else error name end);
  val _ = writeln "C211-HYPOTHESES: 6 clean endpoints"
\<close>

end
