theory Bacon_Parametric_Henkin_Finite_Elimination
  imports Bacon_Parametric_Henkin_Rank
begin

lemma phenkin_pick_image:
  assumes member: "b \<in> image f A"
  obtains a where "a \<in> A" and "b = f a"
proof (rule imageE[where f=f and A=A and b=b, OF member])
  fix a
  assume eq: "b = f a" and a: "a \<in> A"
  show thesis by (rule that[OF a eq])
qed

lemma phenkin_union_outside:
  assumes member: "b \<in> A \<union> B" and outside: "b \<notin> A"
  shows "b \<in> B"
proof (rule UnE[OF member])
  assume "b \<in> A"
  then show ?thesis by (rule notE[OF outside])
next
  assume "b \<in> B"
  then show ?thesis .
qed

lemma phenkin_axioms_typed:
  assumes base: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] S"
    and admitted: "F \<subseteq> phenkin_witness_indices \<Sigma>"
  shows "pH_typed_theory (phenkin_full_signature \<Sigma>) [] (S \<union> image phenkin_index_axiom F)"
proof (unfold pH_typed_theory_def, intro ballI)
  fix B
  assume member: "B \<in> S \<union> image phenkin_index_axiom F"
  show "has_ptype [] B Prop \<and> pterm_in_signature (phenkin_full_signature \<Sigma>) B"
  proof (cases "B \<in> S")
    case True
    show ?thesis by (rule bspec[OF base[unfolded pH_typed_theory_def] True])
  next
    case False
    have image_member: "B \<in> image phenkin_index_axiom F" by (rule phenkin_union_outside[OF member False])
    obtain i where i: "i \<in> F" and B: "B = phenkin_index_axiom i"
      by (rule phenkin_pick_image[where f=phenkin_index_axiom and A=F and b=B, OF image_member])
    have data: "has_ptype [fst i] (snd i) Prop \<and> pterm_in_signature (phenkin_full_signature \<Sigma>) (snd i)"
      using subsetD[OF admitted i] by (simp only: phenkin_witness_indices_def mem_Collect_eq)
    have lang: "pterm_in_language (phenkin_full_signature \<Sigma>) []
        (phenkin_full_witness_axiom (fst i) (snd i)) Prop"
      by (rule phenkin_full_witness_axiom_language[OF conjunct1[OF data] conjunct2[OF data]])
    show ?thesis using lang by (simp only: B phenkin_index_axiom_def pterm_in_language_def)
  qed
qed

section \<open>Eliminating a maximal-rank axiom from each finite collection\<close>

text \<open>
  Conₕ(S) ⇒ Conₕ(S ∪ {Wᵢ : i ∈ F}) for finite F, provided S contains
  only old names.  Removing a maximal-rank index leaves a smaller finite
  collection.  The one-fresh-witness theorem then restores its axiom.
  Dependencies between witness bodies are allowed, but cycles are excluded
  by strict structural rank.  Equal ranks at distinct labels do not obstruct freshness.
\<close>

theorem phenkin_finite_witness_consistency:
  assumes typed: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] S"
    and con: "pH_consistent (phenkin_full_signature \<Sigma>) [] S"
    and old: "\<And>B \<sigma> A. B \<in> S \<Longrightarrow> PFWitness \<sigma> A \<notin> phenkin_names B"
    and finite_F: "finite F" and admitted: "F \<subseteq> phenkin_witness_indices \<Sigma>"
  shows "pH_consistent (phenkin_full_signature \<Sigma>) [] (S \<union> image phenkin_index_axiom F)"
  using finite_F admitted
proof (induction F rule: finite_psubset_induct)
  case (psubset F)
  show ?case
  proof (cases "F = {}")
    case True
    show ?thesis using con by (simp only: True image_empty Un_empty_right)
  next
    case False
    let ?r = "\<lambda>i. size (phenkin_index_name i)"
    have finite_r: "finite (image ?r F)" by (rule finite_imageI[OF psubset.hyps(1)])
    have nonempty_r: "image ?r F \<noteq> {}" using False by simp
    have max_member: "Max (image ?r F) \<in> image ?r F" by (rule Max_in[OF finite_r nonempty_r])
    obtain i where i: "i \<in> F" and maximum: "Max (image ?r F) = ?r i"
      by (rule phenkin_pick_image[where f="?r" and A=F and b="Max (image ?r F)", OF max_member])
    have maximal: "?r i = Max (image ?r F)" by (rule sym[OF maximum])
    let ?G = "F - {i}"
    have missing: "i \<notin> ?G" by simp
    have not_equal: "?G \<noteq> F"
    proof
      assume eq: "?G = F"
      have in_deleted: "i \<in> ?G" using i by (simp only: eq)
      have inside_singleton: "i \<in> {i}" by (rule singletonI)
      show False by (rule DiffD2[where c=i and A=F and B="{i}" and P=False,
        OF in_deleted inside_singleton])
    qed
    have proper: "?G \<subset> F" by (rule psubsetI[OF Diff_subset not_equal])
    have admitted_G: "?G \<subseteq> phenkin_witness_indices \<Sigma>" by (rule subset_trans[OF Diff_subset psubset.prems])
    have con_G: "pH_consistent (phenkin_full_signature \<Sigma>) [] (S \<union> image phenkin_index_axiom ?G)"
      by (rule psubset.IH[OF proper admitted_G])
    have typed_G: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] (S \<union> image phenkin_index_axiom ?G)"
      by (rule phenkin_axioms_typed[OF typed admitted_G])
    have data: "has_ptype [fst i] (snd i) Prop \<and> pterm_in_signature (phenkin_full_signature \<Sigma>) (snd i)"
      using subsetD[OF psubset.prems i] by (simp only: phenkin_witness_indices_def mem_Collect_eq)
    have fresh_rest: "PFWitness (fst i) (snd i) \<notin> phenkin_names B"
      if B: "B \<in> S \<union> image phenkin_index_axiom ?G" for B
    proof (cases "B \<in> S")
      case True
      show ?thesis by (rule old[OF True])
    next
      case False
      have image_member: "B \<in> image phenkin_index_axiom ?G" by (rule phenkin_union_outside[OF B False])
      obtain j where j: "j \<in> ?G" and Bj: "B = phenkin_index_axiom j"
        by (rule phenkin_pick_image[where f=phenkin_index_axiom and A="?G" and b=B, OF image_member])
      have jf: "j \<in> F" using j by simp
      have different: "i \<noteq> j"
      proof
        assume eq: "i = j"
        have in_deleted: "i \<in> ?G" using j by (simp only: eq)
        have inside_singleton: "i \<in> {i}" by (rule singletonI)
        show False by (rule DiffD2[where c=i and A=F and B="{i}" and P=False,
          OF in_deleted inside_singleton])
      qed
      have bound: "?r j \<le> ?r i"
      proof -
        have "?r j \<in> image ?r F" by (rule imageI[OF jf])
        then have "?r j \<le> Max (image ?r F)" by (rule Max_ge[OF finite_r])
        then show ?thesis by (simp only: maximal)
      qed
      have fresh: "phenkin_index_name i \<notin> phenkin_names (phenkin_index_axiom j)"
        by (rule phenkin_max_rank_fresh[OF bound different])
      show ?thesis using fresh by (simp only: Bj phenkin_index_name_def; simp)
    qed
    have insert_con: "pH_consistent (phenkin_full_signature \<Sigma>) []
      (insert (pH_fresh_witness_axiom (PFWitness (fst i) (snd i)) (fst i) (snd i))
        (S \<union> image phenkin_index_axiom ?G))"
      by (rule pH_fresh_witness_consistency[OF typed_G con_G
        conjunct1[OF data] conjunct2[OF data] fresh_rest phenkin_witness_fresh_body])
    have restore: "insert i ?G = F" by (rule insert_Diff[OF i])
    have mapped_restore: "S \<union> image phenkin_index_axiom (insert i ?G) = S \<union> image phenkin_index_axiom F"
      by (rule arg_cong[where f="\<lambda>X. S \<union> image phenkin_index_axiom X", OF restore])
    have union_eq: "S \<union> image phenkin_index_axiom F =
        insert (phenkin_index_axiom i) (S \<union> image phenkin_index_axiom ?G)"
      using mapped_restore[symmetric] by (simp only: image_insert Un_insert_right)
    have restored_con: "pH_consistent (phenkin_full_signature \<Sigma>) []
        (insert (phenkin_index_axiom i) (S \<union> image phenkin_index_axiom ?G))"
      using insert_con by (simp only: phenkin_index_axiom_def phenkin_full_witness_axiom_def
        phenkin_full_witness_def pH_fresh_witness_axiom_def; simp)
    show ?thesis using restored_con by (simp only: union_eq; simp)
  qed
qed

end
