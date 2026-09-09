theory Bacon_Source_Fresh_Embedding
  imports Bacon_Source_Renaming_Conversion Bacon_Source_Variable_Embedding
begin

section \<open>A fresh global variable represents an additional finite slot\<close>

text \<open>
  Given a representation r of Γ in G, choose vₙ:σ outside r[0,…,|Γ|−1].
  Extend r by sending the new slot 0 to n and slot k + 1 to r(k).
  Closing n after this representation agrees with lifting r beneath the
  binder.  Source role: the variable side conditions of Bacon–Dorr Figure 2
  Gen and Inst, p.8, with the fixed rich stock of §1.1.

  Isabelle representation: source_extend_map n r is case_nat n r.  The
  typing statement needs G n = σ and the old type map; freshness is needed
  for the closing equation and freshness of represented old terms.
  No injectivity is assumed for r.  All results concern raw terms, free
  slots, typing, or signature membership, not reverse proof preservation.
\<close>

definition source_extend_map :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "source_extend_map n r = case_nat n r"

lemma source_extend_map_zero[simp]: "source_extend_map n r 0 = n"
  by (simp add: source_extend_map_def)

lemma source_extend_map_Suc[simp]: "source_extend_map n r (Suc k) = r k"
  by (simp add: source_extend_map_def)

lemma sfv_lift_ren_image:
  "{k. Suc k \<in> lift_ren r ` X} = r ` {k. Suc k \<in> X}"
proof (rule equalityI)
  show "{k. Suc k \<in> lift_ren r ` X} \<subseteq> r ` {k. Suc k \<in> X}"
  proof (rule subsetI)
    fix k
    assume member: "k \<in> {k. Suc k \<in> lift_ren r ` X}"
    have image: "Suc k \<in> lift_ren r ` X" by (rule CollectD[OF member])
    from image obtain i where eq: "Suc k = lift_ren r i" and i: "i \<in> X" by (elim imageE)
    show "k \<in> r ` {k. Suc k \<in> X}"
    proof (cases i)
      case 0
      have False using eq by (simp only: 0 lift_ren.simps nat.distinct)
      then show ?thesis by (rule FalseE)
    next
      case (Suc j)
      have k: "k = r j" using eq by (simp only: Suc lift_ren.simps nat.inject)
      have j: "j \<in> {k. Suc k \<in> X}" using i by (simp only: Suc mem_Collect_eq)
      show ?thesis unfolding k by (rule imageI[OF j])
    qed
  qed
next
  show "r ` {k. Suc k \<in> X} \<subseteq> {k. Suc k \<in> lift_ren r ` X}"
  proof (rule subsetI)
    fix k
    assume member: "k \<in> r ` {k. Suc k \<in> X}"
    from member obtain j where eq: "k = r j" and j: "j \<in> {k. Suc k \<in> X}" by (elim imageE)
    have source: "Suc j \<in> X" by (rule CollectD[OF j])
    have image: "lift_ren r (Suc j) \<in> lift_ren r ` X" by (rule imageI[OF source])
    show "k \<in> {k. Suc k \<in> lift_ren r ` X}" using image by (simp only: eq lift_ren.simps mem_Collect_eq)
  qed
qed

lemma sfv_srename:
  "sfv (srename r A) = r ` sfv A"
  by (induction A arbitrary: r) (simp_all add: image_Un sfv_lift_ren_image)

lemma source_embedding_fresh_term:
  assumes typed: "has_stype L \<Gamma> P \<tau>"
    and fresh: "n \<notin> r ` {..<length \<Gamma>}"
  shows "n \<notin> sfv (srename r P)"
proof -
  have included: "sfv (srename r P) \<subseteq> r ` {..<length \<Gamma>}"
    unfolding sfv_srename by (rule image_mono[OF source_typed_fv_bound[OF typed]])
  show ?thesis
  proof (rule notI)
    assume member: "n \<in> sfv (srename r P)"
    have contradiction: "n \<in> r ` {..<length \<Gamma>}" by (rule subsetD[OF included member])
    show False by (rule notE[OF fresh contradiction])
  qed
qed

lemma source_extend_map_type:
  assumes selected: "G n = \<sigma>"
    and oldmap: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> G (r k) = \<rho>"
    and index: "lookup (\<sigma> # \<Gamma>) i = Some \<tau>"
  shows "G (source_extend_map n r i) = \<tau>"
proof (cases i)
  case 0
  have same_type: "\<sigma> = \<tau>" using index by (simp only: 0 lookup_Cons_0 option.inject)
  show ?thesis by (simp only: 0 source_extend_map_zero selected same_type)
next
  case (Suc k)
  have old: "lookup \<Gamma> k = Some \<tau>" using index by (simp only: Suc lookup_Cons_Suc)
  show ?thesis by (simp only: Suc source_extend_map_Suc oldmap[OF old])
qed

lemma source_extend_embedding_type:
  assumes typed: "has_stype L (\<sigma> # \<Gamma>) A \<tau>" and selected: "G n = \<sigma>"
    and oldmap: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> G (r k) = \<rho>"
  shows "has_sgtype L G (srename (source_extend_map n r) A) \<tau>"
  by (rule source_variable_embedding_type[OF typed], rule source_extend_map_type[OF selected oldmap], assumption)

lemma source_extend_embedding_language:
  assumes language: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) A \<tau>" and selected: "G n = \<sigma>"
    and oldmap: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> G (r k) = \<rho>"
  shows "sgterm_in_language L \<Sigma> G (srename (source_extend_map n r) A) \<tau>"
  by (rule source_variable_embedding_language[OF language], rule source_extend_map_type[OF selected oldmap], assumption)

lemma source_extend_sshift:
  "srename (source_extend_map n r) (sshift P) = srename r P"
proof -
  have maps: "source_extend_map n r \<circ> Suc = r" by (rule ext) simp
  show ?thesis by (simp only: sshift_def srename_comp maps)
qed

lemma source_fresh_close_embedding:
  assumes typed: "has_stype L (\<sigma> # \<Gamma>) A \<tau>"
    and fresh: "n \<notin> r ` {..<length \<Gamma>}"
  shows "sclose n (srename (source_extend_map n r) A) = srename (lift_ren r) A"
  unfolding sclose_def srename_comp
proof (rule srename_fv_agreement)
  fix i
  assume member: "i \<in> sfv A"
  have bound: "i < Suc (length \<Gamma>)"
    using subsetD[OF source_typed_fv_bound[OF typed] member] by simp
  show "((\<lambda>k. if k = n then 0 else Suc k) \<circ> source_extend_map n r) i = lift_ren r i"
  proof (cases i)
    case 0
    show ?thesis by (simp add: 0 comp_def)
  next
    case (Suc k)
    have k: "k \<in> {..<length \<Gamma>}" using bound by (simp add: Suc)
    have image: "r k \<in> r ` {..<length \<Gamma>}" by (rule imageI[OF k])
    have distinct: "r k \<noteq> n" using fresh image by blast
    show ?thesis by (simp only: Suc comp_def source_extend_map_Suc distinct if_False lift_ren.simps)
  qed
qed

corollary source_extend_sshift_case_nat:
  "srename (case_nat n r) (sshift P) = srename r P"
  using source_extend_sshift[where n=n and r=r and P=P] by (simp only: source_extend_map_def)

corollary source_fresh_close_embedding_case_nat:
  assumes typed: "has_stype L (\<sigma> # \<Gamma>) A \<tau>"
    and fresh: "n \<notin> r ` {..<length \<Gamma>}"
  shows "sclose n (srename (case_nat n r) A) = srename (lift_ren r) A"
  using source_fresh_close_embedding[OF typed fresh] by (simp only: source_extend_map_def)

end
