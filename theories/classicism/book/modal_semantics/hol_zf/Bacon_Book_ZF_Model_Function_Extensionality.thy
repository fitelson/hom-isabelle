theory Bacon_Book_ZF_Model_Function_Extensionality
  imports Bacon_Book_ZF_Modal_Structure
begin

context book_ZF_modal_structure
begin

theorem function_as_lambda:
  assumes ww: "w \<in> explode W" and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) w)"
    and agree: "\<And>v a. v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      app F (Opair v a) = B (Opair v a)"
  shows "F = Lambda (book_ZF_pairs W R (D \<sigma>) w) B"
proof -
  have fg: "F = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)" by (rule function_graph[OF ww fm])
  have equal: "Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F) = Lambda (book_ZF_pairs W R (D \<sigma>) w) B"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix p
    assume member: "Elem p (book_ZF_pairs W R (D \<sigma>) w)"
    have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
      and am: "Snd p \<in> explode (D \<sigma> (Fst p))" and shape: "Opair (Fst p) (Snd p) = p"
      using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
    show "app F p = B p" using agree[OF vw access am] by (simp only: shape)
  qed
  show ?thesis by (rule trans[OF fg equal])
qed

theorem future_function_extensionality:
  assumes ww: "w \<in> explode W"
    and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) w)" and hm: "H \<in> explode (D (Arr \<sigma> \<tau>) w)"
    and agree: "\<And>v a. v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      app F (Opair v a) = app H (Opair v a)"
  shows "F = H"
proof -
  have fg: "F = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F)" by (rule function_graph[OF ww fm])
  have hg: "H = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app H)" by (rule function_graph[OF ww hm])
  have equal: "Lambda (book_ZF_pairs W R (D \<sigma>) w) (app F) = Lambda (book_ZF_pairs W R (D \<sigma>) w) (app H)"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix p
    assume member: "Elem p (book_ZF_pairs W R (D \<sigma>) w)"
    have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
      and am: "Snd p \<in> explode (D \<sigma> (Fst p))" and shape: "Opair (Fst p) (Snd p) = p"
      using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
    show "app F p = app H p" using agree[OF vw access am] by (simp only: shape)
  qed
  show ?thesis by (rule trans[OF fg trans[OF equal hg[symmetric]]])
qed

end

text \<open>
  The exact graph fields imply the quasi-functionality required of a
  concrete modalized applicative structure (Definition 17.11 and
  Exercise 17.8): equality of every future application gives equality
  of the functions. Equality of present-world applications alone is
  not assumed sufficient. The no-junk graph condition is essential
  to this deduction.
\<close>

end
