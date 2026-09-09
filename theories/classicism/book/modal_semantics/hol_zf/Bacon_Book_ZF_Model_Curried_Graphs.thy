theory Bacon_Book_ZF_Model_Curried_Graphs
  imports Bacon_Book_ZF_Model_Function_Extensionality
begin

context book_ZF_modal_structure
begin

theorem function_as_two_lambdas:
  assumes ww: "w \<in> explode W" and fm: "F \<in> explode (D (Arr \<sigma> (Arr \<tau> \<rho>)) w)"
    and agree: "\<And>v a u b. v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      u \<in> explode W \<Longrightarrow> R v u \<Longrightarrow> b \<in> explode (D \<tau> u) \<Longrightarrow>
      app (app F (Opair v a)) (Opair u b) = B (Opair v a) (Opair u b)"
  shows "F = Lambda (book_ZF_pairs W R (D \<sigma>) w)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D \<tau>) (Fst p)) (B p))"
proof (rule function_as_lambda[OF ww fm])
  fix v a
  assume vw: "v \<in> explode W" and access: "R w v" and am: "a \<in> explode (D \<sigma> v)"
  have inner: "app F (Opair v a) \<in> explode (D (Arr \<tau> \<rho>) v)" by (rule function_type[OF ww vw access fm am])
  have equation: "app F (Opair v a) = Lambda (book_ZF_pairs W R (D \<tau>) v) (B (Opair v a))"
  proof (rule function_as_lambda[OF vw inner])
    fix u b
    assume uw: "u \<in> explode W" and vu: "R v u" and bm: "b \<in> explode (D \<tau> u)"
    show "app (app F (Opair v a)) (Opair u b) = B (Opair v a) (Opair u b)"
      by (rule agree[OF vw access am uw vu bm])
  qed
  show "app F (Opair v a) = Lambda (book_ZF_pairs W R (D \<tau>) (Fst (Opair v a))) (B (Opair v a))"
    by (simp only: Fst; rule equation)
qed

theorem function_as_three_lambdas:
  assumes ww: "w \<in> explode W" and fm: "F \<in> explode (D (Arr \<sigma> (Arr \<tau> (Arr \<upsilon> \<rho>))) w)"
    and agree: "\<And>v a u b t c. v \<in> explode W \<Longrightarrow> R w v \<Longrightarrow> a \<in> explode (D \<sigma> v) \<Longrightarrow>
      u \<in> explode W \<Longrightarrow> R v u \<Longrightarrow> b \<in> explode (D \<tau> u) \<Longrightarrow>
      t \<in> explode W \<Longrightarrow> R u t \<Longrightarrow> c \<in> explode (D \<upsilon> t) \<Longrightarrow>
      app (app (app F (Opair v a)) (Opair u b)) (Opair t c) = B (Opair v a) (Opair u b) (Opair t c)"
  shows "F = Lambda (book_ZF_pairs W R (D \<sigma>) w)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D \<tau>) (Fst p))
      (\<lambda>q. Lambda (book_ZF_pairs W R (D \<upsilon>) (Fst q)) (B p q)))"
proof (rule function_as_two_lambdas[OF ww fm])
  fix v a u b
  assume vw: "v \<in> explode W" and wv: "R w v" and am: "a \<in> explode (D \<sigma> v)"
    and uw: "u \<in> explode W" and vu: "R v u" and bm: "b \<in> explode (D \<tau> u)"
  have first: "app F (Opair v a) \<in> explode (D (Arr \<tau> (Arr \<upsilon> \<rho>)) v)"
    by (rule function_type[OF ww vw wv fm am])
  have second: "app (app F (Opair v a)) (Opair u b) \<in> explode (D (Arr \<upsilon> \<rho>) u)"
    by (rule function_type[OF vw uw vu first bm])
  have equation: "app (app F (Opair v a)) (Opair u b) =
    Lambda (book_ZF_pairs W R (D \<upsilon>) u) (B (Opair v a) (Opair u b))"
  proof (rule function_as_lambda[OF uw second])
    fix t c
    assume tw: "t \<in> explode W" and ut: "R u t" and cm: "c \<in> explode (D \<upsilon> t)"
    show "app (app (app F (Opair v a)) (Opair u b)) (Opair t c) = B (Opair v a) (Opair u b) (Opair t c)"
      by (rule agree[OF vw wv am uw vu bm tw ut cm])
  qed
  show "app (app F (Opair v a)) (Opair u b) =
    Lambda (book_ZF_pairs W R (D \<upsilon>) (Fst (Opair u b))) (B (Opair v a) (Opair u b))"
    by (simp only: Fst; rule equation)
qed

end

text \<open>
  Typed future behavior determines the exact two- or three-layer
  Lambda graph. The candidate alone is assumed in the chosen
  function domain; membership of the prescribed graph is a consequence
  of the resulting equality, not a premise of these lemmas.
\<close>

end
