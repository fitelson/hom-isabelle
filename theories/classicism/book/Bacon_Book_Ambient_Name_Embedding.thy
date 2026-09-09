theory Bacon_Book_Ambient_Name_Embedding
  imports Bacon_Book_Name_Countability
begin

definition book_reserve_name_map :: "'c::countable set \<Rightarrow> 'c set \<Rightarrow> 'c book_henkin_name \<Rightarrow> 'c" where
  "book_reserve_name_map D B x =
    (if x \<in> BookOriginal ` D then inv BookOriginal x
     else from_nat_into (B - D) (2 * to_nat x))"

lemma book_reserve_name_map_original:
  assumes member: "c \<in> D"
  shows "book_reserve_name_map D B (BookOriginal c) = c"
  using member by (simp add: book_reserve_name_map_def inv_f_f[OF book_henkin_original_injective])

lemma book_reserve_name_map_new:
  assumes fresh: "x \<notin> BookOriginal ` D"
  shows "book_reserve_name_map D B x = from_nat_into (B - D) (2 * to_nat x)"
  by (simp only: book_reserve_name_map_def fresh if_False)

locale book_countable_name_reserve =
  fixes old_names :: "'c::countable set" and ambient :: "'c set"
  assumes included: "old_names \<subseteq> ambient"
    and reserve_infinite: "infinite (ambient - old_names)"
begin

abbreviation enumerate_reserve where "enumerate_reserve \<equiv> from_nat_into (ambient - old_names)"
abbreviation embed where "embed \<equiv> book_reserve_name_map old_names ambient"

lemma reserve_position:
  "enumerate_reserve n \<in> ambient - old_names"
proof -
  have nonempty: "ambient - old_names \<noteq> {}"
  proof
    assume empty: "ambient - old_names = {}"
    have finite: "finite (ambient - old_names)" by (simp only: empty; rule finite.emptyI)
    show False by (rule notE[OF reserve_infinite finite])
  qed
  show ?thesis by (rule from_nat_into[OF nonempty])
qed

lemma reserve_enumeration_injective:
  "inj enumerate_reserve"
  using bij_betw_from_nat_into[OF countableI_type reserve_infinite]
  unfolding bij_betw_def by blast

lemma old_name_image:
  assumes old: "x \<in> BookOriginal ` old_names"
  shows "embed x \<in> old_names"
proof -
  obtain c where member: "c \<in> old_names" and shape: "x = BookOriginal c" using old by blast
  show ?thesis by (simp only: shape book_reserve_name_map_original[OF member]; rule member)
qed

lemma new_name_image:
  assumes fresh: "x \<notin> BookOriginal ` old_names"
  shows "embed x \<in> ambient - old_names"
  by (simp only: book_reserve_name_map_new[OF fresh]; rule reserve_position)

theorem book_reserve_embedding_range:
  "range embed \<subseteq> ambient"
  using old_name_image new_name_image included by blast

theorem book_reserve_embedding_injective:
  "inj embed"
proof (rule injI)
  fix x y
  assume equal: "embed x = embed y"
  show "x = y"
  proof (cases "x \<in> BookOriginal ` old_names")
    case True
    obtain c where cm: "c \<in> old_names" and xs: "x = BookOriginal c" using True by blast
    show ?thesis
    proof (cases "y \<in> BookOriginal ` old_names")
      case True
      obtain d where dm: "d \<in> old_names" and ys: "y = BookOriginal d" using True by blast
      have "c = d" using equal by (simp only: xs ys book_reserve_name_map_original[OF cm] book_reserve_name_map_original[OF dm])
      then show ?thesis by (simp only: xs ys)
    next
      case False
      have excluded: "embed y \<notin> old_names"
        by (rule notI; rule DiffD2[OF new_name_image[OF False]]; assumption)
      have old_x: "embed x \<in> old_names" by (rule old_name_image[OF True])
      have included_y: "embed y \<in> old_names" by (rule subst[where P="\<lambda>z. z \<in> old_names", OF equal old_x])
      show ?thesis using excluded included_y by contradiction
    qed
  next
    case False
    show ?thesis
    proof (cases "y \<in> BookOriginal ` old_names")
      case True
      have excluded: "embed x \<notin> old_names"
        by (rule notI; rule DiffD2[OF new_name_image[OF False]]; assumption)
      have old_y: "embed y \<in> old_names" by (rule old_name_image[OF True])
      have included_x: "embed x \<in> old_names" by (rule subst[where P="\<lambda>z. z \<in> old_names", OF equal[symmetric] old_y])
      show ?thesis using excluded included_x by contradiction
    next
      case False_y: False
      have positions: "enumerate_reserve (2 * to_nat x) = enumerate_reserve (2 * to_nat y)"
        using equal by (simp only: book_reserve_name_map_new[OF False] book_reserve_name_map_new[OF False_y])
      have codes: "2 * to_nat x = 2 * to_nat y" by (rule injD[OF reserve_enumeration_injective positions])
      show ?thesis using codes by simp
    qed
  qed
qed

lemma odd_position_unused:
  "enumerate_reserve (2 * n + 1) \<notin> range embed"
proof
  assume member: "enumerate_reserve (2 * n + 1) \<in> range embed"
  obtain x where equal: "enumerate_reserve (2 * n + 1) = embed x" using member by blast
  show False
  proof (cases "x \<in> BookOriginal ` old_names")
    case True
    have position: "enumerate_reserve (2*n+1) \<in> ambient - old_names" by (rule reserve_position)
    have excluded: "enumerate_reserve (2*n+1) \<notin> old_names"
      by (rule notI; rule DiffD2[OF position]; assumption)
    have old_x: "embed x \<in> old_names" by (rule old_name_image[OF True])
    have old: "enumerate_reserve (2*n+1) \<in> old_names"
      by (rule subst[where P="\<lambda>z. z \<in> old_names", OF equal[symmetric] old_x])
    show False by (rule notE[OF excluded old])
  next
    case False
    have positions: "enumerate_reserve (2 * n + 1) = enumerate_reserve (2 * to_nat x)"
      using equal by (simp only: book_reserve_name_map_new[OF False])
    have impossible: "2 * n + 1 = 2 * to_nat x" by (rule injD[OF reserve_enumeration_injective positions])
    show False using impossible by presburger
  qed
qed

theorem book_reserve_embedding_leaves_infinite:
  "infinite (ambient - range embed)"
proof -
  have injective: "inj (\<lambda>n. enumerate_reserve (2*n+1))"
  proof (rule injI)
    fix n m
    assume equal: "enumerate_reserve (2*n+1) = enumerate_reserve (2*m+1)"
    have positions: "2*n+1 = 2*m+1" by (rule injD[OF reserve_enumeration_injective equal])
    show "n = m" using positions by simp
  qed
  have infinite_image: "infinite (range (\<lambda>n. enumerate_reserve (2*n+1)))"
  proof
    assume finite: "finite (range (\<lambda>n. enumerate_reserve (2*n+1)))"
    have impossible: "finite (UNIV :: nat set)" by (rule finite_imageD[OF finite injective])
    show False by (rule notE[OF infinite_UNIV_nat impossible])
  qed
  have subset: "range (\<lambda>n. enumerate_reserve (2*n+1)) \<subseteq> ambient - range embed"
  proof
    fix x
    assume member: "x \<in> range (\<lambda>n. enumerate_reserve (2*n+1))"
    obtain n where shape: "x = enumerate_reserve (2*n+1)" using member by blast
    have position: "enumerate_reserve (2*n+1) \<in> ambient - old_names" by (rule reserve_position)
    have inside: "enumerate_reserve (2*n+1) \<in> ambient" by (rule DiffD1[OF position])
    have unused: "enumerate_reserve (2*n+1) \<notin> range embed" by (rule odd_position_unused)
    show "x \<in> ambient - range embed" by (simp only: shape; rule DiffI[OF inside unused])
  qed
  show ?thesis using infinite_image subset finite_subset by blast
qed

end

text \<open>
  Only Original(c) with c already declared is fixed. Every other name
  is placed in an even position of an enumeration of the old reserve.
  Odd positions remain unused. The maps and the remaining infinity are
  proved explicitly, with countability of the carrier stated. No global
  identity on all Original names or semantic model is assumed.
\<close>

end
