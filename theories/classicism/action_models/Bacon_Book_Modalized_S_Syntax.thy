theory Bacon_Book_Modalized_S_Syntax
  imports Bacon_Book_Modalized_Exponential_Transport
begin

section \<open>The three normalized layers of the modalized S family\<close>

locale book_modalized_S_data =
  fixes W :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool"
    and A :: "'w \<Rightarrow> 'a set" and iA :: "'w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a"
    and B :: "'w \<Rightarrow> 'b set" and iB :: "'w \<Rightarrow> 'w \<Rightarrow> 'b \<Rightarrow> 'b"
    and C :: "'w \<Rightarrow> 'c set" and iC :: "'w \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes A_set: "book_modalized_set W le A iA"
    and B_set: "book_modalized_set W le B iB"
    and C_set: "book_modalized_set W le C iC"
begin

sublocale A: book_modalized_set W le A iA by (rule A_set)
sublocale B: book_modalized_set W le B iB by (rule B_set)
sublocale C: book_modalized_set W le C iC by (rule C_set)

abbreviation S_AB where
  "S_AB \<equiv> book_modalized_exponential W le A iA B iB"
abbreviation S_BC where
  "S_BC \<equiv> book_modalized_exponential W le B iB C iC"
abbreviation S_AC where
  "S_AC \<equiv> book_modalized_exponential W le A iA C iC"
abbreviation S_iAB where
  "S_iAB \<equiv> (\<lambda>w v. book_modalized_exponential_transport W le A v)"
abbreviation S_iBC where
  "S_iBC \<equiv> (\<lambda>w v. book_modalized_exponential_transport W le B v)"
abbreviation S_iAC where
  "S_iAC \<equiv> (\<lambda>w v. book_modalized_exponential_transport W le A v)"
abbreviation S_A_BC where
  "S_A_BC \<equiv> book_modalized_exponential W le A iA S_BC S_iBC"
abbreviation S_iA_BC where
  "S_iA_BC \<equiv> (\<lambda>w v. book_modalized_exponential_transport W le A v)"
abbreviation S_AB_AC where
  "S_AB_AC \<equiv> book_modalized_exponential W le S_AB S_iAB S_AC S_iAC"
abbreviation S_iAB_AC where
  "S_iAB_AC \<equiv> (\<lambda>w v. book_modalized_exponential_transport W le S_AB v)"
abbreviation S_domain where
  "S_domain \<equiv> book_modalized_exponential W le S_A_BC S_iA_BC S_AB_AC S_iAB_AC"

definition book_modalized_S_inner ::
  "'w \<Rightarrow> (('w \<times> 'a) \<Rightarrow> ('w \<times> 'b) \<Rightarrow> 'c) \<Rightarrow>
    (('w \<times> 'a) \<Rightarrow> 'b) \<Rightarrow> ('w \<times> 'a) \<Rightarrow> 'c" where
  "book_modalized_S_inner z f g =
    (\<lambda>(w,a). if (w,a) \<in> book_modalized_exponential_pairs W le A z
      then f (w,a) (w,g (w,a)) else undefined)"

definition book_modalized_S_middle ::
  "'w \<Rightarrow> (('w \<times> 'a) \<Rightarrow> ('w \<times> 'b) \<Rightarrow> 'c) \<Rightarrow>
    ('w \<times> (('w \<times> 'a) \<Rightarrow> 'b)) \<Rightarrow> ('w \<times> 'a) \<Rightarrow> 'c" where
  "book_modalized_S_middle y f =
    (\<lambda>(z,g). if (z,g) \<in> book_modalized_exponential_pairs W le S_AB y
      then book_modalized_S_inner z f g else undefined)"

definition book_modalized_S ::
  "'w \<Rightarrow> ('w \<times> (('w \<times> 'a) \<Rightarrow> ('w \<times> 'b) \<Rightarrow> 'c)) \<Rightarrow>
    ('w \<times> (('w \<times> 'a) \<Rightarrow> 'b)) \<Rightarrow> ('w \<times> 'a) \<Rightarrow> 'c" where
  "book_modalized_S x =
    (\<lambda>(y,f). if (y,f) \<in> book_modalized_exponential_pairs W le S_A_BC x
      then book_modalized_S_middle y f else undefined)"

lemma book_modalized_S_inner_on:
  "(w,a) \<in> book_modalized_exponential_pairs W le A z \<Longrightarrow>
    book_modalized_S_inner z f g (w,a) = f (w,a) (w,g (w,a))"
  by (simp add: book_modalized_S_inner_def)

lemma book_modalized_S_middle_on:
  "(z,g) \<in> book_modalized_exponential_pairs W le S_AB y \<Longrightarrow>
    book_modalized_S_middle y f (z,g) = book_modalized_S_inner z f g"
  by (simp add: book_modalized_S_middle_def)

lemma book_modalized_S_on:
  "(y,f) \<in> book_modalized_exponential_pairs W le S_A_BC x \<Longrightarrow>
    book_modalized_S x (y,f) = book_modalized_S_middle y f"
  by (simp add: book_modalized_S_def)

text \<open>
  Exercise 17.6, p.364: on x ≤ y ≤ z ≤ w these definitions give
  sₓ(y,f)(z,g)(w,a) = f(w,a)(w,g(w,a)).
  Each layer is normalized only outside its own valid future inputs.
  The domains above are the full Definition 17.9 exponentials, including
  homomorphisms that do not extend to earlier worlds.
\<close>

end
end
