theory Bacon_Book_Function_Representation
  imports Bacon_Book_Modalized_Bijection
    Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Exponential_Domain
begin

section \<open>Proposition 18.4: constructing the function represented by a source value\<close>

locale book_function_representation =
  Arg: book_modalized_bijection W le A iA DA dA hA +
  Res: book_modalized_bijection W le B iB DB dB hB +
  Fun: book_modalized_set W le F iF
  for W :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool"
    and A :: "'w \<Rightarrow> 'a set" and iA :: "'w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a"
    and DA :: "'w \<Rightarrow> 'c set" and dA :: "'w \<Rightarrow> 'w \<Rightarrow> 'c \<Rightarrow> 'c"
    and hA :: "'w \<Rightarrow> 'a \<Rightarrow> 'c"
    and B :: "'w \<Rightarrow> 'b set" and iB :: "'w \<Rightarrow> 'w \<Rightarrow> 'b \<Rightarrow> 'b"
    and DB :: "'w \<Rightarrow> 'd set" and dB :: "'w \<Rightarrow> 'w \<Rightarrow> 'd \<Rightarrow> 'd"
    and hB :: "'w \<Rightarrow> 'b \<Rightarrow> 'd"
    and F :: "'w \<Rightarrow> 'f set" and iF :: "'w \<Rightarrow> 'w \<Rightarrow> 'f \<Rightarrow> 'f" +
  fixes app :: "'w \<Rightarrow> 'f \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes app_type: "w \<in> W \<Longrightarrow> f \<in> F w \<Longrightarrow> a \<in> A w \<Longrightarrow> app w f a \<in> B w"
    and app_natural: "w \<in> W \<Longrightarrow> v \<in> W \<Longrightarrow> le w v \<Longrightarrow> f \<in> F w \<Longrightarrow> a \<in> A w \<Longrightarrow>
      iB w v (app w f a) = app v (iF w v f) (iA w v a)"
begin

definition function_h :: "'w \<Rightarrow> 'f \<Rightarrow> ('w \<times> 'c \<Rightarrow> 'd)" where
  "function_h w f = (\<lambda>p. if p \<in> book_modalized_exponential_pairs W le DA w
    then hB (fst p) (app (fst p) (iF w (fst p) f) (Arg.j (fst p) (snd p))) else undefined)"

definition function_domain where "function_domain w = function_h w ` F w"
definition function_j where "function_j w = inv_into (F w) (function_h w)"

lemma function_h_on:
  assumes vw: "v \<in> W" and access: "le w v" and am: "a \<in> DA v"
  shows "function_h w f (v,a) = hB v (app v (iF w v f) (Arg.j v a))"
  using vw access am by (simp add: function_h_def book_modalized_exponential_pairs_iff)

lemma function_h_normal:
  "p \<notin> book_modalized_exponential_pairs W le DA w \<Longrightarrow> function_h w f p = undefined"
  by (simp add: function_h_def)

lemma function_h_type:
  assumes ww: "w \<in> W" and fm: "f \<in> F w"
    and vw: "v \<in> W" and access: "le w v" and am: "a \<in> DA v"
  shows "function_h w f (v,a) \<in> DB v"
proof -
  have moved: "iF w v f \<in> F v" by (rule Fun.counterpart_type[OF ww vw access fm])
  have inverse: "Arg.j v a \<in> A v" by (rule Arg.j_type[OF vw am])
  have result: "app v (iF w v f) (Arg.j v a) \<in> B v" by (rule app_type[OF vw moved inverse])
  show ?thesis by (simp only: function_h_on[OF vw access am]; rule Res.h_type[OF vw result])
qed

text \<open>
  Given the lower-type modalized bijections, h at the function type is
  explicitly f(v,a)=hB(v,Appv(iwv(F),jA(v,a))). Only values outside the
  actual future/argument domain are normalized to undefined, as in the
  existing Definition 17.9 interface. The function domain is the image
  of the source F domain, not the entire exponential. Naturality and
  injectivity remain to be proved in the following leaves; no target
  homomorphism membership or functional representation is assumed here.
\<close>

end

end
