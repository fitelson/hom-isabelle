theory Bacon_Book_Modalized_Exponential_Nonextension
  imports Bacon_Book_Modalized_Exponential_Transport
begin

section \<open>Exercise 17.4: a genuinely new future homomorphism\<close>

definition book_ex17_4_le :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "book_ex17_4_le w v \<longleftrightarrow> (w \<longrightarrow> v)"

definition book_ex17_4_domain :: "bool \<Rightarrow> nat set" where
  "book_ex17_4_domain w = (if w then {0,1,2} else {0,1})"

definition book_ex17_4_counterpart :: "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat" where
  "book_ex17_4_counterpart w v a = a"

abbreviation book_ex17_4_functions where
  "book_ex17_4_functions w \<equiv>
    book_modalized_exponential UNIV book_ex17_4_le
      book_ex17_4_domain book_ex17_4_counterpart book_ex17_4_domain book_ex17_4_counterpart w"

definition book_ex17_4_future_map :: "(bool \<times> nat) \<Rightarrow> nat" where
  "book_ex17_4_future_map p =
    (if p \<in> book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True
      then 2 else undefined)"

theorem book_ex17_4_pointed_preorder:
  "book_pointed_preorder (UNIV :: bool set) book_ex17_4_le False"
  by unfold_locales (auto simp: book_ex17_4_le_def)

theorem book_ex17_4_modalized_set:
  "book_modalized_set (UNIV :: bool set) book_ex17_4_le book_ex17_4_domain book_ex17_4_counterpart"
proof -
  interpret Frame: book_pointed_preorder "UNIV :: bool set" book_ex17_4_le False
    by (rule book_ex17_4_pointed_preorder)
  show ?thesis
  proof unfold_locales
    fix w v a
    assume "w \<in> (UNIV :: bool set)" "v \<in> UNIV"
      and related: "book_ex17_4_le w v" and member: "a \<in> book_ex17_4_domain w"
    show "book_ex17_4_counterpart w v a \<in> book_ex17_4_domain v"
      using related member by (cases w; cases v; auto simp: book_ex17_4_le_def
        book_ex17_4_domain_def book_ex17_4_counterpart_def)
  next
    show "\<And>w a. w \<in> (UNIV :: bool set) \<Longrightarrow> a \<in> book_ex17_4_domain w \<Longrightarrow>
      book_ex17_4_counterpart w w a = a"
      by (simp add: book_ex17_4_counterpart_def)
    show "\<And>w v u a. w \<in> (UNIV :: bool set) \<Longrightarrow> v \<in> UNIV \<Longrightarrow> u \<in> UNIV \<Longrightarrow>
      book_ex17_4_le w v \<Longrightarrow> book_ex17_4_le v u \<Longrightarrow> a \<in> book_ex17_4_domain w \<Longrightarrow>
      book_ex17_4_counterpart w u a =
        book_ex17_4_counterpart v u (book_ex17_4_counterpart w v a)"
      by (simp add: book_ex17_4_counterpart_def)
  qed
qed

lemma book_ex17_4_future_map_value:
  assumes member: "a \<in> book_ex17_4_domain True"
  shows "book_ex17_4_future_map (True,a) = 2"
  using member by (simp add: book_ex17_4_future_map_def book_modalized_exponential_pairs_iff book_ex17_4_le_def)

theorem book_ex17_4_future_map_member:
  "book_ex17_4_future_map \<in> book_ex17_4_functions True"
proof (rule book_modalized_exponentialI)
  fix p
  assume outside: "p \<notin> book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True"
  show "book_ex17_4_future_map p = undefined" by (simp add: book_ex17_4_future_map_def outside)
next
  fix v a
  assume "v \<in> (UNIV :: bool set)" and future: "book_ex17_4_le True v" and member: "a \<in> book_ex17_4_domain v"
  have at_later: "v = True" using future by (simp add: book_ex17_4_le_def)
  have value_eq: "book_ex17_4_future_map (v,a) = 2"
    by (simp only: at_later; rule book_ex17_4_future_map_value; use member in \<open>simp only: at_later\<close>)
  show "book_ex17_4_future_map (v,a) \<in> book_ex17_4_domain v"
    using value_eq by (simp add: at_later book_ex17_4_domain_def)
next
  fix v u a
  assume "v \<in> (UNIV :: bool set)" and future: "book_ex17_4_le True v" and "u \<in> UNIV"
    and later: "book_ex17_4_le v u" and member: "a \<in> book_ex17_4_domain v"
  have at_later: "v = True" and at_future: "u = True"
    using future later by (auto simp: book_ex17_4_le_def)
  show "book_ex17_4_counterpart v u (book_ex17_4_future_map (v,a)) =
      book_ex17_4_future_map (u,book_ex17_4_counterpart v u a)"
    by (simp only: book_ex17_4_counterpart_def at_later at_future)
qed

lemma book_ex17_4_earlier_map_at_zero:
  assumes member: "h \<in> book_ex17_4_functions False"
  shows "h (True,0) \<in> {0,1}"
proof -
  have early_world: "False \<in> (UNIV :: bool set)" and late_world: "True \<in> (UNIV :: bool set)" by simp_all
  have reflexive: "book_ex17_4_le False False" and accessible: "book_ex17_4_le False True"
    by (simp_all add: book_ex17_4_le_def)
  have zero: "0 \<in> book_ex17_4_domain False" by (simp add: book_ex17_4_domain_def)
  have typed: "h (False,0) \<in> book_ex17_4_domain False"
    by (rule book_modalized_exponential_type[OF member early_world reflexive zero])
  have natural: "book_ex17_4_counterpart False True (h (False,0)) =
      h (True,book_ex17_4_counterpart False True 0)"
    by (rule book_modalized_exponential_natural[
      OF member early_world reflexive late_world accessible zero])
  have same: "h (False,0) = h (True,0)" using natural by (simp only: book_ex17_4_counterpart_def)
  show ?thesis using typed by (simp only: book_ex17_4_domain_def if_False same)
qed

theorem book_ex17_4_no_global_extension:
  "\<not> (\<exists>h\<in>book_ex17_4_functions False.
    \<forall>p\<in>book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True.
      h p = book_ex17_4_future_map p)"
proof
  assume extension: "\<exists>h\<in>book_ex17_4_functions False.
    \<forall>p\<in>book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True.
      h p = book_ex17_4_future_map p"
  obtain h where member: "h \<in> book_ex17_4_functions False"
    and agreement: "\<forall>p\<in>book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True.
      h p = book_ex17_4_future_map p" using extension by blast
  have pair: "(True,0) \<in> book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True"
    by (simp add: book_modalized_exponential_pairs_iff book_ex17_4_le_def book_ex17_4_domain_def)
  have equal: "h (True,0) = book_ex17_4_future_map (True,0)" by (rule bspec[OF agreement pair])
  have zero: "0 \<in> book_ex17_4_domain True" by (simp add: book_ex17_4_domain_def)
  have two: "h (True,0) = 2" using equal by (simp only: book_ex17_4_future_map_value[OF zero])
  have bound: "h (True,0) \<in> {0,1}" by (rule book_ex17_4_earlier_map_at_zero[OF member])
  show False using bound by (simp add: two)
qed

theorem book_ex17_4_future_map_not_in_transport:
  "book_ex17_4_future_map \<notin>
    image (book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True)
      (book_ex17_4_functions False)"
proof
  assume in_image: "book_ex17_4_future_map \<in>
    image (book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True)
      (book_ex17_4_functions False)"
  obtain h where member: "h \<in> book_ex17_4_functions False"
    and shape: "book_ex17_4_future_map =
      book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True h"
    using in_image by blast
  have agreement: "h p = book_ex17_4_future_map p"
    if valid_pair: "p \<in> book_modalized_exponential_pairs UNIV book_ex17_4_le book_ex17_4_domain True" for p
  proof -
    have at_pair: "book_ex17_4_future_map p =
        book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True h p"
      by (rule fun_cong[OF shape])
    show ?thesis using at_pair by (simp add: book_modalized_exponential_transport_def valid_pair)
  qed
  show False by (rule notE[OF book_ex17_4_no_global_extension],
    rule bexI[where x=h], intro ballI, rule agreement, assumption, rule member)
qed

lemma book_ex17_4_transport_into_future:
  assumes member: "h \<in> book_ex17_4_functions False"
  shows "book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True h
    \<in> book_ex17_4_functions True"
  by (rule book_modalized_exponential_transport_type[where w=False and v=True,
    OF book_ex17_4_modalized_set book_ex17_4_modalized_set _ _ _ member];
    simp add: book_ex17_4_le_def)

corollary book_ex17_4_transport_not_surjective:
  "image (book_modalized_exponential_transport UNIV book_ex17_4_le book_ex17_4_domain True)
      (book_ex17_4_functions False) \<noteq> book_ex17_4_functions True"
  using book_ex17_4_future_map_member book_ex17_4_future_map_not_in_transport by blast

text \<open>
  False and True represent worlds 0≤1; the source's distinct a,b,c
  are represented by 0,1,2. All counterparts are the inclusion map.
  The later map sends all three legitimate inputs to 2 and is
  normalized only outside its future domain. An earlier homomorphism
  must send input 0 to 0 or 1, and naturality preserves that value
  at the later world. It therefore cannot extend this later map.

  This proves the new-future-homomorphism phenomenon and failure
  of exponential-transport surjectivity in Exercise 17.4, p.364.
  No value of undefined is assumed, and no modal λ interpretation,
  full logical model or model-existence theorem is claimed.
\<close>

end
