theory Bacon_Book_ZF_Nontrivial_Model
  imports Bacon_Book_ZF_Modal_Model
begin

section \<open>Nontrivial modal models at every world\<close>

text \<open>
  Definition 15.1 (pp.314–315) requires a false proposition for the
  minimal logical signature. Definition 18.1 (p.391) does not repeat
  this condition, although p.392 calls modal models instances of
  Chapter 15 models. The structural predicate book_ZF_modal_model
  is retained unchanged, so this refinement is not a silent alteration
  of a previously proved theorem.

  We require inhabited domains and a false proposition at EVERY world.
  Inhabitation prevents truth under all typed assignments from becoming
  vacuous; the false proposition excludes all-true models. The worldwise
  form retains these conditions when a future world becomes the root.
  The actual rerooted structure and its logical operations still require
  separate proofs. This is the source-directed nontrivial model class,
  not a claim that every clause is printed explicitly in Definition 18.1.
\<close>

locale book_ZF_nontrivial_modal_model = book_ZF_modal_model W R root D i signature I
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF
    and D :: book_ZF_domains and i :: book_ZF_counterparts
    and signature :: "'c ssignature" and I :: "'c \<Rightarrow> otype \<Rightarrow> ZF" +
  assumes domain_inhabited:
    "\<And>w \<sigma>. w \<in> explode W \<Longrightarrow> explode (D \<sigma> w) \<noteq> {}"
    and false_at_world:
    "\<And>w. w \<in> explode W \<Longrightarrow> \<exists>p\<in>explode (D Prop w). \<not> Elem w p"
begin

lemma false_at_root:
  "\<exists>p\<in>explode (D Prop root). \<not> Elem root p"
  by (rule false_at_world[OF root_world])

lemma not_all_propositions_true:
  assumes ww: "w \<in> explode W"
  shows "\<not> (\<forall>p\<in>explode (D Prop w). Elem w p)"
  using false_at_world[OF ww] by blast

lemma future_domains_inhabited:
  assumes vw: "v \<in> explode W" and access: "R w v"
  shows "explode (D \<sigma> v) \<noteq> {}"
  by (rule domain_inhabited[OF vw])

text \<open>
  The access premise is unnecessary for inhabitation itself: the
  condition holds throughout W. It is displayed in the last lemma
  only to give the future-world use its usual form.
\<close>

end

end
