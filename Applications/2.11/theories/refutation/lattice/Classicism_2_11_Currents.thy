theory Classicism_2_11_Currents
  imports "Classicism_2_11_Formulas.Classicism_2_11_Order_Defs"
    "Classicism_2_11_Formulas.Classicism_2_11_World_Cases"
begin

section \<open>Current truth relations of raw relational objects\<close>

text \<open>
  For σs = [σ1,…,σk] and a raw object F of type σ1→…→σk→t at world w,
  its current relation is the set of argument tuples, drawn from the
  raw carriers at w, on which iterated application at w is true at w.
  The nullary case (k = 0, type t) is the singleton tuple set or empty.
  These are definitions only.
\<close>

definition c211_tuples :: "otype list \<Rightarrow> ZF \<Rightarrow> ZF list set" where
  "c211_tuples \<sigma>s w = {xs. list_all2 (\<lambda>\<sigma> x. Elem x (raw_D \<sigma> w)) \<sigma>s xs}"

fun c211_rapp :: "otype list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "c211_rapp [] w F xs = F"
| "c211_rapp (\<sigma> # \<sigma>s) w F [] = F"
| "c211_rapp (\<sigma> # \<sigma>s) w F (x # xs) =
    c211_rapp \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x) xs"

definition c211_rcur :: "otype list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF list set" where
  "c211_rcur \<sigma>s w F = {xs \<in> c211_tuples \<sigma>s w. raw_truth w (c211_rapp \<sigma>s w F xs)}"

lemma c211_tuples_Nil [simp]: "c211_tuples [] w = {[]}"
  by (auto simp: c211_tuples_def)

lemma c211_tuples_Cons:
  "xs \<in> c211_tuples (\<sigma> # \<sigma>s) w \<longleftrightarrow>
    (\<exists>x ys. xs = x # ys \<and> Elem x (raw_D \<sigma> w) \<and> ys \<in> c211_tuples \<sigma>s w)"
  by (cases xs) (auto simp: c211_tuples_def)

lemma c211_rcur_Nil: "c211_rcur [] w F = (if raw_truth w F then {[]} else {})"
  by (auto simp: c211_rcur_def)

lemma c211_rcur_Cons:
  "x # ys \<in> c211_rcur (\<sigma> # \<sigma>s) w F \<longleftrightarrow>
    Elem x (raw_D \<sigma> w) \<and> ys \<in> c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x)"
  by (auto simp: c211_rcur_def c211_tuples_def)

lemma c211_rcur_tuples: "c211_rcur \<sigma>s w F \<subseteq> c211_tuples \<sigma>s w"
  by (auto simp: c211_rcur_def)

ML \<open>
  val _ = ["c211_tuples_Cons", "c211_rcur_Nil", "c211_rcur_Cons", "c211_rcur_tuples"]
    |> List.app (fn name =>
      let val th = Proof_Context.get_thm \<^context> name
      in if null (Thm_Deps.all_oracles [th]) andalso null (Thm.hyps_of th)
           andalso null (Thm.tpairs_of th) then () else error name end);
  val _ = writeln "C211-CURRENTS: definitions; 4 clean auxiliary lemmas"
\<close>

end
