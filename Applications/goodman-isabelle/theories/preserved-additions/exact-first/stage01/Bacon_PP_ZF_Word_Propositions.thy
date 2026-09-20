theory Bacon_PP_ZF_Word_Propositions
  imports
    
    "Goodman_Exact_Legacy_01.Bacon_PP_Appendix_Model"
    "HOL-ZF.MainZF"
    "HOL-Library.Countable_Set"
    "HOL-Library.More_List"
begin

section \<open>Neutral HOL-ZF coding of Bacon's proposition M-set\<close>

text \<open>
  This theory contains only the finite-word proposition carrier and Bacon's
  right-division action and lift.  The exact recursive construction and the
  secondary comparison frames may both import this neutral support layer.
\<close>

definition pp_zf_prop :: "(ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_zf_prop P = Sep Nat P"

definition pp_zf_truth :: "bool \<Rightarrow> ZF" where
  "pp_zf_truth b = pp_zf_prop (\<lambda>_. b)"

lemma pp_zf_truth_in_power:
  "Elem (pp_zf_truth b) (Power Nat)"
  by (auto simp: pp_zf_truth_def pp_zf_prop_def Power subset_def Sep)

lemma pp_zf_function_isFun:
  assumes "Elem f (Fun U V)"
  shows "isFun f"
  using assms
  by (simp add: Fun_def PFun_def Sep)

lemma pp_zf_function_domain:
  assumes "Elem f (Fun U V)"
  shows "Domain f = U"
  using assms
  by (simp add: Fun_def Sep)

definition pp_n_encode :: "nat list \<Rightarrow> nat" where
  "pp_n_encode w = to_nat_on UNIV w"

definition pp_n_decode :: "nat \<Rightarrow> nat list" where
  "pp_n_decode n = from_nat_into UNIV n"

lemma pp_n_words_countable:
  "countable (UNIV :: nat list set)"
  by simp

lemma pp_n_words_infinite:
  "infinite (UNIV :: nat list set)"
  using infinite_UNIV_listI by simp

lemma pp_n_decode_encode[simp]:
  "pp_n_decode (pp_n_encode w) = w"
  unfolding pp_n_decode_def pp_n_encode_def
  using from_nat_into_to_nat_on[OF pp_n_words_countable, of w]
  by simp

lemma pp_n_encode_decode[simp]:
  "pp_n_encode (pp_n_decode n) = n"
  unfolding pp_n_decode_def pp_n_encode_def
  using to_nat_on_from_nat_into_infinite[
    OF pp_n_words_countable pp_n_words_infinite, of n] .

definition pp_n_holds :: "ZF \<Rightarrow> nat list \<Rightarrow> bool" where
  "pp_n_holds P w \<longleftrightarrow>
    Elem (nat2Nat (pp_n_encode w)) P"

definition pp_n_prop :: "(nat list \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_n_prop Q =
    pp_zf_prop (\<lambda>z. Q (pp_n_decode (Nat2nat z)))"

lemma pp_n_prop_in_power:
  "Elem (pp_n_prop Q) (Power Nat)"
  by (auto simp: pp_n_prop_def pp_zf_prop_def Power subset_def Sep)

lemma pp_n_holds_prop[simp]:
  "pp_n_holds (pp_n_prop Q) w \<longleftrightarrow> Q w"
  unfolding pp_n_holds_def pp_n_prop_def pp_zf_prop_def
  by (simp add: Sep Elem_nat2Nat_Nat)

lemma pp_n_holds_truth[simp]:
  "pp_n_holds (pp_zf_truth b) w \<longleftrightarrow> b"
  unfolding pp_n_holds_def pp_zf_truth_def pp_zf_prop_def
  by (simp add: Sep Elem_nat2Nat_Nat)


text \<open>
  Bacon's proposition domain is \<open>Pow (nat list)\<close>, with right division
  \<open>i P = {j. j @ i \<in> P}\<close>.  The HOL-ZF frame presents the same
  worlds in prefix order.  Reversal is therefore built into the following
  encoding.  The theorems below prove that this is an isomorphism of the
  proposition M-set, not merely an isomorphism of the underlying frame.
\<close>

definition pp_n_bacon_embed :: "pp_sem_prop \<Rightarrow> ZF" where
  "pp_n_bacon_embed P = pp_n_prop (\<lambda>w. rev w \<in> P)"

definition pp_n_bacon_extract :: "ZF \<Rightarrow> pp_sem_prop" where
  "pp_n_bacon_extract P = {i. pp_n_holds P (rev i)}"

lemma pp_n_bacon_embed_in_domain:
  "Elem (pp_n_bacon_embed P) (Power Nat)"
  unfolding pp_n_bacon_embed_def
  by (rule pp_n_prop_in_power)

lemma pp_n_bacon_embed_holds[simp]:
  "pp_n_holds (pp_n_bacon_embed P) w \<longleftrightarrow> rev w \<in> P"
  by (simp add: pp_n_bacon_embed_def)

lemma pp_n_bacon_extract_embed[simp]:
  "pp_n_bacon_extract (pp_n_bacon_embed P) = P"
  by (auto simp: pp_n_bacon_extract_def)

lemma pp_n_prop_eta:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop (pp_n_holds P) = P"
  unfolding pp_n_prop_def pp_zf_prop_def pp_n_holds_def
proof (subst Ext, intro allI)
  fix z
  have P_power: "Elem P (Power Nat)"
    using P by simp
  then have P_nat: "Elem z P \<Longrightarrow> Elem z Nat"
    by (auto simp: Power subset_def)
  show "Elem z
      (Sep Nat
        (\<lambda>z. Elem
          (nat2Nat
            (pp_n_encode (pp_n_decode (Nat2nat z))))
          P)) =
      Elem z P"
    using P_nat
    by (auto simp: Sep)
qed

lemma pp_n_bacon_embed_extract:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_bacon_embed (pp_n_bacon_extract P) = P"
proof -
  have pointwise:
      "(\<lambda>w. rev w \<in> pp_n_bacon_extract P) = pp_n_holds P"
    by (rule ext) (simp add: pp_n_bacon_extract_def)
  show ?thesis
    unfolding pp_n_bacon_embed_def pointwise
    by (rule pp_n_prop_eta[OF P])
qed

definition pp_n_prop_action :: "pp_word \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_n_prop_action i P =
    pp_n_prop (\<lambda>w. pp_n_holds P (rev i @ w))"

definition pp_n_prop_lift :: "pp_word \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_n_prop_lift i P =
    pp_n_prop (\<lambda>v. \<exists>w. v = rev i @ w \<and> pp_n_holds P w)"

lemma pp_n_prop_action_in_domain:
  "Elem (pp_n_prop_action i P) (Power Nat)"
  unfolding pp_n_prop_action_def
  by (rule pp_n_prop_in_power)

lemma pp_n_prop_lift_in_domain:
  "Elem (pp_n_prop_lift i P) (Power Nat)"
  unfolding pp_n_prop_lift_def
  by (rule pp_n_prop_in_power)

lemma pp_n_prop_action_holds[simp]:
  "pp_n_holds (pp_n_prop_action i P) w \<longleftrightarrow>
    pp_n_holds P (rev i @ w)"
  by (simp add: pp_n_prop_action_def)

lemma pp_n_prop_lift_holds[simp]:
  "pp_n_holds (pp_n_prop_lift i P) v \<longleftrightarrow>
    (\<exists>w. v = rev i @ w \<and> pp_n_holds P w)"
  by (simp add: pp_n_prop_lift_def)

theorem pp_n_prop_action_is_bacon_division:
  "pp_n_prop_action i (pp_n_bacon_embed P) =
    pp_n_bacon_embed (pp_prop_action i P)"
proof -
  have predicates:
      "(\<lambda>w. pp_n_holds (pp_n_bacon_embed P) (rev i @ w)) =
       (\<lambda>w. rev w \<in> pp_prop_action i P)"
    by (rule ext)
      (simp add: pp_prop_action_def pp_view_def rev_append)
  show ?thesis
    using predicates
    unfolding pp_n_prop_action_def pp_n_bacon_embed_def
    by simp
qed

theorem pp_n_prop_lift_is_bacon_lift:
  "pp_n_prop_lift i (pp_n_bacon_embed P) =
    pp_n_bacon_embed (pp_lift i P)"
proof -
  have predicates:
      "(\<lambda>v. \<exists>w.
          v = rev i @ w \<and>
          pp_n_holds (pp_n_bacon_embed P) w) =
       (\<lambda>v. rev v \<in> pp_lift i P)"
  proof (rule ext)
    fix v
    show "(\<exists>w.
        v = rev i @ w \<and>
        pp_n_holds (pp_n_bacon_embed P) w) =
      (rev v \<in> pp_lift i P)"
    proof
      assume "\<exists>w.
          v = rev i @ w \<and>
          pp_n_holds (pp_n_bacon_embed P) w"
      then obtain w where v: "v = rev i @ w" and w: "rev w \<in> P"
        by auto
      have "rev v = rev w @ i"
        using v by (simp add: rev_append)
      then show "rev v \<in> pp_lift i P"
        using w by (auto simp: pp_lift_def)
    next
      assume "rev v \<in> pp_lift i P"
      then obtain j where j: "j \<in> P" and rev_v: "rev v = j @ i"
        by (auto simp: pp_lift_def)
      have v: "v = rev i @ rev j"
        using rev_v by (metis rev_append rev_rev_ident)
      show "\<exists>w.
          v = rev i @ w \<and>
          pp_n_holds (pp_n_bacon_embed P) w"
        using v j by (intro exI[of _ "rev j"]) simp
    qed
  qed
  show ?thesis
    using predicates
    unfolding pp_n_prop_lift_def pp_n_bacon_embed_def
    by simp
qed

theorem pp_n_bacon_extract_action:
  "pp_n_bacon_extract (pp_n_prop_action i P) =
    pp_prop_action i (pp_n_bacon_extract P)"
  by (rule set_eqI)
    (simp add: pp_n_bacon_extract_def pp_prop_action_def
      pp_view_def rev_append)

theorem pp_n_bacon_extract_lift:
  "pp_n_bacon_extract (pp_n_prop_lift i P) =
    pp_lift i (pp_n_bacon_extract P)"
proof (rule set_eqI)
  fix j
  show "j \<in> pp_n_bacon_extract (pp_n_prop_lift i P) \<longleftrightarrow>
      j \<in> pp_lift i (pp_n_bacon_extract P)"
  proof
    assume "j \<in> pp_n_bacon_extract (pp_n_prop_lift i P)"
    then obtain w where rev_j: "rev j = rev i @ w"
      and w: "pp_n_holds P w"
      by (auto simp: pp_n_bacon_extract_def)
    have j: "j = rev w @ i"
      using rev_j by (metis rev_append rev_rev_ident)
    have rev_w: "rev w \<in> pp_n_bacon_extract P"
      using w by (simp add: pp_n_bacon_extract_def)
    show "j \<in> pp_lift i (pp_n_bacon_extract P)"
      using j rev_w unfolding pp_lift_def by blast
  next
    assume "j \<in> pp_lift i (pp_n_bacon_extract P)"
    then obtain k where j: "j = k @ i"
      and k: "pp_n_holds P (rev k)"
      by (auto simp: pp_lift_def pp_n_bacon_extract_def)
    have rev_j: "rev j = rev i @ rev k"
      using j by (simp add: rev_append)
    show "j \<in> pp_n_bacon_extract (pp_n_prop_lift i P)"
      using rev_j k by (auto simp: pp_n_bacon_extract_def)
  qed
qed

lemma pp_n_prop_action_one:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_action pp_subst_one P = P"
  unfolding pp_n_prop_action_def pp_subst_one_def
  by (simp add: pp_n_prop_eta[OF P])

lemma pp_n_prop_action_comp:
  "pp_n_prop_action i (pp_n_prop_action j P) =
    pp_n_prop_action (pp_subst_comp i j) P"
  unfolding pp_n_prop_action_def pp_subst_comp_def
  by (rule arg_cong[where f=pp_n_prop])
    (rule ext, simp add: rev_append append_assoc)

theorem pp_n_prop_action_lift:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_action i (pp_n_prop_lift i P) = P"
proof -
  have pointwise:
      "(\<lambda>w. pp_n_holds (pp_n_prop_lift i P) (rev i @ w)) =
       pp_n_holds P"
  proof (rule ext)
    fix w
    show "pp_n_holds (pp_n_prop_lift i P) (rev i @ w) =
        pp_n_holds P w"
      by auto
  qed
  show ?thesis
    unfolding pp_n_prop_action_def pointwise
    by (rule pp_n_prop_eta[OF P])
qed

theorem pp_n_prop_action_surjective:
  assumes P: "Elem P (Power Nat)"
  shows "\<exists>Q. Elem Q (Power Nat) \<and>
    pp_n_prop_action i Q = P"
  using pp_n_prop_lift_in_domain pp_n_prop_action_lift[OF P, of i]
  by blast

subsection \<open>The full cone-lift algebra at proposition type\<close>

lemma pp_n_bacon_extract_injective_on_domain:
  assumes P: "Elem P (Power Nat)"
    and Q: "Elem Q (Power Nat)"
    and same: "pp_n_bacon_extract P = pp_n_bacon_extract Q"
  shows "P = Q"
proof -
  have "P = pp_n_bacon_embed (pp_n_bacon_extract P)"
    using pp_n_bacon_embed_extract[OF P] by simp
  also have "... = pp_n_bacon_embed (pp_n_bacon_extract Q)"
    using same by simp
  also have "... = Q"
    by (rule pp_n_bacon_embed_extract[OF Q])
  finally show ?thesis .
qed

lemma pp_n_bacon_extract_empty[simp]:
  "pp_n_bacon_extract Empty = {}"
  by (auto simp: pp_n_bacon_extract_def pp_n_holds_def Empty)

lemma pp_n_prop_lift_one:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_lift [] P = P"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_lift [] P) (Power Nat)"
      by (rule pp_n_prop_lift_in_domain)
    show "Elem P (Power Nat)" by (rule P)
    show "pp_n_bacon_extract (pp_n_prop_lift [] P) =
        pp_n_bacon_extract P"
      by (simp add: pp_n_bacon_extract_lift pp_lift_root)
  qed
qed

lemma pp_n_prop_lift_comp:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_lift j (pp_n_prop_lift i P) =
    pp_n_prop_lift (i @ j) P"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_lift j (pp_n_prop_lift i P))
        (Power Nat)"
      by (rule pp_n_prop_lift_in_domain)
    show "Elem (pp_n_prop_lift (i @ j) P) (Power Nat)"
      by (rule pp_n_prop_lift_in_domain)
    show "pp_n_bacon_extract (pp_n_prop_lift j (pp_n_prop_lift i P)) =
        pp_n_bacon_extract (pp_n_prop_lift (i @ j) P)"
      by (simp add: pp_n_bacon_extract_lift pp_lift_compose)
  qed
qed

lemma pp_n_prop_action_empty:
  "pp_n_prop_action i Empty = Empty"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_action i Empty) (Power Nat)"
      by (rule pp_n_prop_action_in_domain)
    show "Elem Empty (Power Nat)"
      by (simp add: Power subset_empty)
    show "pp_n_bacon_extract (pp_n_prop_action i Empty) =
        pp_n_bacon_extract Empty"
      by (simp add: pp_n_bacon_extract_action pp_prop_action_def pp_view_def)
  qed
qed

lemma pp_n_prop_lift_empty:
  "pp_n_prop_lift i Empty = Empty"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_lift i Empty) (Power Nat)"
      by (rule pp_n_prop_lift_in_domain)
    show "Elem Empty (Power Nat)"
      by (simp add: Power subset_empty)
    show "pp_n_bacon_extract (pp_n_prop_lift i Empty) =
        pp_n_bacon_extract Empty"
      by (simp add: pp_n_bacon_extract_lift pp_lift_def)
  qed
qed

lemma pp_n_prop_action_lift_longer:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_action (k @ i) (pp_n_prop_lift i P) =
    pp_n_prop_action k P"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_action (k @ i) (pp_n_prop_lift i P))
        (Power Nat)"
      by (rule pp_n_prop_action_in_domain)
    show "Elem (pp_n_prop_action k P) (Power Nat)"
      by (rule pp_n_prop_action_in_domain)
    show "pp_n_bacon_extract
          (pp_n_prop_action (k @ i) (pp_n_prop_lift i P)) =
        pp_n_bacon_extract (pp_n_prop_action k P)"
      by (simp add: pp_n_bacon_extract_action pp_n_bacon_extract_lift
        pp_prop_action_def pp_view_lift_longer_suffix)
  qed
qed

lemma pp_n_prop_action_lift_shorter:
  assumes P: "Elem P (Power Nat)"
  shows "pp_n_prop_action j (pp_n_prop_lift (k @ j) P) =
    pp_n_prop_lift k P"
proof -
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_action j (pp_n_prop_lift (k @ j) P))
        (Power Nat)"
      by (rule pp_n_prop_action_in_domain)
    show "Elem (pp_n_prop_lift k P) (Power Nat)"
      by (rule pp_n_prop_lift_in_domain)
    show "pp_n_bacon_extract
          (pp_n_prop_action j (pp_n_prop_lift (k @ j) P)) =
        pp_n_bacon_extract (pp_n_prop_lift k P)"
      by (simp add: pp_n_bacon_extract_action pp_n_bacon_extract_lift
        pp_prop_action_def pp_view_lift_shorter_suffix)
  qed
qed

lemma pp_n_prop_action_lift_incomparable:
  assumes P: "Elem P (Power Nat)"
    and not_ji: "\<nexists>k. j = k @ i"
    and not_ij: "\<nexists>k. i = k @ j"
  shows "pp_n_prop_action j (pp_n_prop_lift i P) = Empty"
proof -
  have view_empty:
      "pp_view j (pp_lift i (pp_n_bacon_extract P)) = {}"
    by (rule pp_view_lift_incomparable_suffixes[OF not_ji not_ij])
  show ?thesis
  proof (rule pp_n_bacon_extract_injective_on_domain)
    show "Elem (pp_n_prop_action j (pp_n_prop_lift i P))
        (Power Nat)"
      by (rule pp_n_prop_action_in_domain)
    show "Elem Empty (Power Nat)"
      by (simp add: Power subset_empty)
    show "pp_n_bacon_extract (pp_n_prop_action j (pp_n_prop_lift i P)) =
        pp_n_bacon_extract Empty"
      by (simp add: pp_n_bacon_extract_action pp_n_bacon_extract_lift
        pp_prop_action_def view_empty)
  qed
qed

text \<open>
  Thus clauses 1 and 2 of Bacon's Definition 8.1 are now represented exactly
  at proposition type in HOL-ZF.  The next layer defines the recursive action
  on every function type by Definition 7.2 and proves its surjectivity.
\<close>


end
