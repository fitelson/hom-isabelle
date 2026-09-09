theory Bacon_Source_ZF_Degenerate_Premodel
  imports Bacon_Source_ZF_Action_Premodel
begin

section \<open>A genuine premodel with empty relational stocks\<close>

text \<open>
  Definition 3.18, p.55, permits empty proposition and arrow fibers.
  This example has one object and one arrow. Its individual fiber
  contains Empty; every other selected fiber is empty. Transport is
  the identity at individuals. At other types its total HOL extension
  returns Singleton Empty, a choice unconstrained on empty fibers.

  These are actual actions and subactions, not assumed certificates.
  The example is a premodel only, not an action model or a BBK model.
  Its off-domain extension has no meaning as a source action map.
\<close>

definition paper_ZF_degenerate_arrows :: ZF where
  "paper_ZF_degenerate_arrows = Singleton Empty"

definition paper_ZF_degenerate_domain :: "otype \<Rightarrow> unit \<Rightarrow> ZF" where
  "paper_ZF_degenerate_domain \<rho> W = (if \<rho> = Ind then Singleton Empty else Empty)"

definition paper_ZF_degenerate_transport :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_degenerate_transport \<rho> h x = (if \<rho> = Ind then x else Singleton Empty)"

lemma paper_ZF_degenerate_Prop_domain:
  "paper_ZF_degenerate_domain Prop = (\<lambda>W. Empty)"
  by (rule ext; simp add: paper_ZF_degenerate_domain_def)

lemma paper_ZF_degenerate_arrow_set:
  "explode paper_ZF_degenerate_arrows = {Empty}"
  by (auto simp: paper_ZF_degenerate_arrows_def explode_Elem Singleton)

lemma paper_ZF_degenerate_category:
  "paper_category {()} (explode paper_ZF_degenerate_arrows)
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)"
  by unfold_locales (auto simp: paper_ZF_degenerate_arrow_set)

lemma paper_ZF_degenerate_rooted:
  "paper_rooted_category {()} (explode paper_ZF_degenerate_arrows)
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty) ()"
  by unfold_locales (auto simp: paper_ZF_degenerate_arrow_set)

lemma paper_ZF_degenerate_action:
  "paper_action {()} (explode paper_ZF_degenerate_arrows)
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
    (\<lambda>W. explode (paper_ZF_degenerate_domain \<rho> W)) (paper_ZF_degenerate_transport \<rho>)"
  by unfold_locales
    (auto simp: paper_ZF_degenerate_arrow_set paper_ZF_degenerate_domain_def
      paper_ZF_degenerate_transport_def explode_Elem Empty Singleton split: if_splits)

lemma paper_ZF_degenerate_Prop_subaction:
  "paper_subaction {()} (explode paper_ZF_degenerate_arrows)
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
    (\<lambda>W. explode (paper_ZF_degenerate_domain Prop W)) (paper_ZF_degenerate_transport Prop)
    (\<lambda>W. explode (paper_ZF_powerset_code paper_ZF_degenerate_arrows (\<lambda>_. ()) W))
    (paper_ZF_powerset_transport_code paper_ZF_degenerate_arrows (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty))"
proof (rule paper_subactionI)
  show "paper_action {()} (explode paper_ZF_degenerate_arrows)
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
      (\<lambda>W. explode (paper_ZF_degenerate_domain Prop W)) (paper_ZF_degenerate_transport Prop)"
    by (rule paper_ZF_degenerate_action)
next
  show "paper_action {()} (explode paper_ZF_degenerate_arrows)
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
      (\<lambda>W. explode (paper_ZF_powerset_code paper_ZF_degenerate_arrows (\<lambda>_. ()) W))
      (paper_ZF_powerset_transport_code paper_ZF_degenerate_arrows (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty))"
    by (rule paper_ZF_powerset_action[OF paper_ZF_degenerate_category])
qed (auto simp: paper_ZF_degenerate_domain_def explode_Elem Empty)

lemma paper_ZF_degenerate_arrow_subaction:
  "paper_subaction {()} (explode paper_ZF_degenerate_arrows)
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
    (\<lambda>W. explode (paper_ZF_degenerate_domain (Arr \<sigma> \<tau>) W))
    (paper_ZF_degenerate_transport (Arr \<sigma> \<tau>))
    (\<lambda>W. explode (paper_ZF_exponential_code paper_ZF_degenerate_arrows
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty)
      (paper_ZF_degenerate_domain \<sigma>) (paper_ZF_degenerate_transport \<sigma>)
      (paper_ZF_degenerate_domain \<tau>) (paper_ZF_degenerate_transport \<tau>) W))
    (paper_ZF_exponential_transport_code paper_ZF_degenerate_arrows
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (paper_ZF_degenerate_domain \<sigma>))"
proof -
  interpret Pair: paper_ZF_action_pair "{()}" paper_ZF_degenerate_arrows
      "\<lambda>_. ()" "\<lambda>_. ()" "\<lambda>g f. Empty" "\<lambda>_. Empty"
      "paper_ZF_degenerate_domain \<sigma>" "paper_ZF_degenerate_transport \<sigma>"
      "paper_ZF_degenerate_domain \<tau>" "paper_ZF_degenerate_transport \<tau>"
    by unfold_locales
      (auto simp: paper_ZF_degenerate_arrow_set paper_ZF_degenerate_domain_def
        paper_ZF_degenerate_transport_def explode_Elem Empty Singleton split: if_splits)
  show ?thesis
    by (rule paper_subactionI[OF paper_ZF_degenerate_action Pair.paper_ZF_exponential_action])
      (auto simp: paper_ZF_degenerate_domain_def explode_Elem Empty)
qed

theorem paper_ZF_degenerate_premodel:
  "paper_ZF_action_premodel (\<lambda>\<rho>. {} :: 'c set) {()} paper_ZF_degenerate_arrows
    (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty) ()
    paper_ZF_degenerate_domain paper_ZF_degenerate_transport (\<lambda>\<rho> c. Empty)"
proof (rule paper_ZF_action_premodelI[OF paper_ZF_degenerate_rooted])
  show "paper_action {()} (explode paper_ZF_degenerate_arrows)
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
      (\<lambda>M. explode (paper_ZF_degenerate_domain \<rho> M)) (paper_ZF_degenerate_transport \<rho>)"
    if "paper_R_type \<rho>" for \<rho>
    by (rule paper_ZF_degenerate_action)
next
  show "explode (paper_ZF_degenerate_domain Ind M) \<noteq> {}" if "M \<in> {()}" for M
    by (auto simp: paper_ZF_degenerate_domain_def explode_Elem Singleton)
next
  show "paper_subaction {()} (explode paper_ZF_degenerate_arrows)
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
      (\<lambda>M. explode (paper_ZF_degenerate_domain Prop M)) (paper_ZF_degenerate_transport Prop)
      (\<lambda>M. explode (paper_ZF_powerset_code paper_ZF_degenerate_arrows (\<lambda>_. ()) M))
      (paper_ZF_powerset_transport_code paper_ZF_degenerate_arrows (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty))"
    by (rule paper_ZF_degenerate_Prop_subaction)
next
  show "paper_subaction {()} (explode paper_ZF_degenerate_arrows)
      (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (\<lambda>_. Empty)
      (\<lambda>M. explode (paper_ZF_degenerate_domain (Arr \<sigma> \<tau>) M)) (paper_ZF_degenerate_transport (Arr \<sigma> \<tau>))
      (\<lambda>M. explode (paper_ZF_exponential_code paper_ZF_degenerate_arrows
        (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty)
        (paper_ZF_degenerate_domain \<sigma>) (paper_ZF_degenerate_transport \<sigma>)
        (paper_ZF_degenerate_domain \<tau>) (paper_ZF_degenerate_transport \<tau>) M))
      (paper_ZF_exponential_transport_code paper_ZF_degenerate_arrows
        (\<lambda>_. ()) (\<lambda>_. ()) (\<lambda>g f. Empty) (paper_ZF_degenerate_domain \<sigma>))"
    if "paper_R_type (Arr \<sigma> \<tau>)" for \<sigma> \<tau>
    by (rule paper_ZF_degenerate_arrow_subaction)
next
  show "Empty \<in> explode (paper_ZF_degenerate_domain \<rho> ())"
    if "paper_R_type \<rho>" and "c \<in> ({} :: 'c set)" for \<rho> c
    using that(2) by simp
qed

end
