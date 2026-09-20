theory Bacon_PP_Goodman_T9_Infinitude
  imports 
    "Goodman_Legacy_T9_Cardinal.Bacon_PP_Goodman_T9"
begin

section \<open>Goodman Attack 3: excluding finitely many kinds\<close>

text \<open>
  T8 by itself distinguishes operators, not their kinds.  The argument below
  isolates the extra fact supplied by the type-correct Pure Completeness
  construction.  For each set \<open>S\<close> of kinds, let \<open>classifier S\<close> be the
  pure unary operator which, on an input represented as \<open>B r\<close>, says exactly
  that the kind of \<open>B\<close> belongs to \<open>S\<close>.

  If two such classifiers have the same kind, right composition by a pure
  invertible witnesses that equality.  On represented inputs this right
  composition induces left composition on the represented operator.  Left
  composition by an invertible permutes the kinds, so the two selected sets
  have the same cardinality.  A finite set of \<open>n\<close> kinds has subsets of
  each cardinality from \<open>0\<close> through \<open>n\<close>.  Their classifiers would
  therefore occupy \<open>n + 1\<close> different kinds, which is impossible.
\<close>

definition pp_T9_cardinality_representative ::
    "'a set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "pp_T9_cardinality_representative A n =
    (SOME B. B \<subseteq> A \<and> card B = n)"

lemma pp_T9_cardinality_representative_spec:
  assumes "n \<le> card A"
  shows
    "pp_T9_cardinality_representative A n \<subseteq> A"
    "card (pp_T9_cardinality_representative A n) = n"
proof -
  obtain B where "B \<subseteq> A" and "card B = n"
    using obtain_subset_with_card_n[OF assms] by blast
  then have ex: "\<exists>B. B \<subseteq> A \<and> card B = n"
    by blast
  have chosen:
      "(SOME B. B \<subseteq> A \<and> card B = n) \<subseteq> A
        \<and> card (SOME B. B \<subseteq> A \<and> card B = n) = n"
    using ex by (rule someI_ex)
  show "pp_T9_cardinality_representative A n \<subseteq> A"
    unfolding pp_T9_cardinality_representative_def
    using chosen by blast
  show "card (pp_T9_cardinality_representative A n) = n"
    unfolding pp_T9_cardinality_representative_def
    using chosen by blast
qed

theorem pp_T9_cardinality_separation_excludes_finite_kinds:
  fixes classifier_kind :: "'k set \<Rightarrow> 'k"
  assumes classifier_kind_in:
      "\<And>S. S \<subseteq> K \<Longrightarrow> classifier_kind S \<in> K"
    and collision_preserves_card:
      "\<And>S T. S \<subseteq> K \<Longrightarrow> T \<subseteq> K \<Longrightarrow>
        finite S \<Longrightarrow> finite T \<Longrightarrow>
        classifier_kind S = classifier_kind T \<Longrightarrow>
        card S = card T"
  shows "infinite K"
proof
  assume finite_K: "finite K"
  let ?I = "{..card K}"
  let ?S = "pp_T9_cardinality_representative K"
  let ?f = "\<lambda>n. classifier_kind (?S n)"
  have subset: "?S n \<subseteq> K" if "n \<in> ?I" for n
    using that pp_T9_cardinality_representative_spec(1)
    by simp
  have card_subset: "card (?S n) = n" if "n \<in> ?I" for n
    using that pp_T9_cardinality_representative_spec(2)
    by simp
  have finite_selected: "finite (?S n)" if "n \<in> ?I" for n
    using subset[OF that] finite_K by (rule finite_subset)
  have f_in: "?f ` ?I \<subseteq> K"
    using classifier_kind_in subset by blast
  have f_inj: "inj_on ?f ?I"
  proof (rule inj_onI)
    fix m n
    assume m: "m \<in> ?I" and n: "n \<in> ?I"
      and same: "?f m = ?f n"
    have "card (?S m) = card (?S n)"
      using subset[OF m] subset[OF n]
        finite_selected[OF m] finite_selected[OF n] same
      by (rule collision_preserves_card)
    then show "m = n"
      using card_subset[OF m] card_subset[OF n] by simp
  qed
  have image_card: "card (?f ` ?I) = Suc (card K)"
    using f_inj by (simp add: card_image)
  have "card (?f ` ?I) \<le> card K"
    using finite_K f_in by (rule card_mono)
  then show False
    using image_card by simp
qed

subsection \<open>The type-correct Pure Completeness and L2 bridge\<close>

definition pp_T9_selected_kind_representation ::
    "'u set \<Rightarrow> 'p set \<Rightarrow> ('s \<Rightarrow> 'u \<Rightarrow> bool) \<Rightarrow>
      ('u \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 's \<Rightarrow> 'p \<Rightarrow> bool"
where
  "pp_T9_selected_kind_representation P R selected eval Q p \<longleftrightarrow>
    (\<exists>B \<in> P. \<exists>q \<in> R. selected Q B \<and> p = eval B q)"

text \<open>
  Here \<open>Q\<close> has the higher selector type, corresponding to
  \<open>(t \<rightarrow> t) \<rightarrow> t\<close>.  The represented-kind property has the
  lower unary type \<open>t \<rightarrow> t\<close>.  Thus the theorem does not identify a
  Pure Completeness selector with the unary operator produced from it.
\<close>

theorem pp_T9_PC_L2_selected_kind_specification:
  fixes P :: "'u set"
    and R :: "'p set"
    and K :: "'k set"
    and pc :: "'k set \<Rightarrow> 's"
    and selected :: "'s \<Rightarrow> 'u \<Rightarrow> bool"
    and eval :: "'u \<Rightarrow> 'p \<Rightarrow> 'p"
    and kind :: "'u \<Rightarrow> 'k"
  assumes r: "r \<in> R"
    and B: "B \<in> P"
    and pc_specification:
      "\<And>S X. S \<subseteq> K \<Longrightarrow> X \<in> P \<Longrightarrow>
        (selected (pc S) X \<longleftrightarrow> kind X \<in> S)"
    and weak_L2:
      "\<And>X Y q s. X \<in> P \<Longrightarrow> Y \<in> P \<Longrightarrow>
        q \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
        eval X q = eval Y s \<Longrightarrow> kind X = kind Y"
    and S: "S \<subseteq> K"
  shows
    "pp_T9_selected_kind_representation P R selected eval (pc S)
        (eval B r)
      \<longleftrightarrow> kind B \<in> S"
proof
  assume represented:
    "pp_T9_selected_kind_representation P R selected eval (pc S)
      (eval B r)"
  then obtain X q where X: "X \<in> P" and q: "q \<in> R"
    and selected_X: "selected (pc S) X"
    and equation: "eval B r = eval X q"
    unfolding pp_T9_selected_kind_representation_def by blast
  have kind_X: "kind X \<in> S"
    using pc_specification[OF S X] selected_X by simp
  have "kind B = kind X"
    using weak_L2[OF B X r q] equation by simp
  then show "kind B \<in> S"
    using kind_X by simp
next
  assume kind_B: "kind B \<in> S"
  have selected_B: "selected (pc S) B"
    using pc_specification[OF S B] kind_B by simp
  show
    "pp_T9_selected_kind_representation P R selected eval (pc S)
      (eval B r)"
    unfolding pp_T9_selected_kind_representation_def
    using B r selected_B by blast
qed

corollary pp_T9_PC_L2_classifier_specification:
  fixes P :: "'u set"
    and R :: "'p set"
    and K :: "'k set"
    and pc :: "'k set \<Rightarrow> 's"
    and selected :: "'s \<Rightarrow> 'u \<Rightarrow> bool"
    and eval :: "'u \<Rightarrow> 'p \<Rightarrow> 'p"
    and kind :: "'u \<Rightarrow> 'k"
    and classifier :: "'k set \<Rightarrow> 'u"
    and holds :: "'p \<Rightarrow> bool"
  assumes r: "r \<in> R"
    and B: "B \<in> P"
    and pc_specification:
      "\<And>S X. S \<subseteq> K \<Longrightarrow> X \<in> P \<Longrightarrow>
        (selected (pc S) X \<longleftrightarrow> kind X \<in> S)"
    and weak_L2:
      "\<And>X Y q s. X \<in> P \<Longrightarrow> Y \<in> P \<Longrightarrow>
        q \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
        eval X q = eval Y s \<Longrightarrow> kind X = kind Y"
    and realization:
      "\<And>S p. S \<subseteq> K \<Longrightarrow>
        (holds (eval (classifier S) p) \<longleftrightarrow>
          pp_T9_selected_kind_representation
            P R selected eval (pc S) p)"
    and S: "S \<subseteq> K"
  shows
    "holds (eval (classifier S) (eval B r)) \<longleftrightarrow>
      kind B \<in> S"
proof -
  have represented:
      "pp_T9_selected_kind_representation P R selected eval (pc S)
          (eval B r)
        \<longleftrightarrow> kind B \<in> S"
    using r B pc_specification weak_L2 S
    by (rule pp_T9_PC_L2_selected_kind_specification)
  show ?thesis
    using realization[OF S, of "eval B r"] represented by simp
qed

subsection \<open>The action of reversible operators on kinds\<close>

locale pp_T9_kind_classifier_action =
  fixes P :: "'u set"
    and G :: "'u set"
    and K :: "'k set"
    and kind :: "'u \<Rightarrow> 'k"
    and compose :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and eval :: "'u \<Rightarrow> 'p \<Rightarrow> 'p"
    and holds :: "'p \<Rightarrow> bool"
    and r :: 'p
    and classifier :: "'k set \<Rightarrow> 'u"
  assumes represented:
      "\<And>k. k \<in> K \<Longrightarrow> \<exists>B \<in> P. kind B = k"
    and kind_closed: "kind ` P \<subseteq> K"
    and group_pure: "G \<subseteq> P"
    and compose_pure:
      "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> compose A B \<in> P"
    and compose_associative:
      "\<And>A B C. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> C \<in> P \<Longrightarrow>
        compose A (compose B C) = compose (compose A B) C"
    and application_of_compose:
      "\<And>A B p. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
        eval (compose A B) p = eval A (eval B p)"
    and kind_is_right_orbit:
      "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
        (kind A = kind B \<longleftrightarrow>
          (\<exists>Z \<in> G. A = compose B Z))"
    and group_inverse:
      "\<And>Z. Z \<in> G \<Longrightarrow>
        \<exists>I \<in> G. \<forall>B \<in> P.
          compose I (compose Z B) = B
          \<and> compose Z (compose I B) = B"
    and classifier_pure:
      "\<And>S. S \<subseteq> K \<Longrightarrow> classifier S \<in> P"
    and classifier_specification:
      "\<And>S B. S \<subseteq> K \<Longrightarrow> B \<in> P \<Longrightarrow>
        (holds (eval (classifier S) (eval B r)) \<longleftrightarrow>
          kind B \<in> S)"
begin

definition representative :: "'k \<Rightarrow> 'u" where
  "representative k = (SOME B. B \<in> P \<and> kind B = k)"

lemma representative_spec:
  assumes "k \<in> K"
  shows "representative k \<in> P" "kind (representative k) = k"
proof -
  obtain B where "B \<in> P" and "kind B = k"
    using represented[OF assms] by blast
  then have ex: "\<exists>B. B \<in> P \<and> kind B = k"
    by blast
  have chosen:
      "(SOME B. B \<in> P \<and> kind B = k) \<in> P
        \<and> kind (SOME B. B \<in> P \<and> kind B = k) = k"
    using ex by (rule someI_ex)
  show "representative k \<in> P"
    unfolding representative_def using chosen by blast
  show "kind (representative k) = k"
    unfolding representative_def using chosen by blast
qed

definition left_action :: "'u \<Rightarrow> 'k \<Rightarrow> 'k" where
  "left_action Z k = kind (compose Z (representative k))"

lemma left_composition_respects_kind:
  assumes Z: "Z \<in> G"
    and B: "B \<in> P"
    and C: "C \<in> P"
    and same: "kind B = kind C"
  shows "kind (compose Z B) = kind (compose Z C)"
proof -
  have ZP: "Z \<in> P"
    using group_pure Z by blast
  obtain H where H: "H \<in> G" and B_eq: "B = compose C H"
    using kind_is_right_orbit[OF B C] same by blast
  have HP: "H \<in> P"
    using group_pure H by blast
  have ZB: "compose Z B \<in> P"
    using compose_pure[OF ZP B] .
  have ZC: "compose Z C \<in> P"
    using compose_pure[OF ZP C] .
  have equation: "compose Z B = compose (compose Z C) H"
    using compose_associative[OF ZP C HP]
    unfolding B_eq by simp
  show ?thesis
    using kind_is_right_orbit[OF ZB ZC] H equation by blast
qed

lemma left_action_in:
  assumes Z: "Z \<in> G" and k: "k \<in> K"
  shows "left_action Z k \<in> K"
proof -
  have ZP: "Z \<in> P"
    using group_pure Z by blast
  have repP: "representative k \<in> P"
    using representative_spec(1)[OF k] .
  have "compose Z (representative k) \<in> P"
    using compose_pure[OF ZP repP] .
  then show ?thesis
    unfolding left_action_def using kind_closed by blast
qed

lemma left_action_bijective:
  assumes Z: "Z \<in> G"
  shows "bij_betw (left_action Z) K K"
proof -
  obtain I where I: "I \<in> G"
    and inverse:
      "\<forall>B \<in> P.
        compose I (compose Z B) = B
        \<and> compose Z (compose I B) = B"
    using group_inverse[OF Z] by blast
  have ZP: "Z \<in> P"
    using group_pure Z by blast
  have IP: "I \<in> P"
    using group_pure I by blast
  have into: "left_action Z ` K \<subseteq> K"
    using left_action_in[OF Z] by blast
  have inj: "inj_on (left_action Z) K"
  proof (rule inj_onI)
    fix k l
    assume k: "k \<in> K" and l: "l \<in> K"
      and same: "left_action Z k = left_action Z l"
    have repk: "representative k \<in> P"
      using representative_spec(1)[OF k] .
    have repl: "representative l \<in> P"
      using representative_spec(1)[OF l] .
    have Zk: "compose Z (representative k) \<in> P"
      using compose_pure[OF ZP repk] .
    have Zl: "compose Z (representative l) \<in> P"
      using compose_pure[OF ZP repl] .
    have same_Z:
        "kind (compose Z (representative k)) =
         kind (compose Z (representative l))"
      using same unfolding left_action_def .
    have after_inverse:
        "kind (compose I (compose Z (representative k))) =
         kind (compose I (compose Z (representative l)))"
      using left_composition_respects_kind[OF I Zk Zl same_Z] .
    have "kind (representative k) = kind (representative l)"
      using inverse repk repl after_inverse by simp
    then show "k = l"
      using representative_spec(2)[OF k]
        representative_spec(2)[OF l] by simp
  qed
  have onto: "K \<subseteq> left_action Z ` K"
  proof
    fix k
    assume k: "k \<in> K"
    let ?B = "representative k"
    have BP: "?B \<in> P"
      using representative_spec(1)[OF k] .
    have IBP: "compose I ?B \<in> P"
      using compose_pure[OF IP BP] .
    let ?j = "kind (compose I ?B)"
    have j: "?j \<in> K"
      using kind_closed IBP by blast
    have repj: "representative ?j \<in> P"
      using representative_spec(1)[OF j] .
    have same_j: "kind (representative ?j) = kind (compose I ?B)"
      using representative_spec(2)[OF j] by simp
    have transported:
        "kind (compose Z (representative ?j)) =
         kind (compose Z (compose I ?B))"
      using left_composition_respects_kind[OF Z repj IBP same_j] .
    have "left_action Z ?j = k"
      unfolding left_action_def
      using inverse BP transported representative_spec(2)[OF k]
      by simp
    then have "k = left_action Z ?j"
      by simp
    then show "k \<in> left_action Z ` K"
      using j by (rule image_eqI)
  qed
  show ?thesis
    unfolding bij_betw_def
    using inj into onto by blast
qed

lemma classifier_collision_covariance:
  assumes S: "S \<subseteq> K"
    and T: "T \<subseteq> K"
    and same: "kind (classifier S) = kind (classifier T)"
  obtains Z where
    "Z \<in> G"
    "bij_betw (left_action Z) K K"
    "left_action Z ` S = T"
proof -
  have cS: "classifier S \<in> P"
    using classifier_pure[OF S] .
  have cT: "classifier T \<in> P"
    using classifier_pure[OF T] .
  have orbit:
      "\<exists>Z \<in> G. classifier S = compose (classifier T) Z"
    using kind_is_right_orbit[OF cS cT] same by (rule iffD1)
  obtain Z where Z: "Z \<in> G"
    and classifier_eq: "classifier S = compose (classifier T) Z"
    using orbit by (elim bexE)
  have ZP: "Z \<in> P"
    using group_pure Z by (rule subsetD)
  have bij: "bij_betw (left_action Z) K K"
    using left_action_bijective[OF Z] .
  have membership:
      "k \<in> S \<longleftrightarrow> left_action Z k \<in> T" if k: "k \<in> K" for k
  proof -
    let ?B = "representative k"
    have BP: "?B \<in> P"
      using representative_spec(1)[OF k] .
    have ZB: "compose Z ?B \<in> P"
      using compose_pure[OF ZP BP] .
    have cTZ: "compose (classifier T) Z \<in> P"
      using compose_pure[OF cT ZP] .
    have classifier_application:
        "eval (classifier S) (eval ?B r) =
         eval (classifier T) (eval (compose Z ?B) r)"
    proof -
      have
        "eval (classifier S) (eval ?B r) =
         eval (compose (classifier T) Z) (eval ?B r)"
        using classifier_eq by simp
      also have "... = eval (classifier T) (eval Z (eval ?B r))"
        using application_of_compose[OF cT ZP] by simp
      also have "... = eval (classifier T) (eval (compose Z ?B) r)"
        using application_of_compose[OF ZP BP] by simp
      finally show ?thesis .
    qed
    have
      "k \<in> S \<longleftrightarrow>
       holds (eval (classifier S) (eval ?B r))"
      using classifier_specification[OF S BP]
        representative_spec(2)[OF k] by simp
    also have "... \<longleftrightarrow>
      holds (eval (classifier T) (eval (compose Z ?B) r))"
      using classifier_application by simp
    also have "... \<longleftrightarrow> kind (compose Z ?B) \<in> T"
      using classifier_specification[OF T ZB] by simp
    also have "... \<longleftrightarrow> left_action Z k \<in> T"
      by (simp add: left_action_def)
    finally show ?thesis .
  qed
  have image_eq: "left_action Z ` S = T"
  proof
    show "left_action Z ` S \<subseteq> T"
    proof
      fix k
      assume "k \<in> left_action Z ` S"
      then obtain j where jS: "j \<in> S"
        and k: "k = left_action Z j"
        by (elim imageE)
      have jK: "j \<in> K"
        using S jS by (rule subsetD)
      have "left_action Z j \<in> T"
        using membership[OF jK] jS by simp
      then show "k \<in> T"
        unfolding k .
    qed
    show "T \<subseteq> left_action Z ` S"
    proof
      fix k
      assume kT: "k \<in> T"
      have kK: "k \<in> K"
        using T kT by (rule subsetD)
      have image_K: "left_action Z ` K = K"
        using bij unfolding bij_betw_def by simp
      have "k \<in> left_action Z ` K"
        using kK image_K by simp
      obtain j where jK: "j \<in> K" and jk: "left_action Z j = k"
        using \<open>k \<in> left_action Z ` K\<close>
        by (elim imageE) simp
      have "j \<in> S"
        using membership[OF jK] jk kT by simp
      then have "left_action Z j \<in> left_action Z ` S"
        by (rule imageI)
      then show "k \<in> left_action Z ` S"
        using jk by simp
    qed
  qed
  show thesis
    using that[OF Z bij image_eq] .
qed

lemma classifier_collision_preserves_card:
  assumes S: "S \<subseteq> K"
    and T: "T \<subseteq> K"
    and finite_S: "finite S"
    and finite_T: "finite T"
    and same: "kind (classifier S) = kind (classifier T)"
  shows "card S = card T"
proof -
  obtain Z where bij: "bij_betw (left_action Z) K K"
    and image: "left_action Z ` S = T"
    using classifier_collision_covariance[OF S T same] by blast
  have inj: "inj_on (left_action Z) S"
    using bij S unfolding bij_betw_def
    by (meson inj_on_subset)
  have card_image_eq:
      "card (left_action Z ` S) = card S"
    using inj by (rule card_image)
  show ?thesis
    using card_image_eq image by simp
qed

theorem pp_T9_PC_excludes_finitely_many_kinds:
  shows "infinite K"
proof (rule pp_T9_cardinality_separation_excludes_finite_kinds)
  fix S
  assume "S \<subseteq> K"
  then have "classifier S \<in> P"
    by (rule classifier_pure)
  then show "kind (classifier S) \<in> K"
    using kind_closed by blast
next
  fix S T
  assume "S \<subseteq> K" "T \<subseteq> K"
    "finite S" "finite T"
    "kind (classifier S) = kind (classifier T)"
  then show "card S = card T"
    by (rule classifier_collision_preserves_card)
qed

end

subsection \<open>The repaired Attack 3 theorem\<close>

theorem pp_T9_PC_L2_infinitely_many_kinds:
  fixes P :: "'u set"
    and G :: "'u set"
    and R :: "'p set"
    and K :: "'k set"
    and kind :: "'u \<Rightarrow> 'k"
    and compose :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and eval :: "'u \<Rightarrow> 'p \<Rightarrow> 'p"
    and holds :: "'p \<Rightarrow> bool"
    and pc :: "'k set \<Rightarrow> 's"
    and selected :: "'s \<Rightarrow> 'u \<Rightarrow> bool"
    and classifier :: "'k set \<Rightarrow> 'u"
  assumes represented:
      "\<And>k. k \<in> K \<Longrightarrow> \<exists>B \<in> P. kind B = k"
    and kind_closed: "kind ` P \<subseteq> K"
    and group_pure: "G \<subseteq> P"
    and compose_pure:
      "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> compose A B \<in> P"
    and compose_associative:
      "\<And>A B C. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> C \<in> P \<Longrightarrow>
        compose A (compose B C) = compose (compose A B) C"
    and application_of_compose:
      "\<And>A B p. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
        eval (compose A B) p = eval A (eval B p)"
    and kind_is_right_orbit:
      "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
        (kind A = kind B \<longleftrightarrow>
          (\<exists>Z \<in> G. A = compose B Z))"
    and group_inverse:
      "\<And>Z. Z \<in> G \<Longrightarrow>
        \<exists>I \<in> G. \<forall>B \<in> P.
          compose I (compose Z B) = B
          \<and> compose Z (compose I B) = B"
    and classifier_pure:
      "\<And>S. S \<subseteq> K \<Longrightarrow> classifier S \<in> P"
    and r: "r \<in> R"
    and pc_specification:
      "\<And>S X. S \<subseteq> K \<Longrightarrow> X \<in> P \<Longrightarrow>
        (selected (pc S) X \<longleftrightarrow> kind X \<in> S)"
    and weak_L2:
      "\<And>X Y q s. X \<in> P \<Longrightarrow> Y \<in> P \<Longrightarrow>
        q \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
        eval X q = eval Y s \<Longrightarrow> kind X = kind Y"
    and realization:
      "\<And>S p. S \<subseteq> K \<Longrightarrow>
        (holds (eval (classifier S) p) \<longleftrightarrow>
          pp_T9_selected_kind_representation
            P R selected eval (pc S) p)"
  shows "infinite K"
proof -
  have classifier_specification:
      "\<And>S B. S \<subseteq> K \<Longrightarrow> B \<in> P \<Longrightarrow>
        (holds (eval (classifier S) (eval B r)) \<longleftrightarrow>
          kind B \<in> S)"
  proof -
    fix S B
    assume S: "S \<subseteq> K" and B: "B \<in> P"
    show
      "holds (eval (classifier S) (eval B r)) \<longleftrightarrow>
        kind B \<in> S"
      using r B pc_specification weak_L2 realization S
      by (rule pp_T9_PC_L2_classifier_specification)
  qed
  interpret action: pp_T9_kind_classifier_action
      P G K kind compose eval holds r classifier
  proof
    show "\<And>k. k \<in> K \<Longrightarrow> \<exists>B\<in>P. kind B = k"
      by (rule represented)
    show "kind ` P \<subseteq> K" by (rule kind_closed)
    show "G \<subseteq> P" by (rule group_pure)
    show "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> compose A B \<in> P"
      by (rule compose_pure)
    show "\<And>A B C. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow> C \<in> P \<Longrightarrow>
      compose A (compose B C) = compose (compose A B) C"
      by (rule compose_associative)
    show "\<And>A B p. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
      eval (compose A B) p = eval A (eval B p)"
      by (rule application_of_compose)
    show "\<And>A B. A \<in> P \<Longrightarrow> B \<in> P \<Longrightarrow>
      (kind A = kind B \<longleftrightarrow> (\<exists>Z\<in>G. A = compose B Z))"
      by (rule kind_is_right_orbit)
    show "\<And>Z. Z \<in> G \<Longrightarrow>
      \<exists>I\<in>G. \<forall>B\<in>P.
        compose I (compose Z B) = B \<and> compose Z (compose I B) = B"
      by (rule group_inverse)
    show "\<And>S. S \<subseteq> K \<Longrightarrow> classifier S \<in> P"
      by (rule classifier_pure)
    show "\<And>S B. S \<subseteq> K \<Longrightarrow> B \<in> P \<Longrightarrow>
      (holds (eval (classifier S) (eval B r)) \<longleftrightarrow> kind B \<in> S)"
      by (rule classifier_specification)
  qed
  show ?thesis
    by (rule action.pp_T9_PC_excludes_finitely_many_kinds)
qed

corollary pp_T9_attack3_forces_exponential_group:
  assumes infinite_kinds: "infinite K"
    and T9_counting: "|Pow K| \<le>o |K \<times> G|"
  shows "|Pow K| \<le>o |G|"
proof -
  have "finite K \<or> |Pow K| \<le>o |G|"
    using T9_counting by (rule pp_T9_cardinal_dichotomy)
  then show ?thesis
    using infinite_kinds by blast
qed

text \<open>
  The locale assumptions are the semantic content which must be discharged by
  the CEV+ interpretation.  The crucial classifier specification is
  type-correct: Pure Completeness first selects unary operators at type
  \<open>(t \<rightarrow> t) \<rightarrow> t\<close>, and the generalized T8 construction then
  converts that selector into a unary proposition operator.  Weak L2 proves
  the displayed specification at the chosen \<open>fun\<acute>\<close> proposition.  The
  theorem \<open>pp_T9_PC_L2_infinitely_many_kinds\<close> then excludes T9's finite
  horn.  No classification or cardinal ceiling for \<open>G\<close> is used in this
  infinitude proof.
\<close>

end
