theory Bacon_PP_Axiom_Soundness
  imports 
    "Goodman_Legacy_01.Bacon_CEV_Axiom_Extension"
begin

section \<open>A soundness interface for the axiom-extension calculus\<close>

text \<open>
  The consensus review of 2026-07-25 identified the first thing this project needs:
  a statement of what a positive answer to Goodman's question would actually have to
  establish.  The natural formalization of the question is
  \<open>CEV_axiom_consistent [] pp_recombination_PP_axioms\<close>, and until there is a
  soundness theorem for that calculus, no semantic result can bear on it.  This theory
  supplies the theorem.

  It is deliberately \emph{not} a model construction.  It is a locale enumerating the
  semantic obligations, together with the conditional theorem: if every member of
  \<open>T\<close> is globally valid in a structure meeting those obligations, then \<open>T\<close> is
  consistent as an axiom extension of CEV.  Everything downstream must then be aimed
  at discharging the obligations for a particular structure.

  Two design points matter, and both are responses to defects the review identified.

  First, \emph{denotable rather than full function spaces}.  The existing
  \<open>applicative_structure\<close> locale of \<open>Bacon_Semantics\<close> requires \<open>lam_den_type\<close>: a
  denotation for \emph{every} meta-function from one domain into another.  That is
  full-function comprehension, and it makes countable Henkin domains impossible once
  a source domain is infinite and the target nontrivial.  The locale below never
  quantifies over meta-functions.  It asks only that the denotation of a well-typed
  \emph{term} lie in the domain of its type, which is what a Henkin model provides.

  Second, \emph{global validity}.  The axiom-extension calculus proves necessitation
  above the added axioms, so the members of \<open>T\<close> must hold at every world, not merely
  at a distinguished one.  Root-level truth is not enough, and the interface is
  written so that a root-level theorem cannot be mistaken for the obligation.
\<close>

subsection \<open>Environments\<close>

definition env_ok ::
    "('u \<Rightarrow> bool) list \<Rightarrow> 'u list \<Rightarrow> bool" where
  "env_ok Ds env \<longleftrightarrow>
    length env = length Ds \<and>
    (\<forall>k < length Ds. (Ds ! k) (env ! k))"

lemma env_ok_Nil[simp]: "env_ok [] []"
  by (simp add: env_ok_def)

lemma env_ok_Cons:
  assumes "d x" and "env_ok Ds env"
  shows "env_ok (d # Ds) (x # env)"
  using assms by (auto simp: env_ok_def nth_Cons')

subsection \<open>The interface\<close>

locale henkin_action_model =
  fixes dom :: "otype \<Rightarrow> 'u \<Rightarrow> bool"
    and holds :: "'u \<Rightarrow> 'w \<Rightarrow> bool"
    and den :: "oterm \<Rightarrow> 'u list \<Rightarrow> 'u"
  assumes
    \<comment> \<open>Denotable function spaces.  No quantification over meta-functions.\<close>
    den_type:
      "\<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow> env_ok (map dom \<Gamma>) env \<Longrightarrow>
        dom \<sigma> (den A env)"
  and den_Neg:
      "holds (den (Neg A) env) w \<longleftrightarrow> \<not> holds (den A env) w"
  and den_Imp:
      "holds (den (Imp A B) env) w \<longleftrightarrow>
        (holds (den A env) w \<longrightarrow> holds (den B env) w)"
  and den_Forall:
      "holds (den (Forall \<sigma> Q) env) w \<longleftrightarrow>
        (\<forall>x. dom \<sigma> x \<longrightarrow> holds (den Q (x # env)) w)"
  and den_Exists:
      "holds (den (Exists \<sigma> P) env) w \<longleftrightarrow>
        (\<exists>x. dom \<sigma> x \<and> holds (den P (x # env)) w)"
  and den_shift:
      "den (shift A) (x # env) = den A env"
  and dom_nonempty:
      "\<exists>x. dom \<sigma> x"
begin

text \<open>
  Global validity: true at every world, under every well-typed environment.  This is
  the notion the axiom-extension calculus requires, because it proves necessitation
  above the added axioms.
\<close>

definition gvalid :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "gvalid \<Gamma> A \<longleftrightarrow>
    (\<forall>env. env_ok (map dom \<Gamma>) env \<longrightarrow>
      (\<forall>w. holds (den A env) w))"

definition gvalid_set :: "oterm set \<Rightarrow> bool" where
  "gvalid_set T \<longleftrightarrow> (\<forall>\<Gamma> A. A \<in> T \<longrightarrow> gvalid \<Gamma> A)"

lemma gvalidI:
  assumes "\<And>env w. env_ok (map dom \<Gamma>) env \<Longrightarrow>
    holds (den A env) w"
  shows "gvalid \<Gamma> A"
  using assms unfolding gvalid_def by blast

lemma gvalidD:
  assumes "gvalid \<Gamma> A" and "env_ok (map dom \<Gamma>) env"
  shows "holds (den A env) w"
  using assms unfolding gvalid_def by blast

subsection \<open>Falsity is not globally valid\<close>

lemma holds_ObjTrue: "holds (den ObjTrue env) w"
  unfolding ObjTrue_def
  by (simp add: den_Forall den_Imp)

lemma not_holds_ObjFalse: "\<not> holds (den ObjFalse env) w"
  unfolding ObjFalse_def
  by (simp add: den_Neg holds_ObjTrue)

theorem ObjFalse_not_gvalid: "\<not> gvalid [] ObjFalse"
proof
  assume "gvalid [] ObjFalse"
  then have "holds (den ObjFalse []) w" for w :: 'w
    by (rule gvalidD) simp
  then show False
    using not_holds_ObjFalse by blast
qed

end

subsection \<open>The soundness theorem\<close>

text \<open>
  Two further obligations are carried as explicit hypotheses rather than folded into
  the locale, because they are exactly the two things a concrete model must earn and
  they should be visible in the statement.

  \<open>base_sound\<close> is the background modelhood obligation: every theorem of the already
  certified CEV calculus is globally valid.  \<open>zeta_sound\<close> is the vector-equivalence
  obligation.  Discharging the latter for a concrete model means showing that identity
  at a \<open>Prop\<close>-valued arrow type is pointwise agreement over the domains, and then
  pushing that through the \<open>app_vec\<close> and \<open>fresh_vars\<close> bookkeeping of \<open>zeta_body\<close>;
  that bookkeeping is where the work is, and it is not done here.
\<close>

theorem (in henkin_action_model) CEV_axiom_soundness:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and axioms_valid: "gvalid_set T"
    and derivable: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "gvalid \<Gamma> A"
  using derivable axioms_valid
proof (induct rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  then show ?case
    unfolding gvalid_set_def by blast
next
  case (Base \<Gamma> A T)
  show ?case using Base.hyps(1) by (rule base_sound)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  have body: "gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G)"
    using VectorEquivalence.hyps(4) VectorEquivalence.prems by blast
  show ?case
    by (rule zeta_sound[OF VectorEquivalence.hyps(1)
        VectorEquivalence.hyps(2) body])
next
  case (MP \<Gamma> T A B)
  show ?case
  proof (rule gvalidI)
    fix env w
    assume e: "env_ok (map dom \<Gamma>) env"
    have "holds (den A env) w"
      using MP.hyps(2)[OF MP.prems] e by (rule gvalidD)
    moreover have "holds (den (Imp A B) env) w"
      using MP.hyps(4)[OF MP.prems] e by (rule gvalidD)
    ultimately show "holds (den B env) w"
      by (simp add: den_Imp)
  qed
next
  case (Gen \<Gamma> P \<sigma> Q T)
  show ?case
  proof (rule gvalidI)
    fix env w
    assume e: "env_ok (map dom \<Gamma>) env"
    show "holds (den (Imp P (Forall \<sigma> Q)) env) w"
      unfolding den_Imp
    proof
      assume p: "holds (den P env) w"
      show "holds (den (Forall \<sigma> Q) env) w"
        unfolding den_Forall
      proof (intro allI impI)
        fix x
        assume x: "dom \<sigma> x"
        have e': "env_ok (map dom (\<sigma> # \<Gamma>)) (x # env)"
          using x e by (simp add: env_ok_Cons)
        have "holds (den (Imp (shift P) Q) (x # env)) w"
          using Gen.hyps(4)[OF Gen.prems] e' by (rule gvalidD)
        then have "holds (den (shift P) (x # env)) w \<longrightarrow>
            holds (den Q (x # env)) w"
          by (simp add: den_Imp)
        moreover have "holds (den (shift P) (x # env)) w"
          using p by (simp add: den_shift)
        ultimately show "holds (den Q (x # env)) w" by blast
      qed
    qed
  qed
next
  case (Inst \<sigma> \<Gamma> P Q T)
  show ?case
  proof (rule gvalidI)
    fix env w
    assume e: "env_ok (map dom \<Gamma>) env"
    show "holds (den (Imp (Exists \<sigma> P) Q) env) w"
      unfolding den_Imp
    proof
      assume "holds (den (Exists \<sigma> P) env) w"
      then obtain x where x: "dom \<sigma> x"
        and px: "holds (den P (x # env)) w"
        by (auto simp: den_Exists)
      have e': "env_ok (map dom (\<sigma> # \<Gamma>)) (x # env)"
        using x e by (simp add: env_ok_Cons)
      have "holds (den (Imp P (shift Q)) (x # env)) w"
        using Inst.hyps(4)[OF Inst.prems] e' by (rule gvalidD)
      then have "holds (den (shift Q) (x # env)) w"
        using px by (simp add: den_Imp)
      then show "holds (den Q env) w"
        by (simp add: den_shift)
    qed
  qed
qed

subsection \<open>Consistency of a globally valid axiom set\<close>

theorem (in henkin_action_model) CEV_axiom_consistent_of_gvalid:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and axioms_valid: "gvalid_set T"
  shows "CEV_axiom_consistent [] T"
  unfolding CEV_axiom_consistent_def
proof
  assume "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  with base_sound zeta_sound axioms_valid
  have "gvalid [] ObjFalse"
    by (rule CEV_axiom_soundness)
  then show False
    using ObjFalse_not_gvalid by blast
qed

subsection \<open>Instantiation to Goodman's question\<close>

text \<open>
  The target.  A positive answer needs a structure meeting the locale obligations in
  which the CEV theorems and the vector-equivalence principle are globally valid, and
  in which every member of \<open>pp_recombination_PP_axioms\<close> --- the target PP instance,
  Recombination, the two fundamentality components, and the three unbounded-type
  schemas --- holds at every world under every well-typed environment.
\<close>

theorem (in henkin_action_model) pp_recombination_question_of_gvalid:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and axioms_valid: "gvalid_set pp_recombination_PP_axioms"
  shows "pp_recombination_axiom_consistency_question"
  unfolding pp_recombination_axiom_consistency_question_def
  using base_sound zeta_sound axioms_valid
  by (rule CEV_axiom_consistent_of_gvalid)

theorem (in henkin_action_model) pp_full_QLN_question_of_gvalid:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and axioms_valid: "gvalid_set pp_full_QLN_PP_axioms"
  shows "pp_full_QLN_axiom_consistency_question"
  unfolding pp_full_QLN_axiom_consistency_question_def
  using base_sound zeta_sound axioms_valid
  by (rule CEV_axiom_consistent_of_gvalid)

subsection \<open>The locale is satisfiable\<close>

text \<open>
  A locale with contradictory assumptions proves everything, so the interface is worth
  nothing until it is shown inhabitable.  The following collapsed structure does that:
  values are booleans, every domain is everything, a world sees a value as its own
  truth value, and a term's value ignores its environment and its binders.

  This witness establishes only non-vacuity of the locale.  It does \emph{not} satisfy
  \<open>base_sound\<close> or \<open>zeta_sound\<close>, which are hypotheses of the theorems rather than
  locale axioms; supplying a structure that satisfies those as well is exactly the
  remaining work, and is the point of the checklist below.
\<close>

fun triv_val :: "oterm \<Rightarrow> bool" where
  "triv_val (Var n) = True"
| "triv_val (Const c \<sigma>) = True"
| "triv_val (App M N) = True"
| "triv_val (Lam \<sigma> M) = True"
| "triv_val (Eq \<sigma> M N) = (triv_val M = triv_val N)"
| "triv_val (Neg A) = (\<not> triv_val A)"
| "triv_val (Conj A B) = (triv_val A \<and> triv_val B)"
| "triv_val (Disj A B) = (triv_val A \<or> triv_val B)"
| "triv_val (Imp A B) = (triv_val A \<longrightarrow> triv_val B)"
| "triv_val (Forall \<sigma> A) = triv_val A"
| "triv_val (Exists \<sigma> A) = triv_val A"

lemma triv_val_rename[simp]:
  "triv_val (rename \<rho> A) = triv_val A"
  by (induct A arbitrary: \<rho>) simp_all

lemma triv_val_shift[simp]:
  "triv_val (shift A) = triv_val A"
  by (simp add: shift_def)

interpretation triv_model:
  henkin_action_model
    "\<lambda>\<sigma> x. True"
    "\<lambda>x (w :: unit). x"
    "\<lambda>A env. triv_val A"
  by unfold_locales simp_all

text \<open>
  So the obligations below are non-trivially satisfiable and the conditional theorems
  are not vacuous.
\<close>

subsection \<open>The obligation checklist\<close>

text \<open>
  What a positive answer now has to deliver, in the order the interface exposes it.

  \begin{enumerate}
  \item A structure --- domains \<open>dom\<close>, worlds, denotation \<open>den\<close> --- satisfying the
        locale.  Note what is \emph{not} required: no denotation for arbitrary
        meta-functions, so countable Henkin domains are admissible, which they are not
        under \<open>applicative_structure\<close>.
  \item \<open>base_sound\<close>: every CEV theorem globally valid.  This is background
        modelhood, and it is one hypothesis rather than a scattered obligation.
  \item \<open>zeta_sound\<close>: vector equivalence.  Pointwise identity at \<open>Prop\<close>-valued arrow
        types, pushed through the \<open>app_vec\<close>/\<open>fresh_vars\<close> bookkeeping.
  \item \<open>gvalid_set pp_recombination_PP_axioms\<close>: every axiom true at \emph{every}
        world under \emph{every} well-typed environment.  This is where the
        fixed-\<open>Fun\<close> all-worlds core lives, and where the existing root-level witness
        theorems do not reach.
  \end{enumerate}

  The value of the interface is that these are now four separable jobs with a
  machine-checked statement of how they combine, rather than one undivided
  aspiration.  It also makes the negative discipline explicit: a theorem about the
  word action bears on Goodman's question only by way of item 4, and only if stated
  at every world.
\<close>

end
