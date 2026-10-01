theory Classicism_2_11_Order_Defs
  imports Classicism_2_11_Syntax
begin

section \<open>Order-theoretic interface for the relational carriers\<close>

text \<open>
  These definitions only name semantic notions; nothing here is a truth
  claim. Later theories prove that ≤, x ≤ ¬x, Atom and Atomicity express
  c211_pleq, c211_pempty, c211_patom and c211_patomic exactly, while
  c211_pcomplete (every HOL subset of the carrier has a GLB) is only a
  sufficient condition for Boolean Completeness, whose quantifier ranges
  over predicates of type τ→t. The generic notions are stated for an arbitrary action
  premodel presented by Ar, source, target and D. The order is
  inclusion of propositional leaves along every legitimate outgoing
  arrow and argument (the graph of a function object is total, so this
  is not set inclusion of graphs). The raw notions mirror them on the
  concrete carriers raw_D, before the arrow-coded encoding pc_enc.
\<close>

subsection \<open>Generic notions on D τ W\<close>

primrec c211_pleq :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    otype \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_pleq Ar source target D Ind W a b = (a = b)"
| "c211_pleq Ar source target D Prop W a b = (\<forall>j. Elem j a \<longrightarrow> Elem j b)"
| "c211_pleq Ar source target D (Arr \<sigma> \<rho>) W a b =
    (\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = W \<longrightarrow> Elem x (D \<sigma> (target i)) \<longrightarrow>
      c211_pleq Ar source target D \<rho> (target i) (app a (Opair i x)) (app b (Opair i x)))"

primrec c211_pempty :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    otype \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_pempty Ar source target D Ind W a = False"
| "c211_pempty Ar source target D Prop W a = (\<forall>j. \<not> Elem j a)"
| "c211_pempty Ar source target D (Arr \<sigma> \<rho>) W a =
    (\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = W \<longrightarrow> Elem x (D \<sigma> (target i)) \<longrightarrow>
      c211_pempty Ar source target D \<rho> (target i) (app a (Opair i x)))"

text \<open>The literal semantic reading of Atomτ y (its biconditional).\<close>

definition c211_patom :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    otype \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_patom Ar source target D \<tau> W y \<longleftrightarrow>
    (\<forall>z. Elem z (D \<tau> W) \<longrightarrow>
      ((c211_pleq Ar source target D \<tau> W z y \<and> z \<noteq> y) \<longleftrightarrow>
        c211_pempty Ar source target D \<tau> W z))"

definition c211_patomic :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    otype \<Rightarrow> 'o \<Rightarrow> bool" where
  "c211_patomic Ar source target D \<tau> W \<longleftrightarrow>
    (\<forall>x. Elem x (D \<tau> W) \<longrightarrow> c211_pempty Ar source target D \<tau> W x \<or>
      (\<exists>y. Elem y (D \<tau> W) \<and> c211_patom Ar source target D \<tau> W y \<and>
        c211_pleq Ar source target D \<tau> W y x))"

definition c211_pcomplete :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    otype \<Rightarrow> 'o \<Rightarrow> bool" where
  "c211_pcomplete Ar source target D \<tau> W \<longleftrightarrow>
    (\<forall>S. S \<subseteq> explode (D \<tau> W) \<longrightarrow>
      (\<exists>m. Elem m (D \<tau> W) \<and>
        (\<forall>z. Elem z (D \<tau> W) \<longrightarrow>
          ((\<forall>y\<in>S. c211_pleq Ar source target D \<tau> W z y) \<longleftrightarrow>
            c211_pleq Ar source target D \<tau> W z m))))"

lemma c211_patom_not_pempty:
  "Elem y (D \<tau> W) \<Longrightarrow> c211_patom Ar source target D \<tau> W y \<Longrightarrow>
    \<not> c211_pempty Ar source target D \<tau> W y"
  unfolding c211_patom_def by blast

subsection \<open>Rigidity of properties of propositions\<close>

text \<open>
  The intended semantic reading, at the root, of Rigid Y and of Rigid
  Comprehension for type t→t: the outer □ ranges over root arrows h,
  ∀X over D (t→t) (target h), the inner □ over arrows i out of
  target h. c211_pcur F V z says that F is currently true of z at V.
\<close>

definition c211_pcur :: "('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_pcur identity V F z \<longleftrightarrow> Elem (identity V) (app F (Opair (identity V) z))"

definition c211_prigid :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_prigid Ar source target identity D T Root y \<longleftrightarrow>
    (\<forall>h X. h \<in> explode Ar \<longrightarrow> source h = Root \<longrightarrow> Elem X (D (Arr Prop Prop) (target h)) \<longrightarrow>
      ((\<forall>z. Elem z (D Prop (target h)) \<longrightarrow>
          c211_pcur identity (target h) (T (Arr Prop Prop) h y) z \<longrightarrow>
          (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow>
            c211_pcur identity (target i) (T (Arr Prop Prop) i X) (T Prop i z)))
       \<longleftrightarrow> c211_pleq Ar source target D (Arr Prop Prop) (target h) (T (Arr Prop Prop) h y) X))"

definition c211_pRC :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> bool" where
  "c211_pRC Ar source target identity D T Root \<longleftrightarrow>
    (\<forall>x. Elem x (D (Arr Prop Prop) Root) \<longrightarrow>
      (\<exists>y. Elem y (D (Arr Prop Prop) Root) \<and> c211_prigid Ar source target identity D T Root y \<and>
        (\<forall>z. Elem z (D Prop Root) \<longrightarrow>
          (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z))))"

subsection \<open>Raw mirrors on the concrete carriers\<close>

primrec c211_rleq :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_rleq Ind w x y = (x = y)"
| "c211_rleq Prop w x y =
    (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow>
      raw_truth v (raw_T Prop w v x) \<longrightarrow> raw_truth v (raw_T Prop w v y))"
| "c211_rleq (Arr \<sigma> \<rho>) w F G =
    (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_rleq \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x)
        (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v G) x))"

primrec c211_rempty :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_rempty Ind w x = False"
| "c211_rempty Prop w x =
    (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> \<not> raw_truth v (raw_T Prop w v x))"
| "c211_rempty (Arr \<sigma> \<rho>) w F =
    (\<forall>v x. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem x (raw_D \<sigma> v) \<longrightarrow>
      c211_rempty \<rho> v (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x))"

definition c211_ratom :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_ratom \<tau> w y \<longleftrightarrow>
    (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow>
      ((c211_rleq \<tau> w z y \<and> z \<noteq> y) \<longleftrightarrow> c211_rempty \<tau> w z))"

definition c211_ratomic :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_ratomic \<tau> w \<longleftrightarrow>
    (\<forall>x. Elem x (raw_D \<tau> w) \<longrightarrow> c211_rempty \<tau> w x \<or>
      (\<exists>y. Elem y (raw_D \<tau> w) \<and> c211_ratom \<tau> w y \<and> c211_rleq \<tau> w y x))"

definition c211_rcomplete :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_rcomplete \<tau> w \<longleftrightarrow>
    (\<forall>S. S \<subseteq> explode (raw_D \<tau> w) \<longrightarrow>
      (\<exists>m. Elem m (raw_D \<tau> w) \<and>
        (\<forall>z. Elem z (raw_D \<tau> w) \<longrightarrow>
          ((\<forall>y\<in>S. c211_rleq \<tau> w z y) \<longleftrightarrow> c211_rleq \<tau> w z m))))"

subsection \<open>Concrete instances of the generic notions\<close>

abbreviation c211_cleq :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_cleq \<equiv> c211_pleq pa_Ar Fst Snd paper_D"
abbreviation c211_cempty :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_cempty \<equiv> c211_pempty pa_Ar Fst Snd paper_D"
abbreviation c211_catomic :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_catomic \<equiv> c211_patomic pa_Ar Fst Snd paper_D"
abbreviation c211_ccomplete :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "c211_ccomplete \<equiv> c211_pcomplete pa_Ar Fst Snd paper_D"

ML \<open>
  val th = @{thm c211_patom_not_pempty}
  val _ = if null (Thm_Deps.all_oracles [th]) andalso null (Thm.hyps_of th)
    andalso null (Thm.tpairs_of th) then () else error "c211_patom_not_pempty"
  val _ = writeln "C211-ORDER-DEFS: definitions; 1 clean auxiliary theorem"
\<close>

end
