theory Bacon_Syntax
  imports Bacon_Types
begin

section \<open>Object-language syntax\<close>

text \<open>
  Terms use de Bruijn indices. Thus \<open>Var 0\<close> names the nearest enclosing
  binder, \<open>Var 1\<close> the next one out, and so on. This makes alpha-equivalent
  expressions definitionally identical in the metalanguage.

  The principal constructor readings are:

  \<^item> \<open>App F A\<close>: \<open>F A\<close>;
  \<^item> \<open>Lam \<sigma> M\<close>: \<open>\<lambda>x\<^sub>\<sigma>. M\<close>;
  \<^item> \<open>Eq \<sigma> M N\<close>: \<open>M =\<^sub>\<sigma> N\<close>;
  \<^item> \<open>Neg A\<close>, \<open>Conj A B\<close>, \<open>Disj A B\<close>, and \<open>Imp A B\<close>:
    \<open>\<not>A\<close>, \<open>A \<and> B\<close>, \<open>A \<or> B\<close>, and \<open>A \<longrightarrow> B\<close>;
  \<^item> \<open>Forall \<sigma> A\<close> and \<open>Exists \<sigma> A\<close>:
    \<open>\<forall>x\<^sub>\<sigma>. A\<close> and \<open>\<exists>x\<^sub>\<sigma>. A\<close>.

  Binder bodies are represented in the context obtained by adding the bound
  variable at slot zero.  A constant is identified by both its string and its
  displayed object type; fixed signatures are imposed only in later layers.

  The paper and book allow changes of primitive logical basis.  This
  development takes implication and the displayed Boolean connectives as
  primitive syntax and chooses \<open>\<forall>p. p \<longrightarrow> p\<close> as its truth representative.
  These formulas are truth-equivalent to Bacon and Dorr's printed choices, but
  truth-equivalence alone is not object-language identity in H.  Later claims
  therefore use the definitions below literally unless a stronger system
  supplies an identity bridge.
\<close>

datatype oterm =
    Var nat
  | Const string otype
  | App oterm oterm
  | Lam otype oterm
  | Eq otype oterm oterm
  | Neg oterm
  | Conj oterm oterm
  | Disj oterm oterm
  | Imp oterm oterm
  | Forall otype oterm
  | Exists otype oterm

abbreviation ObjIff :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infixr "\<longleftrightarrow>\<^sub>o" 25) where
  "A \<longleftrightarrow>\<^sub>o B \<equiv> Conj (Imp A B) (Imp B A)"

definition ObjTrue :: oterm where
  "ObjTrue = Forall Prop (Imp (Var 0) (Var 0))"

definition ObjFalse :: oterm where
  "ObjFalse = Neg ObjTrue"

abbreviation ObjExists :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "ObjExists \<equiv> Exists"

end
