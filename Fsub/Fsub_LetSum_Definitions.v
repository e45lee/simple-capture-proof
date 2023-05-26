(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##wf">Well-formedness</a>#
      - #<a href="##sub">Subtyping</a>#
      - #<a href="##typing_doc">Typing</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##auto">Automation</a>#
*)

Require Export Metalib.Metatheory.
Require Export Fsub.CaptureSets.
Require Export String.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the MetatheoryAtom library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)

Inductive shp : Type :=
  | shp_top : shp
  | shp_bvar : nat -> shp
  | shp_fvar : atom -> shp
  | shp_arrow : typ -> typ -> shp
  | shp_sall : shp -> typ -> shp
  | shp_call : captureset -> typ -> shp

with typ : Type :=
  | pair : shp -> captureset -> typ
.

Inductive exp : Type :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> captureset -> exp -> exp
  | exp_sabs : shp -> exp -> exp
  | exp_sapp : exp -> shp -> exp
  | exp_cabs : captureset -> exp -> exp
  | exp_capp : exp -> captureset -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion shp_bvar : nat >-> shp.
Coercion shp_fvar : atom >-> shp.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on natural numbers
    (e.g., [K == J]) is defined in the CoqEqDec library, which is
    included by the Metatheory library.  The order of arguments to
    each "open" function is the same.  For example, [(open_tt_rec K U
    T)] can be read as "substitute [U] for index [K] in [T]."

    Note that we assume [U] is locally closed (and similarly for the
    other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_ss_rec (K : nat) (U : shp) (Sh : shp)  {struct Sh} : shp :=
  match Sh with
  | shp_top => shp_top
  | shp_bvar J => if K == J then U else (shp_bvar J)
  | shp_fvar X => shp_fvar X
  | shp_arrow T1 T2 => shp_arrow (open_st_rec K U T1) (open_st_rec K U T2)
  | shp_sall S1 T => shp_sall (open_ss_rec K U S1) (open_st_rec (S K) U T)
  | shp_call C1 T => shp_call C1 (open_st_rec K U T)
  end
with open_st_rec (K : nat) (U : shp) (T : typ)  {struct T} : typ :=
  match T with
  | pair Sh C => pair (open_ss_rec K U Sh) C
  end.

Fixpoint open_se_rec (K : nat) (U : shp) (e : exp) {struct e}: exp :=
  match e with
  | exp_fvar x => exp_fvar x
  | exp_bvar i => exp_bvar i
  | exp_abs T e1 => exp_abs (open_st_rec K U T)  (open_se_rec K U e1)
  | exp_app e1 cap e2 => exp_app (open_se_rec K U e1) cap (open_se_rec K U e2)
  | exp_sabs Sh e1 => exp_sabs (open_ss_rec K U Sh) (open_se_rec (S K) U e1)
  | exp_sapp e1 Sh => exp_sapp (open_se_rec K U e1) (open_ss_rec K U Sh)
  | exp_cabs C e1 => exp_cabs C (open_se_rec K U e1)
  | exp_capp e1 C => exp_capp (open_se_rec K U e1) C
  end.

Definition open_cc_rec (K : nat) (U : captureset) (C : captureset): captureset :=
  match C with
  | cset_universal => cset_universal
  | cset_set As Ns => match (NatSetImpl.mem K Ns) with
                      | false => cset_set As Ns
                      | true => match U with
                                | cset_universal => cset_universal
                                | cset_set UAs UNs => cset_set (AtomSetImpl.union UAs As) (NatSetImpl.union (NatSetImpl.remove K Ns) UNs)
                                end
                      end
  end.

Fixpoint open_cs_rec (K : nat) (U : captureset) (Sh : shp)  {struct Sh}: shp :=
  match Sh with
  | shp_top => shp_top
  | shp_bvar J => shp_bvar J
  | shp_fvar X => shp_fvar X
  | shp_arrow T1 T2 => shp_arrow (open_ct_rec K U T1) (open_ct_rec (S K) U T2)
  | shp_sall S1 T => shp_sall (open_cs_rec K U S1) (open_ct_rec K U T)
  | shp_call C1 T => shp_call (open_cc_rec K U C1) (open_ct_rec (S K) U T)
  end
with open_ct_rec (K : nat) (U : captureset) (T : typ)  {struct T}: typ :=
  match T with
  | pair Sh C => pair (open_cs_rec K U Sh) (open_cc_rec K U C)
  end.

Fixpoint open_ce_rec (K : nat) (U : captureset) (e : exp) {struct e}: exp :=
  match e with
  | exp_fvar x => exp_fvar x
  | exp_bvar i => exp_bvar i
  | exp_abs T e1 => exp_abs (open_ct_rec K U T)  (open_ce_rec (S K) U e1)
  | exp_app e1 cap e2 => exp_app (open_ce_rec K U e1) (open_cc_rec K U cap) (open_ce_rec K U e2)
  | exp_sabs Sh e1 => exp_sabs (open_cs_rec K U Sh) (open_ce_rec K U e1)
  | exp_sapp e1 Sh => exp_sapp (open_ce_rec K U e1) (open_cs_rec K U Sh)
  | exp_cabs C e1 => exp_cabs (open_cc_rec K U C) (open_ce_rec (S K) U e1)
  | exp_capp e1 C => exp_capp (open_ce_rec K U e1) (open_cc_rec K U C)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (C :captureset) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f C e1)
  | exp_app e1 cap e2 => exp_app (open_ee_rec k f C e1) (open_cc_rec k C cap) (open_ee_rec k f C e2)
  | exp_sabs Sh e1 => exp_sabs Sh (open_ee_rec k f C e1)
  | exp_sapp e1 Sh => exp_sapp (open_ee_rec k f C e1) Sh
  | exp_cabs D e1 => exp_cabs D (open_ee_rec (S k) f C e1)
  | exp_capp e1 D => exp_capp (open_ee_rec k f C e1) D
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_ss Sh2 Sh1 := open_ss_rec 0 Sh1 Sh2.
Definition open_st T S := open_st_rec 0 S T.
Definition open_se e S := open_se_rec 0 S e.

Definition open_cc C2 C1 := open_cc_rec 0 C1 C2.
Definition open_cs S C := open_cs_rec 0 C S.
Definition open_ct T C := open_ct_rec 0 C T.
Definition open_ce e C := open_ce_rec 0 C e.

Definition open_ee e1 e2 C := open_ee_rec 0 e2 C e1.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed, we must
    check that [T1] is locally closed and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2) .
>>  Or, we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2) .
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite"
    quantification: we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive capture : captureset -> Prop :=
  | cap_atoms : forall (As : atoms),
      capture (cset_set As {}N)
  | cap_universal :
      capture (cset_universal)
.

Inductive shape : shp -> Prop :=
  | shape_top :
      shape shp_top
  | shape_var : forall X,
      shape (shp_fvar X)
  | shape_arrow : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_ct T2 (cset_fvar X))) ->
      shape (shp_arrow T1 T2)
  | shape_sall : forall L S T,
      shape S ->
      (forall X : atom, X `notin` L -> type (open_st T X)) ->
      shape (shp_sall S T)
  | shape_call : forall L C T,
      capture C ->
      (forall X : atom, X `notin` L -> type (open_ct T (cset_fvar X))) ->
      shape (shp_call C T)

with type : typ -> Prop :=
  | type_pair : forall (Sh :shp) (C : captureset),
      shape Sh ->
      capture C ->
      type (pair Sh C)
.

Print cset_set.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x (cset_fvar x))) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 C e2,
      expr e1 ->
      capture C ->
      expr e2 ->
      expr (exp_app e1 C e2)
  | expr_sabs : forall L Sh e1,
      shape Sh ->
      (forall X : atom, X `notin` L -> expr (open_se e1 X)) ->
      expr (exp_sabs Sh e1)
  | expr_sapp : forall e1 V,
      expr e1 ->
      shape V ->
      expr (exp_sapp e1 V)
  | expr_cabs : forall L C e1,
      capture C ->
      (forall X : atom, X `notin` L -> expr (open_ce e1 (cset_fvar X))) ->
      expr (exp_cabs C e1)
  | expr_capp : forall e1 V,
      expr e1 ->
      capture V ->
      expr (exp_capp e1 V)
.


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The Metatheory and MetatheoryEnv libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  They treat environments as lists of type [list
    (atom * A)].  The notation [(x ~ a)] denotes a list consisting of
    a single binding from [x] to [a].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Type :=
  | bind_sub_shp : shp -> binding
  | bind_sub_cap : captureset -> binding
  | bind_typ : typ -> binding.

(** A binding [(X ~ bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x ~ bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. x ~ bind_typ T
  3. Y ~ bind_sub S ++ x ~ bind_typ T
  4. F ++ x ~ bind_typ T ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's List library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

Inductive wf_cap : env -> captureset -> Prop :=
  | wf_cset_universal : forall E,
      wf_cap E cset_universal
  | wf_cset_set : forall E (A : atoms),
      (forall a, AtomSetImpl.In a A -> ((exists U, binds a (bind_sub_cap U) E) \/ (exists V, binds a (bind_typ V) E))) ->
      wf_cap E (cset_set A {}N) 
.

Inductive wf_shp : env -> shp -> Prop :=
  | wf_shp_top : forall E,
      wf_shp E shp_top
  | wf_shp_fvar : forall E U (x : atom),
      binds x (bind_sub_shp U) E ->
      wf_shp E (shp_fvar x)
  | wf_shp_arrow : forall L E (T1 : typ) (T2 : typ),
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_typ T1 ++ E) (open_ct T2 (cset_fvar X))) ->
      wf_shp E (shp_arrow T1 T2)
  | wf_shp_sall : forall L E S T,
      wf_shp E S ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub_shp S ++ E) (open_st T X)) ->
      wf_shp E (shp_sall S T)
  | wf_shp_call : forall L E C T,
      wf_cap E C ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub_cap C ++ E) (open_ct T (cset_fvar X))) ->
      wf_shp E (shp_call C T)

with wf_typ : env -> typ -> Prop :=
  | wf_pair : forall E S C,
      wf_shp E S ->
      wf_cap E C ->
      wf_typ E (pair S C) 
.

(** An environment [E] is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [uniq]
    relation defined in the MetatheoryEnv library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub_shp : forall (E : env) (X : atom) (Sh : shp),
      wf_env E ->
      wf_shp E Sh ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub_shp Sh ++ E)
  | wf_env_sub_cap : forall (E : env) (X : atom) (C : captureset),
      wf_env E ->
      wf_cap E C ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub_cap C ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E)
.


(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

Inductive sub_cap : env -> captureset -> captureset -> Prop :=
  | sub_cap_universal : forall E C,
      wf_env E ->
      wf_cap E C ->
      sub_cap E C cset_universal
  | sub_cap_in : forall E (x : atom) ys,
      wf_env E ->
      wf_cap E (cset_set ys {}N) ->
      x `in` ys ->
      sub_cap E (cset_fvar x) (cset_set ys {}N)
  | sub_cap_cvar : forall E (x : atom) ys C,
      sub_cap E C (cset_set ys {}N) ->
      binds x (bind_sub_cap C) E ->
      sub_cap E (cset_fvar x) (cset_set ys {}N)
  | sub_cap_var : forall E (x : atom) ys C Sh,
      sub_cap E C (cset_set ys {}N) ->
      binds x (bind_typ (pair Sh C)) E ->
      sub_cap E (cset_fvar x) (cset_set ys {}N)
  | sub_cap_bound : forall E xs ys,
      wf_env E ->
      wf_cap E (cset_set xs {}N) ->
      wf_cap E (cset_set ys {}N) ->
      AtomSetImpl.For_all (fun x => (sub_cap E (cset_fvar x) (cset_set ys {}N))) xs ->
      sub_cap E (cset_set xs {}N) (cset_set ys {}N)
.

Inductive sub_shp : env -> shp -> shp -> Prop :=
  | sub_shp_top : forall E S,
      wf_env E ->
      wf_shp E S ->
      sub_shp E S shp_top
  | sub_shp_refl_tvar : forall E X,
      wf_env E ->
      wf_shp E (shp_fvar X) ->
      sub_shp E (shp_fvar X) (shp_fvar X)
  | sub_shp_trans_tvar : forall U E Sh X,
      binds X (bind_sub_shp U) E ->
      sub_shp E U Sh ->
      sub_shp E (shp_fvar X) Sh
  | sub_shp_arrow : forall L E S1 S2 T1 T2,
      sub_typ E T1 S1 ->
      (forall X : atom, X `notin` L ->
        sub_typ (X ~ bind_typ T1 ++ E) (open_ct S2 (cset_fvar X)) (open_ct T2 (cset_fvar X))) ->
      sub_shp E (shp_arrow S1 S2) (shp_arrow T1 T2)
  | sub_shp_sall : forall L E S1 S2 T1 T2,
      sub_shp E T1 S1 ->
      (forall X : atom, X `notin` L -> 
        sub_typ (X ~ bind_sub_shp T1 ++ E) (open_st S2 X) (open_st T2 X)) ->
      sub_shp E (shp_sall S1 S2) (shp_sall T1 T2)
  | sub_shp_call : forall L E S1 S2 T1 T2,
      sub_cap E T1 S1 -> 
      (forall X : atom, X `notin` L ->
        sub_typ (X ~ bind_sub_cap T1 ++ E) (open_ct S2 (cset_fvar X)) (open_ct T2 (cset_fvar X))) ->
      sub_shp E (shp_call S1 S2) (shp_call T1 T2)

with sub_typ : env -> typ -> typ -> Prop :=
  | sub_typ_pair : forall E Sh1 Sh2 C1 C2,
      sub_cap E C1 C2 ->
      sub_shp E Sh1 Sh2 ->
      sub_typ E (pair Sh1 C1) (pair Sh2 C2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of typing is straightforward.  It uses the [binds]
    relation from the MetatheoryEnv library (in the [typing_var] case)
    and cofinite quantification in the cases involving binders (e.g.,
    [typing_abs] and [typing_tabs]). *)

Fixpoint fv_exp_for_cap (e : exp) {struct e} : atoms :=
  match e with
  | exp_fvar x => (AtomSetImpl.singleton x)
  | exp_bvar n => (AtomSetImpl.empty)
  | exp_abs T e1 =>(fv_exp_for_cap e1)
  | exp_app e1 C e2 => (AtomSetImpl.union (fv_exp_for_cap e1)(fv_exp_for_cap e2))
  | exp_sabs Sh e => (fv_exp_for_cap e)
  | exp_sapp e1 Sh =>(fv_exp_for_cap e1)
  | exp_cabs C e1 => (fv_exp_for_cap e1)
  | exp_capp e1 C => (fv_exp_for_cap e1)
  end
.

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E x S C,
      wf_env E ->
      binds x (bind_typ (pair S C)) E ->
      typing E (exp_fvar x) (pair S (cset_fvar x))
  | typing_abs : forall L E V e1 T1,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x (cset_fvar x)) (open_ct T1 (cset_fvar x))) ->
      typing E (exp_abs V e1) (pair 
        (shp_arrow V T1) (cset_set (fv_exp_for_cap e1) {}N))
  | typing_app : forall T1 E e1 e2 T2 C D,
      typing E e1 (pair (shp_arrow (pair T1 C) T2) D) ->
      typing E e2 (pair T1 C) ->
      typing E (exp_app e1 C e2) (open_ct T2 C)
  | typing_sabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub_shp V ++ E) (open_se e1 X) (open_st T1 X)) ->
      typing E (exp_sabs V e1) (pair (shp_sall V T1) 
      (cset_set (fv_exp_for_cap e1) {}N))
  | typing_sapp : forall Sh1 E e1 Sh T2 C,
      typing E e1 (pair (shp_sall Sh1 T2) C) ->
      sub_shp E Sh Sh1 ->
      typing E (exp_sapp e1 Sh) (open_st T2 Sh)
  | typing_cabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub_cap V ++ E) (open_ce e1 (cset_fvar X)) (open_ct T1 (cset_fvar X))) ->
      typing E (exp_cabs V e1) (pair (shp_call V T1) (cset_set (fv_exp_for_cap e1) {}N))
  | typing_capp : forall C1 E e1 C T2 D,
      typing E e1 (pair (shp_call C1 T2) D) ->
      sub_cap E C C1 ->
      typing E (exp_capp e1 C) (open_ct T2 C)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub_typ E S T ->
      typing E e T
.

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall Sh e1,
      expr (exp_sabs Sh e1) ->
      value (exp_sabs Sh e1)
  | value_cabs : forall C e1,
      expr (exp_cabs C e1) ->
      value (exp_cabs C e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall C e1 e1' e2,
      expr e2 ->
      capture C ->
      red e1 e1' ->
      red (exp_app e1 C e2) (exp_app e1' C e2)
  | red_app_2 : forall C e1 e2 e2',
      value e1 ->
      capture C ->
      red e2 e2' ->
      red (exp_app e1 C e2) (exp_app e1 C e2')
  | red_sapp : forall e1 e1' Sh,
      shape Sh ->
      red e1 e1' ->
      red (exp_sapp e1 Sh) (exp_sapp e1' Sh)
  | red_capp : forall e1 e1' C,
      capture C ->
      red e1 e1' ->
      red (exp_capp e1 C) (exp_capp e1' C)
  | red_abs : forall C T e1 v2,
      expr (exp_abs T e1) ->
      capture C ->
      value v2 ->
      red (exp_app (exp_abs T e1) C v2) (open_ee e1 v2 C)
  | red_sabs : forall Sh1 e1 Sh2,
      expr (exp_sabs Sh1 e1) ->
      shape Sh2 ->
      red (exp_sapp (exp_sabs Sh1 e1) Sh2) (open_se e1 Sh2)
  | red_cabs : forall C1 e1 C2,
      expr (exp_cabs C1 e1) ->
      capture C2 ->
      red (exp_capp (exp_cabs C1 e1) C2) (open_ce e1 C2)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

#[export] Hint Constructors sub_typ sub_cap shape capture type expr wf_typ wf_shp wf_cap wf_env value red : core. 
#[export] Hint Resolve sub_shp_top sub_shp_refl_tvar sub_shp_arrow : core.
#[export] Hint Resolve typing_var typing_app typing_sapp typing_capp typing_sub : core.
