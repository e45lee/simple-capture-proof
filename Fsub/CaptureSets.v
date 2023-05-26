(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metalib.Metatheory.
Require Import Coq.Program.Tactics.
Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import Metalib.MetatheoryAtom.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Init.Datatypes.

(** Helpers, defining a set of natural numbers. 
Module Type NATSET.
  Declare Module OT : UsualOrderedType with Definition t := nat.
  Parameter eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
End NATSET.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module NatSetImpl : NATSET.
  (* begin hide *)
  Module OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts OT.
  Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} :=
    Facts.eq_dec.
  (* end hide *)
End NatSetImpl.

(** Defining a set of Natural Numbers. *)
Module NatSet : Metalib.FiniteSets.S with Module E := NatSetImpl.OT :=
  FiniteSets.Make NatSetImpl.OT.

(** The type [nats] is the type of finite sets of [nat]s. *)
Notation nats := NatSet.F.t.
Notation "{}N" :=
  NatSet.F.empty : metatheory_scope.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module NatSetDecide := FSetDecide.Decide NatSet.F.
Module NatSetNotin  := FSetNotin.Notin   NatSet.F.
Module NatSetFacts  := FSetFacts.Facts NatSet.F.
Module NatSetProperties := FSetProperties.Properties NatSet.F. *)

(** * Finite sets of atoms *)

(** We use our implementation of atoms to obtain an implementation of
    finite sets of atoms.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library.  In order to avoid polluting Coq's namespace, we do
    not use [Module Export]. *)

Module NatSetImpl : FSetExtra.WSfun Nat_as_OT :=
  FSetExtra.Make Nat_as_OT.

Notation nats :=
  NatSetImpl.t.

Notation "{}N" := NatSetImpl.empty.

(** The [AtomSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)


Module Export NatSetDecide := Coq.FSets.FSetDecide.WDecide_fun Nat_as_OT NatSetImpl.

(** The [AtomSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    atoms, as well as a variety of lemmas about non-membership. *)

Module Export NatSetNotin := FSetWeakNotin.Notin_fun Nat_as_OT NatSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module NatSetFacts := FSetFacts.WFacts_fun Nat NatSetImpl.
Module NatSetProperties := FSetProperties.WProperties_fun Nat NatSetImpl.

Export NatSetFacts.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of nats *)

(** The tactic [fnsetdec] is a general purpose decision procedure
    for solving facts about finite sets of atoms. *)

Ltac fnsetdec := NatSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac nnotin_simpl := NatSetNotin.destruct_notin.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac nnotin_solve := NatSetNotin.solve_notin.

Definition disjoint (xs : atoms) (ys: atoms) : Prop :=
  AtomSetImpl.Empty (AtomSetImpl.inter xs ys).

Notation "a `disjoint` b" := (disjoint a b) (at level 1)  : metatheory_scope.

Declare Scope cset_scope.

(** A captureset -- a pair of free variables and bound variables. *)
Inductive captureset : Type :=
  | cset_universal : captureset
  | cset_set : atoms -> nats -> captureset.

Definition empty_cset := cset_set {} {}N.
Definition universal_cset := cset_universal.

(** The empty set may be written similarly to informal practice. *)
Notation "{}C" :=
  empty_cset : metatheory_scope.
Notation "{*}C" :=
  universal_cset : metatheory_scope.

(** Accessors *)
Definition cset_fvars (c : captureset) : atoms :=
  match c with
  | cset_universal => {}
  | cset_set A N => A
  end.

Definition cset_bvars (c : captureset) : nats :=
  match c with
  | cset_universal => {}N
  | cset_set A N => N
  end.

(** Lifts predicates on sets of captures to non-universal capture sets **)
Definition cset_vars (pf : atoms -> Prop)  (pb : nats -> Prop) (c : captureset) : Prop :=
  match c with
  | cset_set A N => pf A /\ pb N
  | cset_universal => False
  end.

(* Could be implemented in terms of cset_vars but that leaves us with a dangeling /\ True *)
Definition cset_all_fvars (p : atoms -> Prop) (c : captureset) : Prop :=
  match c with
  | cset_set A N => p A
  | cset_universal => False
  end.


Definition cset_all_bvars (p : nats -> Prop) (c : captureset) : Prop :=
  match c with
  | cset_set A N => p N
  | cset_universal => False
  end.

(** Singletons *)
Definition cset_fvar (a : atom) :=
  (cset_set (AtomSetImpl.singleton a) {}N).
Definition cset_bvar (k : nat) :=
  (cset_set (AtomSetImpl.empty) (NatSetImpl.singleton k)).

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)
Definition cset_references_bvar (k : nat) (c : captureset) :=
  cset_all_bvars (NatSetImpl.In k) c.

Definition cset_references_fvar (a : atom) (c : captureset) :=
  cset_all_fvars (AtomSetImpl.In a) c.

Definition cset_references_bvar_dec (k : nat) (c : captureset) :=
  match c with
  | cset_universal => false
  | cset_set A N => NatSetImpl.mem k N
  end.

Definition cset_references_fvar_dec (a : atom) (c : captureset) :=
  match c with
  | cset_universal => false
  | cset_set A N => AtomSetImpl.mem a A
  end.

Lemma cset_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = true <-> cset_references_bvar k c.
Proof.
  destruct c ; simpl ; intuition.
Qed.

Lemma cset_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = true <-> cset_references_fvar k c.
Proof.
  destruct c ; simpl ; intuition.
Qed.

Lemma cset_not_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = false <-> ~ cset_references_bvar k c.
Proof.
  destruct c ; simpl.
  - intuition.
  - rewrite <- NatSetFacts.not_mem_iff. intuition.
Qed.

Lemma cset_not_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = false <-> ~ cset_references_fvar k c.
Proof.
  destruct c ; simpl.
  - intuition.
  - rewrite <- AtomSetFacts.not_mem_iff. intuition.
Qed.


(** More predicates *)
Definition empty_cset_bvars (c : captureset) : Prop :=
  cset_all_bvars NatSetImpl.Empty c.
Definition empty_cset_fvars (c : captureset) : Prop :=
  cset_all_fvars AtomSetImpl.Empty c.

Definition cset_disjoint_fvars (c1 c2 :captureset) : Prop :=
  match c1 , c2 with
  | (cset_set A1 N1), (cset_set A2 N2) => AtomSetImpl.Empty (AtomSetImpl.inter A1 A2)
  | _ , _ => True
  end.

(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : captureset) : captureset :=
  match c1 , c2 with
  | _ , cset_universal => cset_universal
  | cset_universal , _ => cset_universal
  | cset_set A1 N1 , cset_set A2 N2 => cset_set (AtomSetImpl.union A1 A2) (NatSetImpl.union N1 N2)
  end.

(** Empty capture sets / universal capture sets *)
Definition cset_empty (c : captureset) : Prop :=
  match c with
  | cset_universal => False
  | cset_set A N => empty_cset_bvars c /\ empty_cset_fvars c
  end.

Definition cset_remove_bvar (k : nat) (c : captureset) : captureset :=
  match c with
  | cset_universal => cset_universal
  | cset_set AC NC => cset_set AC (NatSetImpl.remove k NC)
  end.

Definition cset_remove_fvar (a : atom) (c : captureset) : captureset :=
  match c with
  | cset_universal => cset_universal
  | cset_set AC NC => cset_set (AtomSetImpl.remove a AC) NC
  end.


(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_cset (k : nat) (c : captureset) (d : captureset) : captureset :=
  if cset_references_bvar_dec k d then
    cset_union c (cset_remove_bvar k d)
  else
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition subst_cset (a : atom) (c : captureset) (d: captureset) : captureset :=
  if cset_references_fvar_dec a d then
    cset_union c (cset_remove_fvar a d)
  else
    d.

(* TODO rename to cset_subset *)
(** Predicates around subsets, and decidability for destruction *)
Inductive cset_subset_prop : captureset -> captureset -> Prop :=
| cset_subset_univ : forall c, cset_subset_prop c cset_universal
| cset_subset_elem : forall ac nc ad nd,
  AtomSetImpl.Subset ac ad -> NatSetImpl.Subset nc nd -> cset_subset_prop (cset_set ac nc) (cset_set ad nd)
.

Definition cset_subset_dec (c d : captureset) :=
  match c , d with
  | _ , cset_universal => true
  | cset_universal , _ => false
  | cset_set AC NC , cset_set AD ND => AtomSetImpl.subset AC AD && NatSetImpl.subset NC ND
  end.

(** A helper, to eliminate terms like <complex computation> && false *)
Local Lemma reduce_false (b : bool) : b && false = false.
Proof.
destr_bool.
Qed.

(** Why isn't this part of the standard library? **)
Local Lemma eliminate_false (b : bool) : (b = false) <-> (b <> true).
Proof.
destr_bool; split; destr_bool.
contradict H; trivial.
Qed.

(** Two relations relating the subset relation to the subset computation. *)
Lemma cset_subset_iff (c1 c2 : captureset) : cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = true.
Proof.
  split.
  (* --> *)
  * intro. inversion H ; unfold cset_subset_dec.
    - subst. destruct c1 ; eauto.
    - subst.
      rewrite NatSetFacts.subset_iff in *. rewrite AtomSetFacts.subset_iff in *.
      rewrite H0. rewrite H1. auto.
  (* <-- *)
  * intro. unfold cset_subset_dec in H.
    destruct c1 eqn:H1 ; destruct c2 eqn:H2.
    - apply cset_subset_univ.
    - discriminate H.
    - apply cset_subset_univ.
    - apply cset_subset_elem ; rewrite andb_true_iff in H ; destruct H ;
      rewrite <- NatSetFacts.subset_iff in * ; rewrite <- AtomSetFacts.subset_iff in * ; auto.
Qed.

Lemma cset_subset_not_iff (c1 c2 : captureset) : ~ cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = false.
Proof with auto*.
  split.
  * intro H. rewrite eliminate_false. contradict H. apply cset_subset_iff...
  * intro H. rewrite eliminate_false in H. contradict H. apply cset_subset_iff...
Qed.

(* TODO move to CaptureSets. *)
Lemma cset_subset_reflexivity (c : captureset) : cset_subset_prop c c.
Proof with auto.
  rewrite cset_subset_iff.
  unfold cset_subset_dec.
  destruct c...
  assert (AtomSetImpl.subset t t = true). { rewrite <- AtomSetFacts.subset_iff. intro. intro. assumption. }
  assert (NatSetImpl.subset t0 t0 = true). { rewrite <- NatSetFacts.subset_iff. fnsetdec. }
  intuition.
Qed.

(* unversals can't be subcaptres of concrete capture sets. *)
Lemma cset_universal_subset : forall tf tb,
  cset_subset_prop cset_universal (cset_set tf tb) ->
  False.
Proof with auto.
  intros tf tb H.
  inversion H...
Qed.


(* Some simple tactics to work with capture sets *)

(* Uses hypothesis about capture set inclusion to rewrite hyps and goal *)
Ltac simpl_in_cset :=
  match goal with
    H: cset_references_bvar_dec ?I ?C = ?B
    |- _ => rewrite H in *
  end.

(* Rewrites hypothesis by unfolding cset definitions and using hypothesis about
   inclusion. *)
Ltac csethyp := try autounfold with cset_scope in *; try simpl_in_cset.

(* Uses facts about the underlying sets to simplify hypothesis and solve the goal *)
Ltac csetdec := repeat (
  try csethyp ;
  (try rewrite <- NatSetFacts.mem_iff in * ; try fnsetdec; try nnotin_solve) ||
  (try rewrite <- AtomSetFacts.mem_iff in * ; try fsetdec; try solve_notin)
).

Hint Constructors cset_subset_prop : core.

Hint Transparent
  cset_references_bvar cset_references_fvar
  cset_remove_bvar cset_remove_fvar open_cset subst_cset
  disjoint
: cset_scope.

Hint Unfold
  cset_union cset_subset_dec
  cset_remove_bvar cset_remove_fvar
  open_cset subst_cset
  cset_references_bvar cset_references_fvar
  cset_all_fvars cset_all_bvars
  disjoint
: cset_scope.
