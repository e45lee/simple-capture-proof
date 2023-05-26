(** Infrastructure lemmas and tactic definitions for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##gather_atoms">The "gather_atoms" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##auto">Automation</a>#
      - #<a href="##body">Properties of body_e</a># *)

Require Export Fsub.Fsub_LetSum_Definitions.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

(* Note, the only purpose of this function is the avoid naming conflicts, 
   as a result, this stupid definition below works *)

Definition fv_cc (C : captureset): atoms :=
  match C with
  | cset_universal => {}
  | cset_set As Ns => As 
  end
.


Definition fv_ec (C : captureset): atoms :=
  match C with
  | cset_universal => {}
  | cset_set As Ns => As
  end
.

Fixpoint fv_ss (Sh : shp) {struct Sh} : atoms :=
  match Sh with
  | shp_top => {}
  | shp_bvar J => {}
  | shp_fvar X => {{ X }}
  | shp_arrow T1 T2 => (fv_st T1) `union` (fv_st T2)
  | shp_sall Sh1 T => (fv_ss Sh1) `union` (fv_st T)
  | shp_call C T => (fv_st T)
  end
with fv_st (T : typ) {struct T} : atoms :=
  match T with
  | pair Sh1 C => (fv_ss Sh1) 
  end
.

Fixpoint fv_cs (Sh : shp) {struct Sh} : atoms :=
  match Sh with
  | shp_top => {}
  | shp_bvar J => {}
  | shp_fvar X => {}
  | shp_arrow T1 T2 => (fv_ct T1) `union` (fv_ct T2)
  | shp_sall Sh1 T => (fv_cs Sh1) `union` (fv_ct T)
  | shp_call C T => (fv_cc C) `union` (fv_ct T)
  end
with fv_ct (T : typ) {struct T} : atoms :=
  match T with
  | pair Sh1 C => (fv_cs Sh1) `union` (fv_cc C)
  end
.

Fixpoint fv_se (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs V e1  => (fv_st V) `union` (fv_se e1)
  | exp_app e1 C e2 => (fv_se e1) `union` (fv_se e2)
  | exp_sabs V e1 => (fv_ss V) `union` (fv_se e1)
  | exp_sapp e1 V => (fv_ss V) `union` (fv_se e1)
  | exp_cabs C e1 => (fv_se e1)
  | exp_capp e1 C => (fv_se e1)
  end
.

Fixpoint fv_ce (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs V e1  => (fv_ct V) `union` (fv_ce e1)
  | exp_app e1 C e2 => (fv_ce e1) `union` (fv_cc C) `union` (fv_ce e2)
  | exp_sabs V e1 => (fv_cs V) `union` (fv_ce e1)
  | exp_sapp e1 V => (fv_cs V) `union` (fv_ce e1)
  | exp_cabs C e1 => (fv_cc C) `union` (fv_ce e1)
  | exp_capp e1 C => (fv_cc C) `union` (fv_ce e1)
  end
.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {{ x }}
  | exp_abs V e1 => (fv_ee e1)
  | exp_app e1 C e2 => (fv_ee e1) `union` (fv_ec C) `union` (fv_ee e2)
  | exp_sabs V e1 => (fv_ee e1)
  | exp_sapp e1 V => (fv_ee e1)
  | exp_cabs V e1 => (fv_ee e1)
  | exp_capp e1 V => (fv_ee e1)
  end.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Fixpoint subst_ss (Z : atom) (U : shp) (T : shp) {struct T} : shp :=
  match T with
  | shp_top => shp_top
  | shp_bvar J => shp_bvar J
  | shp_fvar X => if X == Z then U else T
  | shp_arrow T1 T2 => shp_arrow (subst_st Z U T1) (subst_st Z U T2)
  | shp_sall Sh T2 => shp_sall (subst_ss Z U Sh) (subst_st Z U T2)
  | shp_call C T2 => shp_call C (subst_st Z U T2)
  end
with subst_st (Z : atom) (U : shp) (T : typ) {struct T}: typ :=
  match T with
  | pair Sh C => pair (subst_ss Z U Sh) C
  end
.

Fixpoint subst_se (Z : atom) (U : shp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (subst_st Z U V)  (subst_se Z U e1)
  | exp_app e1 C e2 => exp_app (subst_se Z U e1) C (subst_se Z U e2)
  | exp_sabs V e1 => exp_sabs (subst_ss Z U V)  (subst_se Z U e1)
  | exp_sapp e1 V => exp_sapp (subst_se Z U e1) (subst_ss Z U V)
  | exp_cabs V e1 => exp_cabs V (subst_se Z U e1)
  | exp_capp e1 V => exp_capp (subst_se Z U e1) V
  end.

Fixpoint subst_cc (Z : atom) (U : captureset) (C : captureset) {struct C} : captureset :=
  match C with
  | cset_universal => cset_universal
  | cset_set As Ns => match (AtomSetImpl.mem Z As) with
                      | false => cset_set As Ns
                      | true => match U with
                                | cset_universal => cset_universal
                                | cset_set UAs UNs => cset_set (AtomSetImpl.union (AtomSetImpl.remove Z As) UAs) (NatSetImpl.union Ns UNs)
                                end
                      end
  end
.
Arguments  subst_cc : simpl never.


Fixpoint subst_cs (Z : atom) (U : captureset) (Sh : shp) {struct Sh} : shp :=
  match Sh with
  | shp_top => shp_top
  | shp_bvar J => shp_bvar J
  | shp_fvar X => shp_fvar X
  | shp_arrow T1 T2 => shp_arrow (subst_ct Z U T1) (subst_ct Z U T2)
  | shp_sall Sh T2 => shp_sall (subst_cs Z U Sh) (subst_ct Z U T2)
  | shp_call C T2 => shp_call (subst_cc Z U C) (subst_ct Z U T2)
  end
with subst_ct (Z : atom) (U : captureset) (T : typ) {struct T} : typ :=
 match T with
 | pair Sh C => pair (subst_cs Z U Sh) (subst_cc Z U C)
 end. 

Fixpoint subst_ce (Z : atom) (U : captureset) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs (subst_ct Z U V) (subst_ce Z U e1)
  | exp_app e1 C e2 => exp_app (subst_ce Z U e1) (subst_cc Z U C) (subst_ce Z U e2)
  | exp_sabs V e1 => exp_sabs (subst_cs Z U V) (subst_ce Z U e1)
  | exp_sapp e1 V => exp_sapp (subst_ce Z U e1) (subst_cs Z U V)
  | exp_cabs C e1 => exp_cabs (subst_cc Z U C) (subst_ce Z U e1)
  | exp_capp e1 C => exp_capp (subst_ce Z U e1) (subst_cc Z U C)
  end
.

Fixpoint subst_ee (z : atom) (U : captureset) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs V e1 => exp_abs (subst_ct z U V) (subst_ee z U u e1)
  | exp_app e1 C e2 => exp_app (subst_ee z U u e1) (subst_cc z U C) (subst_ee z U u e2)
  | exp_sabs V e1 => exp_sabs (subst_cs z U V) (subst_ee z U u e1)
  | exp_sapp e1 V => exp_sapp (subst_ee z U u e1) (subst_cs z U V)
  | exp_cabs V e1 => exp_cabs (subst_cc z U V) (subst_ee z U u e1)
  | exp_capp e1 V => exp_capp (subst_ee z U u e1) (subst_cc z U V)
  end.

Definition subst_sb (Z : atom) (P : shp) (b : binding) : binding :=
  match b with
  | bind_sub_shp Sh => bind_sub_shp (subst_ss Z P Sh)
  | bind_sub_cap C => bind_sub_cap C
  | bind_typ T => bind_typ (subst_st Z P T)
  end.

Definition subst_cb (Z : atom) (P : captureset) (b : binding) : binding :=
  match b with
  | bind_sub_shp Sh => bind_sub_shp (subst_cs Z P Sh)
  | bind_sub_cap C => bind_sub_cap (subst_cc Z P C)
  | bind_typ T => bind_typ (subst_ct Z P T)
  end
.

(* ********************************************************************** *)
(** * #<a name="gather_atoms"></a># The "[gather_atoms]" tactic *)

(** The Metatheory and MetatheoryAtom libraries define a number of
    tactics for working with cofinite quantification and for picking
    fresh atoms.  To specialize those tactics to this language, we
    only need to redefine the [gather_atoms] tactic, which returns the
    set of all atoms in the current context.

    The definition of [gather_atoms] follows a pattern based on
    repeated calls to [gather_atoms_with].  The one argument to this
    tactic is a function that takes an object of some particular type
    and returns a set of atoms that appear in that argument.  It is
    not necessary to understand exactly how [gather_atoms_with] works.
    If we add a new inductive datatype, say for kinds, to our
    language, then we would need to modify [gather_atoms].  On the
    other hand, if we merely add a new type, say products, then there
    is no need to modify [gather_atoms]; the required changes would be
    made in [fv_tt]. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_se x) in
  let D := gather_atoms_with (fun x : exp => fv_ce x) in
  let E := gather_atoms_with (fun x : exp => fv_ee x) in
  let F := gather_atoms_with (fun x : typ => fv_st x) in
  let G := gather_atoms_with (fun x : typ => fv_ct x) in
  let H := gather_atoms_with (fun x : env => dom x) in
  let I := gather_atoms_with (fun x : captureset => fv_cc x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G `union` H `union` I).


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(* A few lemmas to make my life easier.  
   TODO: (Edward) Adopt MetaLib to reintroduce equality on sets *)

Axiom NatSetEqual : forall s1 s2,
  s1 = s2 <-> NatSetImpl.Equal s1 s2.

Axiom AtomSetEqual : forall s1 s2,
  s1 = s2 <-> AtomSetImpl.Equal s1 s2.

Definition sumbool_to_or {P : Prop} {Q : Prop} (H : (sumbool P Q)) :=
  match H with
    | left p0 => or_introl p0
    | right q0 => or_intror q0
  end.

Lemma union_empty_atoms: forall s,
  s = (AtomSetImpl.union s {}).
Proof.
  intro s.
  apply AtomSetEqual.
  intro a. split;intro aIn.
  * apply AtomSetImpl.union_2.
    apply aIn.
  * apply AtomSetImpl.union_1 in aIn.
    destruct aIn.
    ** apply H.
    ** destruct (AtomSetImpl.empty_1 H).
Qed.

Lemma union_empty_nats: forall s,
  s = (NatSetImpl.union s {}N).
Proof.
  intro s.
  apply NatSetEqual.
  intro a. split;intro aIn.
  * apply NatSetImpl.union_2.
    apply aIn.
  * apply NatSetImpl.union_1 in aIn.
    destruct aIn.
    ** apply H.
    ** destruct (NatSetImpl.empty_1 H).
Qed.

Lemma mem_union_or_atoms: forall s T1 T2,
  AtomSetImpl.mem s (union T1 T2) = 
  (AtomSetImpl.mem s T1) || (AtomSetImpl.mem s T2).
Proof with auto.
  intros s T1 T2.
  destruct (AtomSetImpl.mem s T1) eqn:sInT1; destruct (AtomSetImpl.mem s T2) eqn:sInT2;simpl.
  * apply AtomSetImpl.mem_1. apply AtomSetImpl.union_2. apply AtomSetFacts.mem_iff in sInT1...
  * apply AtomSetImpl.mem_1. apply AtomSetImpl.union_2. apply AtomSetFacts.mem_iff in sInT1...
  * apply AtomSetImpl.mem_1. apply AtomSetImpl.union_3. apply AtomSetFacts.mem_iff in sInT2...
  * apply AtomSetFacts.not_mem_iff. intro H. apply AtomSetFacts.union_iff in H. destruct H.
    ** apply AtomSetFacts.not_mem_iff in sInT1. apply (sInT1 H).
    ** apply AtomSetFacts.not_mem_iff in sInT2. apply (sInT2 H).
Qed.

Lemma mem_union_or_nats: forall s T1 T2,
  NatSetImpl.mem s (NatSetImpl.union T1 T2) = 
  (NatSetImpl.mem s T1) || (NatSetImpl.mem s T2).
Proof with auto.
  intros s T1 T2.
  destruct (NatSetImpl.mem s T1) eqn:sInT1; destruct (NatSetImpl.mem s T2) eqn:sInT2;simpl.
  * apply NatSetImpl.mem_1. apply NatSetImpl.union_2. apply NatSetFacts.mem_iff in sInT1...
  * apply NatSetImpl.mem_1. apply NatSetImpl.union_2. apply NatSetFacts.mem_iff in sInT1...
  * apply NatSetImpl.mem_1. apply NatSetImpl.union_3. apply NatSetFacts.mem_iff in sInT2...
  * apply NatSetFacts.not_mem_iff. intro H. apply NatSetFacts.union_iff in H. destruct H.
    ** apply NatSetFacts.not_mem_iff in sInT1. apply (sInT1 H).
    ** apply NatSetFacts.not_mem_iff in sInT2. apply (sInT2 H).
Qed.


Lemma cset_subset : forall t t0 t1 t2 C1 C2,
  C1 = cset_set t t0 ->
  C2 = cset_set t1 t2 ->
  (cset_subset_prop C1 C2) ->
  (AtomSetImpl.Subset t t1) /\ (NatSetImpl.Subset t0 t2).
Proof with auto.
  intros T T0 T1 T2 C1 C2 SC1 SC2 H.
  split; destruct H eqn:shpH...
  * discriminate SC2.
  * inversion SC2. inversion SC1.
    rewrite <- H1.
    rewrite <- H3.
    apply s.
  * discriminate SC2.
  * inversion SC1. inversion SC2.
    rewrite <- H2.
    rewrite <- H4.
    apply s0.
Qed.

Lemma cset_open_idempotent : forall i C c,
  c = open_cc_rec i C c <->
  (~ (cset_references_bvar i c)) \/ (cset_subset_prop C c /\ cset_references_bvar i C).
Proof.
  intros i C c.
  split.
  (* -> *)
  - intros H. destruct (cset_references_bvar_dec i c) eqn:Hic.
    * csethyp. destruct c ; auto.
      simpl in Hic.
      destruct C.
      ** unfold open_cc_rec in H.
         rewrite Hic in H.
         discriminate H.
      ** inversion H. right. split.
        *** eapply cset_subset_elem ; csetdec;intros a int1...
            **** rewrite (NatSetImpl.mem_1 Hic) in H1. inversion H1.
                 apply (AtomSetImpl.union_2 t int1).
            **** rewrite (NatSetImpl.mem_1 Hic) in H1.
                 inversion H1.
                 apply (NatSetImpl.union_3 (NatSetImpl.remove i t0) int1).
        *** inversion H. rewrite Hic in H2. rewrite Hic in H1.
            inversion H2.
            csetdec.
            rewrite H4 in Hic.
            destruct (NatSetImpl.union_1 Hic)...
            **** destruct ((NatSetImpl.remove_1 (reflexivity i)) H0).
            **** apply H0.
    * left. apply cset_not_references_bvar_eq. auto.
  (* <-  *)
  - intros H. destruct H.
    * unfold open_cset.
      destruct (cset_references_bvar_dec i c) eqn:iINc...
      rewrite (cset_references_bvar_eq i c) in iINc.
      contradiction.
      destruct C; destruct c; simpl...
      ** reflexivity.
      ** simpl in H.
         destruct (NatSetImpl.mem i t0) eqn:iInt0...
        *** exfalso.
            apply (H (NatSetImpl.mem_2 iInt0)).
        *** reflexivity.
      ** reflexivity.
      ** simpl in H.
         destruct (NatSetImpl.mem i t2) eqn:iInt2...
        *** exfalso.
            apply (H (NatSetImpl.mem_2 iInt2)).
        *** reflexivity.
    * unfold open_cc_rec...
      destruct C eqn:shpC; destruct c eqn:shpc...
      ** reflexivity.
      ** inversion H.
         simpl in H1.
         contradiction.
      ** reflexivity.
      ** destruct (NatSetImpl.mem i t2) eqn:iInt2...
        *** f_equal...
            **** rewrite AtomSetEqual.
                 intro a. split.
                 ***** apply AtomSetImpl.union_3.
                 ***** inversion H.
                       apply (cset_subset t t0 t1 t2 _ _) in H0.
                       ****** inversion H0.
                              intro aIntt1.
                              apply AtomSetImpl.union_1 in aIntt1.
                              destruct aIntt1.
                              ******* apply (H2 a H4).
                              ******* apply H4.
                       ****** reflexivity.
                       ****** reflexivity.
            **** rewrite NatSetEqual.
                 intro n. split.
                  ****** intro nInT2.
                         destruct (i === n)...
                         ******* apply NatSetImpl.union_3.
                                 rewrite <- e.
                                 inversion H.
                                 simpl in H1.
                                 apply H1.
                         ******* apply NatSetImpl.union_2.
                                 apply NatSetImpl.remove_2.
                                 apply n0.
                                 apply nInT2.
                  ****** intro nInt2t0.
                         destruct (i === n).
                         ******* rewrite e in iInt2.
                                 apply (NatSetImpl.mem_2 iInt2).
                         ******* apply NatSetImpl.union_1 in nInt2t0.
                                 destruct nInt2t0.
                                 ******** apply (NatSetImpl.remove_3 H0).
                                 ******** inversion H.
                                          apply (cset_subset t t0 t1 t2 _ _) in H1.
                                          inversion H1.
                                          ********* apply (H4 n H0).
                                          ********* reflexivity.
                                          ********* reflexivity.
        *** reflexivity.
Qed.

Lemma capture_as_ns_empty : forall C,
  capture C ->
  C <> cset_universal ->
  exists As, C = cset_set As {}N. 
Proof.
  intros C H Neq.
  induction H.
  * apply (ex_intro _ As).
    reflexivity.
  * contradiction.
Qed.

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_ss_rec_shape_aux : forall T j V i U,
  i <> j ->
  open_ss_rec j V T = open_ss_rec i U (open_ss_rec j V T) ->
  T = open_ss_rec i U T
with open_st_rec_type_aux : forall T j V i U,
  i <> j ->
  open_st_rec j V T = open_st_rec i U (open_st_rec j V T) ->
  T = open_st_rec i U T.
Proof with congruence || eauto.
  clear open_ss_rec_shape_aux...
  ----- intros T j V i U Neq H...
    induction T...
    + simpl in *...
      destruct (i === n)...
      destruct (j === n)...
      simpl in *...
      destruct (i === n)...
    + simpl in *...
      f_equal...
      inversion H...
      inversion H...
    + simpl in *...
      f_equal...
      apply IHT...
      inversion H...
    + simpl in *...
      f_equal...
      inversion H...
  ----- clear open_st_rec_type_aux...
   intros T j V i U Neq H...
   induction T...
   simpl in *...
   f_equal...
   inversion H...
Qed.

Lemma open_ss_open_cs_rec_shape_aux: forall T j C i U,
  open_cs_rec j C T = open_ss_rec i U (open_cs_rec j C T) ->
  T = open_ss_rec i U T
with open_st_open_ct_rec_type_aux: forall T j C i U,
  open_ct_rec j C T = open_st_rec i U (open_ct_rec j C T) ->
  T = open_st_rec i U T.
Proof with congruence || eauto.
  ----- clear open_ss_open_cs_rec_shape_aux.
        intros T j C i U H.
        induction T;simpl in *; inversion H; f_equal...
  ----- clear open_st_open_ct_rec_type_aux.
        intros T j C i U H.
        induction T; simpl in *; inversion H; f_equal...
Qed.

Lemma open_cs_open_ss_rec_shape_aux: forall T j V i C,
  open_ss_rec j V T = open_cs_rec i C (open_ss_rec j V T) ->
  T = open_cs_rec i C T
with open_ct_open_st_rec_type_aux: forall T j V i C,
  open_st_rec j V T = open_ct_rec i C (open_st_rec j V T) ->
  T = open_ct_rec i C T.
Proof with congruence || eauto.
  ----- clear open_cs_open_ss_rec_shape_aux.
        intros T j V i C H.
        induction T; simpl in *; inversion H; f_equal...
  ----- clear open_ct_open_st_rec_type_aux.
        intros T j V i C H.
        induction T; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ss_rec_shape : forall T U k,
  shape T ->
  T = open_ss_rec k U T
with open_st_rec_type : forall T U k,
  type T ->
  T = open_st_rec k U T.
Proof with auto.
  ----- clear open_ss_rec_shape.
        intros T U k shpT. revert k.
        induction shpT; intro k; simpl; f_equal; pick fresh X...
        + unfold open_ct in H0.
          apply (open_st_open_ct_rec_type_aux _ 0 (cset_fvar X) _ _)...
        + apply (open_st_rec_type_aux T 0 (shp_fvar X))...
          apply (open_st_rec_type).
          apply H.
          csetdec.
        + unfold open_ct in H0.
          apply (open_st_open_ct_rec_type_aux _ 0 (cset_fvar X) _ _)...
  ----- clear open_st_rec_type.
        intros T U k shpT. revert k.
        induction shpT; intro k; simpl; f_equal;pick fresh X...
Qed.

Lemma open_cc_rec_capture_aux : forall T j V i U,
  i <> j ->
  V <> cset_universal ->
  capture V ->
  (AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc V) (fv_cc U))) ->
  open_cc_rec j V T = open_cc_rec i U (open_cc_rec j V T) ->
  T = open_cc_rec i U T.
Proof with congruence || eauto.
  intros T j V i U Neq VFin Closed Disj H.
  rewrite (cset_open_idempotent i U (open_cc_rec j V T)) in H.
  rewrite cset_open_idempotent.
  destruct (cset_references_bvar_dec i T) eqn:Hic.
  (* i is in c *)
  - destruct (cset_references_bvar_dec j T) eqn:Hjc ; csethyp...
    destruct H.
    * destruct V eqn:shpV; destruct T eqn:shpT; csethyp ; auto.
      left. simpl in *. rewrite Hjc in H. fnsetdec.
    * destruct H. destruct U eqn:HC.
      ** contradiction.
      ** unfold empty_cset_bvars in Closed. unfold cset_all_bvars in *. destruct V eqn:shpV; destruct T eqn:Hc ; eauto.
         right. split...
         inversion H ; csethyp ; simpl in *. constructor. unfold disjoint in *.
         rewrite Hjc in *. discriminate. rewrite Hjc in *. discriminate. rewrite Hjc in *.
         constructor...
         inversion H3.
         subst.
         *** intros a aint.
             destruct (AtomSetImpl.union_1 (H4 a aint)).
             **** destruct (Disj a (AtomSetImpl.inter_3 H1 aint)).
             **** apply H1.
         *** inversion H3.
             rewrite H8 in H5.
             destruct (capture_as_ns_empty (cset_set t1 t2) Closed VFin).
             inversion H6.
             rewrite H11 in *.
             intros a aint0...
             destruct (NatSetImpl.union_1 (H5 a aint0))...
             **** apply (NatSetImpl.remove_3 H9).
             **** destruct ((NatSetImpl.empty_1 H9)).
    * destruct V eqn:shpV; destruct T eqn:shpT; csethyp ; auto.
      right. simpl in *. rewrite Hjc in H. destruct H...
      destruct (H (NatSetImpl.mem_2 Hic)). (* fnsetdec. *)
  (* i is not in c *)
  - left. apply cset_not_references_bvar_eq. apply Hic.
Qed.

Lemma open_cc_rec_capture : forall T U k,
  capture T ->
  T = open_cc_rec k U T.
Proof.
  intros T U k capT.
  rewrite cset_open_idempotent.
  left.
  destruct T.
  * simpl...
    unfold not.
    trivial.
  * destruct (capture_as_ns_empty (cset_set t t0) capT).
    ** discriminate.
    ** inversion H.
       simpl.
       apply NatSetImpl.empty_1.
Qed.

Lemma open_cs_rec_shape_aux : forall T j V i U,
  i <> j ->
  V <> cset_universal ->
  capture V ->
  (AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc V) (fv_cc U))) ->
  open_cs_rec j V T = open_cs_rec i U (open_cs_rec j V T) ->
  T = open_cs_rec i U T
with open_ct_rec_type_aux : forall T j V i U,
  i <> j ->
  V <> cset_universal ->
  capture V ->
  (AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc V) (fv_cc U))) ->
  open_ct_rec j V T = open_ct_rec i U (open_ct_rec j V T) ->
  T = open_ct_rec i U T.
Proof with congruence || eauto.
  clear open_cs_rec_shape_aux.
  ----- intros T j V i U Neq Vfin capV Disj H.
        induction T;simpl in *...
        + f_equal.
          inversion H...
          inversion H...
        + f_equal.
          inversion H...
          inversion H...
        + f_equal.
          inversion H...
          apply (open_cc_rec_capture_aux c j V i U)...
          inversion H...
  ----- clear open_ct_rec_type_aux.
        intros T j V i U Neq Vfin capV Disj H.
        induction T;simpl in *...
        inversion H.
        f_equal...
        apply (open_cc_rec_capture_aux c j V i U)...
Qed.

Lemma open_cs_rec_shape : forall T U k,
  shape T ->
  T = open_cs_rec k U T
with open_ct_rec_type : forall T U k,
  type T ->
  T = open_ct_rec k U T.
Proof with auto.
  ----- clear open_cs_rec_shape.
        intros T U K shpT.
        induction shpT;simpl in *;f_equal...
        * pick fresh X.
          eapply open_ct_rec_type_aux with (V := cset_fvar X) (j := 0);
            eauto; try solve [discriminate]...
          constructor...
          simpl; AtomSetDecide.fsetdec.
      * pick fresh X.
          apply (open_ct_open_st_rec_type_aux _ 0 X _ _).
          apply (open_ct_rec_type (open_st_rec 0 X T) U K).
          unfold open_st in H.
          apply (H X)...
        * apply open_cc_rec_capture...
        * pick fresh X for (union (union L (union (fv_st T) (fv_ct T))) (fv_cc U)).
          apply (open_ct_rec_type_aux _ 0 (cset_fvar X) _ _)...
          discriminate.
          apply cap_atoms...
          simpl.
          intros a aInInter.
          apply AtomSetFacts.inter_iff in aInInter.
          destruct aInInter...
          apply AtomSetImpl.singleton_1 in H1.
          rewrite H1 in *.
          auto.
          apply (open_ct_rec_type (open_ct_rec 0 (cset_fvar X) T) U (S K))...
          unfold open_ct in H0.
          apply (H0 X)...
  ----- clear open_ct_rec_type.
        intros T U K typT.
        induction typT...
        simpl.
        f_equal...
        apply open_cc_rec_capture. apply H0.
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_ss_fresh : forall Z U T,
  Z `notin` fv_ss T ->
  T = subst_ss Z U T
with subst_st_fresh : forall Z U T,
  Z `notin` fv_st T ->
  T = subst_st Z U T.
Proof with auto.
  clear subst_ss_fresh.
  ----- induction T; simpl; intro H; f_equal...
        + destruct (a === Z)...
          destruct (H (AtomSetImpl.singleton_2 e)).
  ----- clear subst_st_fresh.
        induction T; simpl; intro H; f_equal...   
Qed.
 
Lemma subst_cs_fresh : forall Z U T,
  Z `notin` fv_cs T ->
  T = subst_cs Z U T
with subst_ct_fresh : forall Z U T,
  Z `notin` fv_ct T ->
  T = subst_ct Z U T.
Proof with auto.
  clear subst_cs_fresh.
  ----- induction T; simpl; intro H; f_equal...
        destruct c.
        + simpl.
          reflexivity.
        + simpl; unfold subst_cc.
          simpl in H.
          destruct (AtomSetImpl.mem Z t0) eqn:ZmemT0...
          exfalso.
          csetdec.
  ----- clear subst_ct_fresh.
        induction T; simpl; intro H; f_equal...
        destruct c...
        simpl; unfold subst_cc.
        simpl in H.
        destruct (AtomSetImpl.mem Z t) eqn:Zmemt...
        exfalso.
        csetdec.
Qed.

Lemma subst_cc_fresh : forall Z U T,
  Z `notin` fv_cc T ->
  T = subst_cc Z U T.
Proof.
  induction T; unfold subst_cc; intro H. f_equal...
  - reflexivity.
  - destruct (AtomSetImpl.mem Z t) eqn:zInT...
    * destruct (H (AtomSetImpl.mem_2 zInT)).
    * reflexivity.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)
Lemma subst_ss_open_ss_rec : forall T1 T2 X P k,
  shape P ->
  subst_ss X P (open_ss_rec k T2 T1) = 
    open_ss_rec k (subst_ss X P T2) (subst_ss X P T1)
with subst_st_open_st_rec : forall T1 T2 X P k,
  shape P ->
  subst_st X P (open_st_rec k T2 T1) = 
    open_st_rec k (subst_ss X P T2) (subst_st X P T1).
Proof with auto.
  ----- clear subst_ss_open_ss_rec.
        intros T1 T2 X P k WP. revert k.
        induction T1; intros k; simpl; f_equal...
        - destruct (k === n); subst...
        - destruct (a == X); subst... apply open_ss_rec_shape...
  ----- clear subst_st_open_st_rec.
        intros T1 T2 X P k WP. revert k.
        induction T1; intros k; simpl; f_equal...
Qed.

Lemma subst_cc_open_cc_rec : forall T1 T2 X P k,
  capture P ->
  subst_cc X P (open_cc_rec k T2 T1) = 
    open_cc_rec k (subst_cc X P T2) (subst_cc X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; induction T2; induction P; intros k; simpl; unfold subst_cc; f_equal...
  - destruct (NatSetImpl.mem k t0) eqn:kInt0;destruct (AtomSetImpl.mem X t) eqn:xInt; simpl
      ;try rewrite kInt0; try rewrite xInt...
  - destruct (NatSetImpl.mem k t0) eqn:kInt0;destruct (AtomSetImpl.mem X t) eqn:xInt; simpl;
      try rewrite kInt0; try rewrite xInt...
    * apply NatSetImpl.mem_2 in kInt0. apply (NatSetImpl.union_2 t2) in kInt0.
      apply NatSetImpl.mem_1 in kInt0. rewrite kInt0...
    * destruct (capture_as_ns_empty (cset_set t1 t2) WP)... discriminate.
      inversion H.
      rewrite <- union_empty_nats. rewrite kInt0...
  - destruct (NatSetImpl.mem k t0) eqn:kInt0;destruct (AtomSetImpl.mem X t) eqn:xInt; simpl;
    try rewrite xInt; try rewrite kInt0...
    rewrite (AtomSetImpl.mem_1 (AtomSetImpl.union_3 t1 (AtomSetImpl.mem_2 xInt)))...
    destruct (AtomSetImpl.mem X t1) eqn:xInt1; rewrite mem_union_or_atoms; rewrite xInt1; rewrite xInt...
  - destruct (capture_as_ns_empty (cset_set t3 t4) WP)... discriminate.
    inversion H.
    destruct (NatSetImpl.mem k t0) eqn:kInt0;
    destruct (AtomSetImpl.mem X t1) eqn:xInt1;
    destruct (AtomSetImpl.mem X t) eqn: xInt;
    try rewrite xInt1; try rewrite xInt; simpl; try rewrite xInt; try rewrite kInt0;
    try rewrite mem_union_or_atoms; try rewrite mem_union_or_nats; 
    try rewrite xInt1; try rewrite xInt;try rewrite kInt0;simpl;f_equal; repeat try rewrite <- union_empty_nats; try rewrite NatSetFacts.empty_b; try apply AtomSetEqual...
    * intro a. split; intro aInU; destruct (a == X); apply AtomSetFacts.union_iff in aInU;
      destruct aInU;csetdec...
      ** destruct (AtomSetImpl.remove_1 (eq_sym e) H0)...
      ** apply AtomSetImpl.remove_3 in H0. apply AtomSetFacts.union_iff in H0. destruct H0...
      ** rewrite e in *. apply AtomSetFacts.union_iff in H0. destruct H0...
         apply (AtomSetImpl.remove_1 (eq_refl X)) in H0. destruct H0.
      ** apply AtomSetFacts.union_iff in H0. destruct H0... rewrite e in *.
         apply (AtomSetImpl.remove_1 (eq_refl X)) in H0. destruct H0.
      ** apply AtomSetFacts.union_iff in H0. destruct H0... apply AtomSetImpl.remove_3 in H0.
         apply AtomSetFacts.union_iff. left. apply AtomSetImpl.remove_2...
      ** apply AtomSetFacts.union_iff in H0. destruct H0...
         apply AtomSetFacts.union_iff. left.
         apply AtomSetImpl.remove_3 in H0.
         apply AtomSetFacts.remove_iff. split...
    * intro a. split; intro aInU; destruct (a == X); apply AtomSetFacts.union_iff in aInU;
      destruct aInU...
      ** destruct (AtomSetImpl.remove_1 (eq_sym e) H0)...
      ** apply AtomSetImpl.remove_3 in H0. apply AtomSetFacts.union_iff in H0. destruct H0...
      ** rewrite e in *. apply AtomSetFacts.union_iff in H0. destruct H0...
         apply (AtomSetImpl.remove_1 (eq_refl X)) in H0. destruct H0.
      ** apply AtomSetFacts.not_mem_iff in xInt. rewrite e in H0. destruct (xInt H0).
      ** apply AtomSetFacts.union_iff in H0. destruct H0...
         apply AtomSetFacts.union_iff. left.
         apply AtomSetImpl.remove_3 in H0.
         apply AtomSetFacts.remove_iff. split...
    * intro a. split; intro aInU; destruct (a == X); apply AtomSetFacts.union_iff in aInU;
      destruct aInU...
      ** destruct (AtomSetImpl.remove_1 (eq_sym e) H0)...
      ** apply AtomSetImpl.remove_3 in H0. apply AtomSetFacts.union_iff in H0. destruct H0...
      ** csetdec. rewrite e in *. apply AtomSetFacts.not_mem_iff in xInt1...
      ** apply AtomSetFacts.union_iff in H0. destruct H0... apply AtomSetImpl.remove_1 in H0. destruct H0... apply (eq_sym e).
      ** apply AtomSetFacts.union_iff in H0. destruct H0...
         apply AtomSetFacts.union_iff. left.
         apply AtomSetImpl.remove_3 in H0.
         apply AtomSetFacts.remove_iff. split...
Qed.

Lemma subst_cs_open_cs_rec : forall T1 T2 X P k,
  capture P ->
  subst_cs X P (open_cs_rec k T2 T1) = 
    open_cs_rec k (subst_cc X P T2) (subst_cs X P T1)
with subst_ct_open_ct_rec : forall T1 T2 X P k,
  capture P ->
  subst_ct X P (open_ct_rec k T2 T1) = 
    open_ct_rec k (subst_cc X P T2) (subst_ct X P T1).
Proof.
  ----- clear subst_cs_open_cs_rec.
        intros T1 T2 X P k WP. revert k.
        induction T1; intros k; simpl; f_equal...
        - reflexivity.
        - apply subst_ct_open_ct_rec.
          apply WP.
        - apply subst_ct_open_ct_rec.
          apply WP.
        - apply IHT1.
        - apply subst_ct_open_ct_rec.
          apply WP.
        - apply subst_cc_open_cc_rec.
          apply WP.
        - apply subst_ct_open_ct_rec.
          apply WP.
  ----- clear subst_ct_open_ct_rec.
        intros T1 T2 X P k WP. revert k.
        induction T1; intros k; simpl; f_equal...
        apply subst_cs_open_cs_rec; apply WP.
        apply subst_cc_open_cc_rec; apply WP.
Qed.

Lemma subst_ss_open_cs_rec : forall Z P k C T,
  shape P ->
  subst_ss Z P (open_cs_rec k C T) = open_cs_rec k C (subst_ss Z P T)
with subst_st_open_ct_rec : forall Z P k C T,
  shape P ->
  subst_st Z P (open_ct_rec k C T) = open_ct_rec k C (subst_st Z P T).
Proof with auto.
  ----- clear subst_ss_open_cs_rec.
        intros Z P k C T shpP. revert k.
        induction T; intro k; simpl; f_equal...
        destruct (a == Z)...
        apply open_cs_rec_shape...
  ----- clear subst_st_open_ct_rec.
        intros Z P k C T shpP. revert k.
        induction T; intro k; simpl; f_equal...
Qed.

Lemma subst_cs_open_ss_rec : forall Z P k C T,
  subst_cs Z P (open_ss_rec k C T) = open_ss_rec k (subst_cs Z P C) (subst_cs Z P T)
with subst_ct_open_st_rec : forall Z P k C T,
  subst_ct Z P (open_st_rec k C T) = open_st_rec k (subst_cs Z P C) (subst_ct Z P T).
Proof with auto.
  ----- clear subst_cs_open_ss_rec.
        intros Z P k C T. revert k.
        induction T; intro k; simpl; f_equal...
        destruct (k == n)...
  ----- clear subst_ct_open_st_rec.
        intros Z P k C T. revert k.
        induction T; intro k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)


Lemma subst_ss_open_ss : forall T1 T2 (X:atom) P,
  shape P ->
  subst_ss X P (open_ss T1 T2) = open_ss (subst_ss X P T1) (subst_ss X P T2)
with subst_st_open_st : forall T1 T2 (X:atom) P,
  shape P ->
  subst_st X P (open_st T1 T2) = open_st (subst_st X P T1) (subst_ss X P T2).
Proof with auto.  
  ----- clear subst_ss_open_ss.
        intros T1 T2 X P shpP.
        apply (subst_ss_open_ss_rec T1 T2 X P 0).
        apply shpP.
  ----- clear subst_st_open_st.
        intros T1 T2 X P shpP.
        apply (subst_st_open_st_rec T1 T2 X P 0).
        apply shpP.
Qed.

Lemma subst_cc_open_cc : forall T1 T2 (X:atom) P,
  capture P ->
  subst_cc X P (open_cc T1 T2) = open_cc (subst_cc X P T1) (subst_cc X P T2).
Proof.
  intros T1 T2 X P capP.
  apply (subst_cc_open_cc_rec T1 T2 X P 0).
  apply capP.
Qed.

Lemma subst_cs_open_cs : forall T1 T2 (X:atom) P,
  capture P ->
  subst_cs X P (open_cs T1 T2) = open_cs (subst_cs X P T1) (subst_cc X P T2)
with subst_ct_open_ct : forall T1 T2 (X:atom) P,
  capture P ->
  subst_ct X P (open_ct T1 T2) = open_ct (subst_ct X P T1) (subst_cc X P T2).
Proof.
  ----- clear subst_cs_open_cs.
        intros T1 T2 X P capP.
        apply (subst_cs_open_cs_rec T1 T2 X P 0).
        apply capP.
  ----- clear subst_ct_open_ct.
        intros T1 T2 X P capP.
        apply (subst_ct_open_ct_rec T1 T2 X P 0).
        apply capP.
Qed.

Lemma subst_ss_open_cs : forall Z P C T,
  shape P ->
  subst_ss Z P (open_cs T C) = open_cs (subst_ss Z P T) C
with subst_st_open_ct : forall Z P C T,
  shape P ->
  subst_st Z P (open_ct T C) = open_ct (subst_st Z P T) C.
Proof with auto.
  ----- clear subst_ss_open_cs.
        intros Z P C T shpP.
        apply (subst_ss_open_cs_rec _ _ 0 _ _).
        apply shpP.
  ----- clear subst_st_open_ct.
        intros Z P C T shpP.
        apply (subst_st_open_ct_rec _ _ 0 _ _).
        apply shpP.
Qed.

Lemma subst_cs_open_ss : forall Z P C T,
  subst_cs Z P (open_ss T C) = open_ss (subst_cs Z P T) (subst_cs Z P C)
with subst_ct_open_st : forall Z P C T,
  subst_ct Z P (open_st T C) = open_st (subst_ct Z P T) (subst_cs Z P C).
Proof with auto.
  ----- clear subst_cs_open_ss.
        intros Z P C T.
        apply (subst_cs_open_ss_rec _ _ 0 _ _).
  ----- clear subst_ct_open_st.
        intros Z P C T.
        apply (subst_ct_open_st_rec _ _ 0 _ _).
Qed.


Lemma subst_ss_open_ss_var : forall (X Y:atom) P T,
  Y <> X ->
  shape P ->
  open_ss (subst_ss X P T) Y = subst_ss X P (open_ss T Y)
with subst_st_open_st_var : forall (X Y:atom) P T,
  Y <> X ->
  shape P ->
  open_st (subst_st X P T) Y = subst_st X P (open_st T Y).
Proof with congruence || auto.
  ----- clear subst_ss_open_ss_var.
        intros X Y P T Neq shpP.
        rewrite (subst_ss_open_ss T Y X P).
        f_equal...
        simpl...
        destruct (Y === X)...
        apply shpP.
  ----- clear subst_st_open_st_var.
        intros X Y P T Neq shpP.
        rewrite (subst_st_open_st T Y X P).
        f_equal...
        simpl...
        destruct (Y === X)...
        apply shpP.
Qed.

Lemma subst_cc_open_cc_var : forall (X Y:atom) P T,
  Y <> X ->
  capture P ->
  open_cc (subst_cc X P T) (cset_fvar Y) = subst_cc X P (open_cc T (cset_fvar Y)).
Proof.
  intros X Y P T Neq capP.
  rewrite (subst_cc_open_cc T (cset_fvar Y) X P).
  * rewrite <- (subst_cc_fresh X P (cset_fvar Y)).
    reflexivity.
    simpl.
    solve_notin.
  * apply capP.
Qed.

Lemma subst_cs_open_cs_var : forall (X Y:atom) P T,
  Y <> X ->
  capture P ->
  open_cs (subst_cs X P T) (cset_fvar Y) = subst_cs X P (open_cs T (cset_fvar Y))
with subst_ct_open_ct_var : forall (X Y:atom) P T,
  Y <> X ->
  capture P ->
  open_ct (subst_ct X P T) (cset_fvar Y) = subst_ct X P (open_ct T (cset_fvar Y)).
Proof.
  ----- clear subst_cs_open_cs_var.
        intros X Y P T Neq capP.
        rewrite (subst_cs_open_cs T (cset_fvar Y) X P).
        rewrite <- (subst_cc_fresh X P (cset_fvar Y)).
        * reflexivity.
        * simpl. solve_notin.
        * apply capP.
  ----- clear subst_ct_open_ct_var.
        intros X Y P T Neq capP.
        rewrite (subst_ct_open_ct T (cset_fvar Y) X P).
        rewrite <- (subst_cc_fresh X P (cset_fvar Y)).
        * reflexivity.
        * simpl. solve_notin.
        * apply capP.
Qed.

Lemma subst_cs_open_ss_var : forall (X : atom) Z P T,
  subst_cs Z P (open_ss T X) = open_ss (subst_cs Z P T) X
with subst_ct_open_st_var : forall (X : atom) Z P T,
  subst_ct Z P (open_st T X) = open_st (subst_ct Z P T) X.
Proof with auto.
  ----- clear subst_cs_open_ss_var.
        intros X Z P T...
        apply subst_cs_open_ss...
  ----- clear subst_ct_open_st_var.
        intros X Z P T.
        apply subst_ct_open_st...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_ss_intro_rec : forall X T2 U k,
  X `notin` fv_ss T2 ->
  open_ss_rec k U T2 = subst_ss X U (open_ss_rec k (shp_fvar X) T2)
with subst_st_intro_rec : forall X T2 U k,
  X `notin` fv_st T2 ->
  open_st_rec k U T2 = subst_st X U (open_st_rec k (shp_fvar X) T2).
Proof with congruence || auto.
  ----- clear subst_ss_intro_rec.
        induction T2; intros U k Fr; simpl in *; f_equal...
        - destruct (k === n)... simpl. destruct (X == X)...
        - destruct (a == X)... contradict Fr. rewrite e. fsetdec.
  -----clear subst_st_intro_rec.
        induction T2; intros U k Fr; simpl in *; f_equal...
Qed.

Lemma subst_cc_intro_rec : forall X T2 U k,
  X `notin` fv_cc T2 ->
  open_cc_rec k U T2 = subst_cc X U (open_cc_rec k (cset_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k H; unfold subst_cc in *; simpl in *;f_equal...
  destruct (NatSetImpl.mem k t0) eqn:kInt0...
  * destruct U; simpl; destruct (AtomSetImpl.mem X (union (singleton X) t)) eqn:xInx... 
    ** rewrite (AtomSetImpl.mem_1 (AtomSetImpl.union_2 t (AtomSetImpl.singleton_2 (eq_refl X) ))) in xInx.
       discriminate xInx.
    ** f_equal...
       *** rewrite (AtomSetEqual (union t1 t) (union (remove X (union (singleton X) t)) t1)).
           intro a. split.
           **** intro aInt1t.
                apply AtomSetImpl.union_1 in aInt1t.
                destruct aInt1t.
                ***** apply AtomSetImpl.union_3.
                      apply H0.
                ***** apply AtomSetImpl.union_2.
                      destruct (a === X) eqn:ax...
           **** intro aInBig.
                apply AtomSetImpl.union_1 in aInBig.
                destruct aInBig.
                ***** destruct (a === X)...
                      ****** rewrite e in *.
                             destruct ((AtomSetImpl.remove_1 (eq_refl X)) H0).
                      ****** apply AtomSetImpl.union_3.
                             destruct (AtomSetImpl.union_1 (AtomSetImpl.remove_3 H0)).
                             ******* destruct (n (eq_sym (AtomSetImpl.singleton_1 H1))).
                             ******* apply H1.
                ***** apply AtomSetImpl.union_2.
                      apply H0.
       *** apply NatSetEqual.
           fsetdec.
    ** rewrite (AtomSetImpl.mem_1 (AtomSetImpl.union_2 t (AtomSetImpl.singleton_2 (eq_refl X) ))) in xInx.
       discriminate xInx.
  * simpl.
    destruct (AtomSetImpl.mem X t) eqn:XInt...
    exfalso.
    apply (H (AtomSetImpl.mem_2 XInt)).
Qed.

Lemma subst_cs_intro_rec : forall X T2 U k,
  X `notin` fv_cs T2 ->
  open_cs_rec k U T2 = subst_cs X U (open_cs_rec k (cset_fvar X) T2)
with subst_ct_intro_rec : forall X T2 U k,
  X `notin` fv_ct T2 ->
  open_ct_rec k U T2 = subst_ct X U (open_ct_rec k (cset_fvar X) T2).
Proof with auto.
  ----- clear subst_cs_intro_rec.
        induction T2; intros U k Fr; simpl in *; f_equal...
        apply subst_cc_intro_rec.
        destruct c...
  ----- clear subst_ct_intro_rec.
        induction T2; intros U k Fr; simpl in *; f_equal...
        * apply subst_cc_intro_rec. destruct c...
Qed.


(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_ss_intro : forall X T2 U,
  X `notin` fv_ss T2 ->
  open_ss T2 U = subst_ss X U (open_ss T2 X)
with subst_st_intro : forall X T2 U,
  X `notin` fv_st T2 ->
  open_st T2 U = subst_st X U (open_st T2 X).
Proof with auto.
  ----- clear subst_ss_intro.
        intros.
        apply subst_ss_intro_rec...
  ----- clear subst_st_intro.
        intros.
        apply subst_st_intro_rec...
Qed.

Lemma subst_cc_intro : forall X T2 U,
  X `notin` fv_cc T2 ->
  open_cc T2 U = subst_cc X U (open_cc T2 (cset_fvar X)).
Proof with auto.
  intros.
  apply subst_cc_intro_rec...
Qed.

Lemma subst_cs_intro : forall X T2 U,
  X `notin` fv_cs T2 ->
  open_cs T2 U = subst_cs X U (open_cs T2 (cset_fvar X))
with subst_ct_intro : forall X T2 U,
  X `notin` fv_ct T2 ->
  open_ct T2 U = subst_ct X U (open_ct T2 (cset_fvar X)).
Proof with auto.
  ----- clear subst_cs_intro.
        intros.
        apply subst_cs_intro_rec...
  ----- clear subst_ct_intro.
        intros.
        apply subst_ct_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_se_rec_expr_aux : forall e j C u i P ,
  open_ee_rec j u C e = open_se_rec i P (open_ee_rec j u C e) ->
  e = open_se_rec i P e.
Proof with congruence || eauto.
  induction e; intros j C u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ce_rec_expr_aux : forall e j C u i P ,
  i <> j ->
  C <> cset_universal ->
  capture C ->
  AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc C) (fv_cc P)) ->
  open_ee_rec j u C e = open_ce_rec i P (open_ee_rec j u C e) ->
  e = open_ce_rec i P e.
Proof with congruence || eauto.
  induction e; intros j C u i P Neq UFin capU disj H; simpl in *;inversion H;f_equal...
  * apply (open_cc_rec_capture_aux c j C i P)...
Qed.

Lemma open_se_rec_shape_aux : forall e j Q i P,
  i <> j ->
  open_se_rec j Q e = open_se_rec i P (open_se_rec j Q e) ->
  e = open_se_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_ss_rec_shape_aux; eauto using open_st_rec_type_aux.
Qed.

Lemma open_ce_rec_capture_aux : forall e j Q i P,
  i <> j ->
  Q <> cset_universal ->
  capture Q ->
  AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc Q) (fv_cc P)) ->
  open_ce_rec j Q e = open_ce_rec i P (open_ce_rec j Q e) ->
  e = open_ce_rec i P e.
Proof with auto.
  induction e; intros j Q i P Neq QFin CapQ Disj Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_cs_rec_shape_aux; eauto using open_ct_rec_type_aux; eauto using open_cc_rec_capture_aux.
Qed.

Lemma open_se_open_ce_rec_capture_aux : forall e j C i Sh,
  open_ce_rec j C e = open_se_rec i Sh (open_ce_rec j C e) ->
  e = open_se_rec i Sh e.
Proof with auto.
  induction e; intros j C i Sh H; simpl in *; inversion H; f_equal;
  eauto using open_ss_open_cs_rec_shape_aux;
  eauto using open_st_open_ct_rec_type_aux;
  eauto using open_cs_open_ss_rec_shape_aux;
  eauto using open_ct_open_st_rec_type_aux...
Qed.

Lemma open_ce_open_se_rec_capture_aux : forall e j Sh i C,
  open_se_rec j Sh e = open_ce_rec i C (open_se_rec j Sh e) ->
  e = open_ce_rec i C e.
Proof with auto.
  induction e; intros j Sh i C H; simpl in *; inversion H; f_equal;
  eauto using open_ss_open_cs_rec_shape_aux;
  eauto using open_st_open_ct_rec_type_aux;
  eauto using open_cs_open_ss_rec_shape_aux;
  eauto using open_ct_open_st_rec_type_aux;
  try rewrite <- H2...
  rewrite <- H1. apply H1.
Qed.

Lemma open_se_rec_expr : forall e U k,
  expr e ->
  e = open_se_rec k U e.
Proof with auto.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_ss_rec_shape; auto using open_st_rec_type; unfold open_ee in *.
  * pick fresh x.
    apply (open_se_rec_expr_aux e1 0 (cset_fvar x) x _ _ )...
  * pick fresh x.
    unfold open_se in *.
    apply (open_se_rec_shape_aux e1 0 x _ _ )...
  * pick fresh x.
    unfold open_ce in *.
    apply (open_se_open_ce_rec_capture_aux _ 0 (cset_fvar x) _ _)...
Qed.

Lemma open_ce_rec_expr : forall e U k,
  expr e ->
  e = open_ce_rec k U e.
Proof with auto.
  intros e U k WF. revert k.
  induction WF; intro k; simpl; f_equal...
  * apply open_ct_rec_type. apply H.
  * pick fresh X for (union (fv_cc U) L).
    apply (open_ce_rec_expr_aux _ 0 (cset_fvar X) X _ _)...
    discriminate.
    apply cap_atoms...
    simpl. intros a aInInter.
    apply AtomSetFacts.inter_iff in aInInter.
    inversion aInInter.
    apply AtomSetImpl.singleton_1 in H2.
    rewrite H2 in Fr.
    apply (AtomSetImpl.union_2 L) in H3.
    apply (Fr H3).
    apply (H1 X)...
  * apply open_cc_rec_capture...
  * apply open_cs_rec_shape...
  * pick fresh X.
    apply (open_ce_open_se_rec_capture_aux _ 0 X _ _)...
    unfold open_se in H1.
    apply (H1 X)...
  * apply open_cs_rec_shape...
  * apply open_cc_rec_capture...
  * pick fresh X for (union (fv_cc U) L).
    apply (open_ce_rec_capture_aux _ 0 (cset_fvar X) _ _).
    discriminate. discriminate.
    apply cap_atoms...
    simpl. intros a aInInter.
    apply AtomSetFacts.inter_iff in aInInter.
    inversion aInInter.
    apply AtomSetImpl.singleton_1 in H2.
    rewrite H2 in Fr.
    apply (AtomSetImpl.union_2 L) in H3.
    apply (Fr H3).
    apply (H1 X)...
  * apply open_cc_rec_capture...
Qed.

Lemma subst_se_fresh : forall X U e,
  X `notin` fv_se e ->
  e = subst_se X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_ss_fresh; auto using subst_st_fresh.
Qed.

Lemma subst_ce_fresh : forall X U e,
  X `notin` fv_ce e ->
  e = subst_ce X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_cs_fresh; auto using subst_ct_fresh;
  auto using subst_cc_fresh.
Qed.

Lemma subst_se_open_se_rec : forall e T X U k,
  shape U ->
  subst_se X U (open_se_rec k T e) =
    open_se_rec k (subst_ss X U T) (subst_se X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_ss_open_ss_rec; auto using subst_st_open_st_rec.
Qed.

Lemma subst_ce_open_ce_rec : forall e T X U k,
  capture U ->
  X `notin` fv_cc T ->
  subst_ce X U (open_ce_rec k T e) =
    open_ce_rec k (subst_cc X U T) (subst_ce X U e).
Proof.
  intros e T X U k WU FninT. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_cs_open_cs_rec; auto using subst_ct_open_ct_rec; auto using subst_cc_open_cc_rec.
Qed.


Lemma subst_se_open_se : forall e T X U,
  shape U ->
  subst_se X U (open_se e T) = open_se (subst_se X U e) (subst_ss X U T).
Proof with auto.
  intros.
  unfold open_se.
  apply subst_se_open_se_rec...
Qed.

Lemma subst_ce_open_ce : forall e T X U,
  capture U ->
  X `notin` fv_cc T ->
  subst_ce X U (open_ce e T) = open_ce (subst_ce X U e) (subst_cc X U T).
Proof with auto.
  intros.
  unfold open_ce.
  apply subst_ce_open_ce_rec...
Qed.

Lemma subst_se_open_se_var : forall (X Y:atom) U e,
  Y <> X ->
  shape U ->
  open_se (subst_se X U e) Y = subst_se X U (open_se e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_se.
  rewrite subst_se_open_se_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_ce_open_ce_var : forall (X Y:atom) U e,
  Y <> X ->
  capture U ->
  open_ce (subst_ce X U e) (cset_fvar Y) = subst_ce X U (open_ce e (cset_fvar Y)).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_ce.
  rewrite subst_ce_open_ce_rec...
  repeat (simpl; unfold subst_cc).
  destruct (AtomSetImpl.mem X (singleton Y)) eqn:xIny...
  destruct (Neq (AtomSetImpl.singleton_1 (AtomSetImpl.mem_2 xIny))).
Qed.

Lemma subst_se_intro_rec : forall X e U k,
  X `notin` fv_se e ->
  open_se_rec k U e = subst_se X U (open_se_rec k (shp_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_ss_intro_rec;
    auto using subst_st_intro_rec.
Qed.

Lemma subst_ce_intro_rec : forall X e U k,
  X `notin` fv_ce e ->
  open_ce_rec k U e = subst_ce X U (open_ce_rec k (cset_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_cs_intro_rec;
    auto using subst_ct_intro_rec;
    auto using subst_cc_intro_rec.
Qed.

Lemma subst_se_intro : forall X e U,
  X `notin` fv_se e ->
  open_se e U = subst_se X U (open_se e X).
Proof with auto.
  intros.
  unfold open_se.
  apply subst_se_intro_rec...
Qed.

Lemma subst_ce_intro : forall X e U,
  X `notin` fv_ce e ->
  open_ce e U = subst_ce X U (open_ce e (cset_fvar X)).
Proof with auto.
  intros.
  unfold open_ce.
  apply subst_ce_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j C1 v u C2 i,
  i <> j ->
  C1 <> cset_universal ->
  capture C1 ->
  (AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc C1) (fv_cc C2))) ->
  open_ee_rec j v C1 e = open_ee_rec i u C2 (open_ee_rec j v C1 e) ->
  e = open_ee_rec i u C2 e.
Proof with congruence || eauto.
  induction e; intros j C1 v u C2 i Neq C1Fin capC1 Disj H; simpl in *; inversion H; f_equal...
  destruct (j===n)... destruct (i===n)...
  apply (open_cc_rec_capture_aux c j C1 i C2)...
Qed.

Lemma open_ee_rec_shape_aux : forall e j C V u i,
  open_se_rec j V e = open_ee_rec i u C (open_se_rec j V e) ->
  e = open_ee_rec i u C e.
Proof.
  induction e; intros j C V u i H; simpl; inversion H; f_equal; eauto.
  rewrite <- H2.
  apply H2.
Qed.

Lemma open_ee_rec_capture_aux : forall e j C V u i,
  i <> j ->
  V <> cset_universal ->
  capture V ->
  AtomSetImpl.Empty (AtomSetImpl.inter (fv_cc V) (fv_cc C)) ->
  open_ce_rec j V e = open_ee_rec i u C (open_ce_rec j V e) ->
  e = open_ee_rec i u C e.
Proof.
  induction e; intros j C V u i Neq Vfin CapV Disj H; simpl; inversion H; f_equal; eauto.
  apply open_cc_rec_capture_aux in H2.
  apply H2. apply Neq. apply Vfin. apply CapV. apply Disj.
Qed.


Lemma open_ee_rec_expr : forall e u C k,
  expr e ->
  e = open_ee_rec k u C e.
Proof with auto.
  intros e u C k WF; revert k; induction WF; intro k; simpl; f_equal...
  * pick fresh x for (union L (fv_cc C)).
    apply (open_ee_rec_expr_aux _ 0 (cset_fvar x) x _ _ _).
    discriminate. discriminate. apply cap_atoms...
    intros a aInInter. apply AtomSetFacts.inter_iff in aInInter. simpl in *. inversion aInInter.
    apply AtomSetImpl.singleton_1 in H2.
    rewrite H2 in *.
    apply (AtomSetImpl.union_3 L) in H3.
    apply (Fr H3)...
    unfold open_ee in H1.
    apply (H1 x)...
  * apply open_cc_rec_capture...
  * pick fresh x for (union L (fv_cc C)).
    apply (open_ee_rec_shape_aux _ 0 C x _ _).
    unfold open_se in H1.
    apply (H1 x)...
  * pick fresh x for (union L (fv_cc C)).
    apply (open_ee_rec_capture_aux _ 0 _ (cset_fvar x) _ _)...
    discriminate. apply cap_atoms...
    intros a aInInter. apply AtomSetFacts.inter_iff in aInInter. simpl in *. inversion aInInter.
    apply AtomSetImpl.singleton_1 in H2.
    rewrite H2 in *.
    apply (AtomSetImpl.union_3 L) in H3.
    apply (Fr H3)...
    unfold open_ce in H1.
    apply (H1 x)...
Qed.
(*
  intros u e C k Hexpr Cfin. revert k.
  induction Hexpr; intro k; simpl; f_equal...
  * pick fresh x.
    apply (open_ee_rec_expr_aux e1 0 C0 x _ _ _)...
    unfold open_ee in *.
    CFin
    destruct (capture_as_ns_empty C0 H0).
    csetdec.
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  ].
 *)

Lemma subst_ee_fresh : forall (x: atom) U u e,
  x `notin` (fv_ee e `union` fv_ce e) ->
  e = subst_ee x U u e.
Proof with auto using subst_cc_fresh, subst_ct_fresh, subst_cs_fresh.
  intros *; induction e; simpl; intro H; f_equal...
  - destruct (a==x)...
    exfalso. AtomSetDecide.fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 C e2 x U u k,
  expr u ->
  capture U ->
  C <> cset_universal ->
  subst_ee x U u (open_ee_rec k e2 C e1) =
    open_ee_rec k (subst_ee x U u e2) (subst_cc x U C) (subst_ee x U u e1).
Proof with auto.
  intros * WP WU CFin. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
  Case "exp_capp".
    rewrite <- subst_cc_open_cc_rec...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 C x U u,
  capture U ->
  expr u ->
  C <> cset_universal ->
  subst_ee x U u (open_ee e1 e2 C) =
    open_ee (subst_ee x U u e1) (subst_ee x U u e2) (subst_cc x U C).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u U e C,
  y <> x ->
  capture U ->
  expr u ->
  C <> cset_universal ->
  open_ee (subst_ee x U u e) y (subst_cc x U C) = subst_ee x U u (open_ee e y C).
Proof with congruence || auto.
  intros * Neq WU Wu CFin.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_se_open_ce_rec : forall Z P e k C,
  shape P ->
  subst_se Z P (open_ce_rec k C e) = open_ce_rec k C (subst_se Z P e).
Proof with auto.
  intros Z P e k C shpP. revert k.
  induction e; intro k; simpl; f_equal...
  * apply subst_st_open_ct_rec...
  * apply subst_ss_open_cs_rec...
  * apply subst_ss_open_cs_rec...
Qed.

Lemma subst_se_open_ee_rec : forall e1 C e2 Z P k,
  subst_se Z P (open_ee_rec k e2 C e1) =
    open_ee_rec k (subst_se Z P e2) C (subst_se Z P e1).
Proof with auto.
  induction e1; intros C e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_ce_open_se_rec : forall e1 Z  Q P k,
  capture P ->
  subst_ce Z P (open_se_rec k Q e1) =
    open_se_rec k (subst_cs Z P Q) (subst_ce Z P e1).
Proof with auto.
  induction e1; intros Z Q P k capP; simpl; f_equal...
  apply subst_ct_open_st_rec...
  apply subst_cs_open_ss_rec...
  apply subst_cs_open_ss_rec...
Qed.


Lemma subst_ce_open_se: forall Z P Q e,
  capture P ->
  subst_ce Z P (open_se e Q) =
    open_se  (subst_ce Z P e) (subst_cs Z P Q).
Proof with auto.
  intros Z P e C shpP.
  apply (subst_ce_open_se_rec _ _ _ _ _ )...
Qed.

Lemma subst_ce_open_ee_rec : forall e1 C e2 Z P k,
  capture P ->
  subst_ce Z P (open_ee_rec k e2 C e1) =
    open_ee_rec k (subst_ce Z P e2) (subst_cc Z P C) (subst_ce Z P e1).
Proof with auto.
  induction e1; intros C e2 Z P k capP; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
  apply subst_cc_open_cc_rec...
Qed.

Lemma subst_se_open_ce: forall Z P e C,
  shape P ->
  subst_se Z P (open_ce e C) = open_ce (subst_se Z P e) C.
Proof with auto.
  intros Z P e C shpP.
  apply (subst_se_open_ce_rec _ _ _ 0 _ )...
Qed.

Lemma subst_se_open_ee : forall e1 C e2 Z P,
  subst_se Z P (open_ee e1 e2 C) = open_ee (subst_se Z P e1)(subst_se Z P e2) C.
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_se_open_ee_rec...
Qed.

Lemma subst_ce_open_ee : forall e1 C e2 Z P,
  capture P ->
  subst_ce Z P (open_ee e1 e2 C) = open_ee (subst_ce Z P e1)(subst_ce Z P e2) (subst_cc Z P C).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ce_open_ee_rec...
Qed.

Lemma subst_se_open_ee_var : forall Z (x:atom) P e C,
  open_ee (subst_se Z P e) x C = subst_se Z P (open_ee e x C).
Proof with auto.
  intros.
  rewrite subst_se_open_ee...
Qed.

Lemma subst_ce_open_ee_var : forall Z (x:atom) P e C,
  capture P ->
  open_ee (subst_ce Z P e) x (subst_cc Z P C) = subst_ce Z P (open_ee e x C).
Proof with auto.
  intros.
  rewrite subst_ce_open_ee...
Qed.

Lemma subst_ee_open_se_rec : forall e P z U u k,
  capture U ->
  expr u ->
  subst_ee z U u (open_se_rec k P e) = open_se_rec k (subst_cs z U P) (subst_ee z U u e).
Proof with auto using subst_ct_open_st_rec, subst_cs_open_ss_rec.
  induction e; intros * WU Wu; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_se_rec_expr...
Qed.

Lemma subst_ee_open_ce_rec : forall e P z U u k,
  capture U ->
  expr u ->
  subst_ee z U u (open_ce_rec k P e) = open_ce_rec k (subst_cc z U P) (subst_ee z U u e).
Proof with auto using subst_ct_open_ct_rec, subst_cc_open_cc_rec, subst_cs_open_cs_rec.
  induction e; intros * WU Wu; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_ce_rec_expr...
Qed.

Lemma subst_ee_open_se : forall e P z U u,
  capture U ->
  expr u ->
  subst_ee z U u (open_se e P) = open_se (subst_ee z U u e) (subst_cs z U P).
Proof with auto using subst_ct_open_ct_rec, subst_cc_open_cc_rec, subst_cs_open_cs_rec.
  intros.
  unfold open_se.
  apply subst_ee_open_se_rec...
Qed.

Lemma subst_ee_open_ce : forall e P z U u,
  capture U ->
  expr u ->
  subst_ee z U u (open_ce e P) = open_ce (subst_ee z U u e) (subst_cc z U P).
Proof with auto.
  intros.
  unfold open_ce.
  apply subst_ee_open_ce_rec...
Qed.

Lemma subst_ee_open_se_var : forall z (X:atom) u U e,
  capture U ->
  expr u ->
  open_se (subst_ee z U u e) X = subst_ee z U u (open_se e X).
Proof with auto.
  intros * WU Wu.
  rewrite subst_ee_open_se...
Qed.

Lemma subst_ee_open_ce_var : forall z (X:atom) U u e,
  z <> X ->
  capture U ->
  expr u ->
  open_ce (subst_ee z U u e) (cset_fvar X) = subst_ee z U u (open_ce e (cset_fvar X)).
Proof with auto.
  intros * Fr WU Wu.
  rewrite subst_ee_open_ce...
    repeat(simpl; unfold subst_cc); destruct (AtomSetImpl.mem z (singleton X)) eqn:HX...
    exfalso. rewrite <- AtomSetFacts.mem_iff in *. AtomSetDecide.fsetdec.
Qed.

Lemma subst_ee_intro_rec : forall x e u k C,
  x `notin` (fv_ee e) `union` (fv_ce e)->
  open_ee_rec k u C e = (subst_ee x C u (open_ee_rec k (exp_fvar x) (cset_fvar x) e)).
Proof with congruence || auto using subst_cc_intro_rec, subst_ct_fresh, subst_cs_fresh, subst_cc_fresh.
  induction e; intros * Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... AtomSetDecide.fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u C,
  x `notin` fv_ee e `union` (fv_ce e) ->
  open_ee e u C = subst_ee x C u (open_ee e x (cset_fvar x)).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_cc_capture : forall Z C D,
  capture C ->
  capture D ->
  capture (subst_cc Z C D).
Proof with eauto.
  intros Z C D capC capD.
  induction C; induction D...
  * unfold subst_cc...
    destruct (AtomSetImpl.mem Z t)...
  * unfold subst_cc...
    destruct (AtomSetImpl.mem Z t1)...
    apply capture_as_ns_empty in capC...
    apply capture_as_ns_empty in capD...
    destruct capC; destruct capD...
    inversion H. inversion H0...
    rewrite <- (union_empty_nats {}N).
    apply cap_atoms...
    discriminate. discriminate.
Qed.

Lemma subst_ss_shape : forall Z P T,
  shape T ->
  shape P ->
  shape (subst_ss Z P T)
with subst_st_type : forall Z P T,
  type T ->
  shape P ->
  type (subst_st Z P T).
Proof with auto.
  ----- clear subst_ss_shape. intros Z P T HT HP.
        induction HT; simpl...
        * destruct (X == Z)...
        * pick fresh Y and apply shape_arrow...
          rewrite <- subst_st_open_ct...
        * pick fresh Y and apply shape_sall...
          rewrite subst_st_open_st_var...
        * pick fresh Y and apply shape_call...
          rewrite <- subst_st_open_ct...
  ----- clear subst_st_type. intros Z P T HT HP.
        induction HT; simpl...
Qed.

Lemma subst_cs_shape : forall Z P T,
  shape T ->
  capture P ->
  shape (subst_cs Z P T)
with subst_ct_type : forall Z P T,
  type T ->
  capture P ->
  type (subst_ct Z P T).
Proof with auto using subst_cc_capture.
  ----- clear subst_cs_shape. intros Z P T HT HP.
        induction HT; simpl...
        * pick fresh Y and apply shape_arrow...
          rewrite subst_ct_open_ct_var...
        * pick fresh Y and apply shape_sall...
          rewrite <- subst_ct_open_st_var...
        * pick fresh Y and apply shape_call...
          rewrite subst_ct_open_ct_var...
  ----- clear subst_ct_type. intros Z P T HT HP.
        induction HT; simpl...
Qed.

(** The following lemma depends on [subst_tt_type],
    [subst_te_open_ee_var], and [sbust_te_open_te_var]. *)

Lemma subst_se_expr : forall Z P e,
  expr e ->
  shape P ->
  expr (subst_se Z P e).
Proof with eauto using subst_ss_shape.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_ss_shape; auto using subst_st_type.
  * apply (expr_abs L (subst_st Z P T) (subst_se Z P e1)).
    apply subst_st_type...
    intros x xnInl.
    rewrite subst_se_open_ee_var...
  * apply (expr_sabs (AtomSetImpl.union L (AtomSetImpl.singleton Z)) (subst_ss Z P Sh) (subst_se Z P e1)).
    apply subst_ss_shape...
    intros.
    rewrite subst_se_open_se_var...
  * apply (expr_cabs L C (subst_se Z P e1)).
    apply H.
    intros.
    rewrite <- subst_se_open_ce.
    apply (H1 X)...
    apply Hp.
Qed.

Lemma subst_ce_expr : forall Z P e,
  expr e ->
  capture P ->
  expr (subst_ce Z P e).
Proof with eauto.
  intros Z P e exprE capP.
  induction exprE; simpl; auto using subst_cs_shape; auto using subst_ct_type; auto using subst_cc_capture...
  * apply expr_abs with (L:=(union L {{ Z }}))...
    ** apply subst_ct_type...
    ** intros x xnInL.
       replace (exp_fvar x) with (subst_ce Z P x) by auto...
       replace (cset_fvar x) with (subst_cc Z P (cset_fvar x))...
       rewrite <- subst_ce_open_ee...
       unfold subst_cc; simpl...
       replace (AtomSetImpl.mem Z (singleton x)) with false...
       symmetry.
       apply AtomSetFacts.not_mem_iff...
  * apply expr_sabs with (L:=(union L {{ Z }}))...
    ** apply subst_cs_shape...
    ** intros x xnInL.
       replace (shp_fvar x) with (subst_cs Z P x) by auto...
       rewrite <- subst_ce_open_se...
  * apply expr_cabs with (L:=(union L {{ Z }}))...
    ** apply subst_cc_capture...
    ** intros X XnInL.
       replace (cset_fvar X) with (subst_cc Z P (cset_fvar X)).
       rewrite <- subst_ce_open_ce...
       unfold subst_cc; simpl...
       replace (AtomSetImpl.mem Z (singleton X)) with false...
       symmetry.
       apply AtomSetFacts.not_mem_iff...
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ee_expr : forall z e1 C e2,
  capture C ->
  expr e1 ->
  expr e2 ->
  expr (subst_ee z C e2 e1).
Proof with eauto using subst_cc_capture, subst_ct_type, subst_cs_shape.
  intros * HC He1 He2.
  induction He1; simpl; unfold subst_cc; auto...
  * destruct (x == z)...
  * eapply expr_abs with (L := L `union` (singleton z))...
    intros. replace (cset_fvar x) with (subst_cc z C (cset_fvar x))...
    rewrite subst_ee_open_ee_var; simpl...
    discriminate.
    repeat (simpl; unfold subst_cc). 
    destruct (AtomSetImpl.mem z (singleton x)) eqn:HZ...
    rewrite <- AtomSetFacts.mem_iff in *. AtomSetDecide.fsetdec...
  * eapply expr_sabs with (L := L `union` (singleton z))...
    intros.
    rewrite subst_ee_open_se_var...
  * eapply expr_cabs with (L := L `union` (singleton z))...
    intros...
    rewrite subst_ee_open_ce_var...
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

#[export] Hint Resolve 
  subst_ss_shape subst_st_type  subst_ct_type subst_se_expr subst_ee_expr subst_ce_expr
  subst_cc_capture : core.

(** We also add as hints the lemmas concerning [body_e]. *)

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the MetatheoryEnv library. *)

#[export] Hint Extern 1 (binds _ (?F (subst_ss ?X ?U ?T)) _) =>
  unsimpl (subst_sb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_st ?X ?U ?T)) _) =>
  unsimpl (subst_sb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_cc ?X ?U ?T)) _) =>
  unsimpl (subst_cb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_cs ?X ?U ?T)) _) =>
  unsimpl (subst_cb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_ct ?X ?U ?T)) _) =>
  unsimpl (subst_cb X U (F T)) : core.
