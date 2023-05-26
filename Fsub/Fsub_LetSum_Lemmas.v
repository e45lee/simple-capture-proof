(** Administrative lemmas for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Fsub.Fsub_LetSum_Infrastructure.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma union_rewrite : forall S1 S2 (t : atom),
  t `notin` (union S1 S2) <->
  (t `notin` S1) /\ (t `notin` S2).
Proof.
  intros S1 S2 t.
  split; intro H.
  * split; auto.
  * intro nIn. inversion H.
    apply AtomSetFacts.union_iff in nIn.
    destruct nIn; auto.
Qed.

Lemma capture_from_wf_cap : forall E C,
  wf_cap E C -> capture C.
Proof.
  intros E T H; induction H; eauto.
Qed.

Lemma shape_from_wf_shp : forall E Sh,
  wf_shp E Sh -> shape Sh
with type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  ----- clear shape_from_wf_shp.
        intros E T H; induction H; eauto.
        * eapply shape_call...
          apply (capture_from_wf_cap E C H).
          intros.
          apply (type_from_wf_typ (X ~ bind_sub_cap C ++ E) (open_ct T (cset_fvar X)) (H0 X H1)).
  ----- clear type_from_wf_typ.
        intros E T H; induction H.
        apply (type_pair S C (shape_from_wf_shp E S H) (capture_from_wf_cap E C H0)).
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_cap_weakening : forall C E F G,
  wf_cap (G ++ E) C ->
  uniq (G ++ F ++ E) ->
  wf_cap (G ++ F ++ E) C.
Proof with simpl_env; eauto.
  intros C E F G Hwf_cap Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_cap; intros G Hok Heq; subst...
  apply wf_cset_set...
  intros a aNinA.
  rewrite <- app_assoc.
  destruct (H a)...
  * left. destruct H0.
    eapply ex_intro.
    apply binds_app_iff in H0. destruct H0...
  * right. destruct H0.
    eapply ex_intro.
    apply binds_app_iff in H0. destruct H0...
Qed.

Lemma wf_shp_weakening : forall Sh E F G,
  wf_shp (G ++ E) Sh ->
  uniq (G ++ F ++ E) ->
  wf_shp (G ++ F ++ E) Sh
with wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  ----- clear wf_shp_weakening.
        intros Sh E F G Hwf_shp Hk.
        remember (G ++ E) as F'.
        generalize dependent G.
        induction Hwf_shp; intros G Hok Heq; subst...
        * apply (wf_shp_arrow (union L (union (dom E) (union (dom F) (dom G)))) _ _)...
          intros X XnInL.
          apply (wf_typ_weakening _ E F (X ~ bind_typ T1 ++ G)).
          apply (H0 X)...
          apply uniq_cons...
        * apply (wf_shp_sall (union L (union (dom E) (union (dom F) (dom G)))) _ _)...
          intros X XnInL.
          eapply (wf_typ_weakening (open_st T X) E F (X ~ bind_sub_shp S ++ G) _)...
          Unshelve.
          rewrite app_assoc.
          eapply (H X _).
          Unshelve.
          solve_notin.
        * apply (wf_shp_call (union L (union (dom E) (union (dom F) (dom G)))) _ _)...
          ** apply wf_cap_weakening...
          ** intros X XnInL.
             eapply (wf_typ_weakening (open_ct T (cset_fvar X)) E F (X ~ bind_sub_cap C ++ G) _)...
             Unshelve.
             rewrite app_assoc.
              eapply (H0 X _).
              Unshelve.
              solve_notin.
  ----- clear wf_typ_weakening.
        intros Sh E F G Hwf_typ Hk.
        remember (G ++ E) as F'.
        generalize dependent G.
        induction Hwf_typ; intros G Hok Heq; subst...
        apply wf_pair...
        apply wf_cap_weakening...
Qed.

Lemma wf_cap_weaken_head : forall C E F,
  wf_cap E C ->
  uniq (F ++ E) ->
  wf_cap (F ++ E) C.
Proof.
  intros.
  rewrite_env (empty ++ F ++ E).
  auto using wf_cap_weakening.
Qed.

Lemma wf_shp_weaken_head : forall Sh E F,
  wf_shp E Sh ->
  uniq (F ++ E) ->
  wf_shp (F ++ E) Sh.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_shp_weakening.
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_cap_narrowing_shp : forall V U C E F X,
  wf_cap (F ++ X ~ bind_sub_shp V ++ E) C ->
  wf_cap (F ++ X ~ bind_sub_shp U ++ E) C.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_cap.
  remember (F ++ X ~ bind_sub_shp V ++ E) as G.
  generalize dependent F.
  induction Hwf_cap; intros F Heq; subst...
  apply wf_cset_set...
  intros a anInA.
  destruct (H a)...
  * left. destruct H0.
    eapply ex_intro.
    apply binds_app_1 in H0.
    destruct H0.
    ** apply binds_app_2. apply H0.
    ** apply binds_app_1 in H0.
       destruct H0.
       *** apply binds_one_iff in H0.
           inversion H0.
           discriminate H2.
       *** apply binds_app_3. apply binds_app_3. apply H0.
  * right. destruct H0. 
    eapply ex_intro.
    apply binds_app_1 in H0.
    destruct H0.
    ** apply binds_app_2. apply H0.
    ** apply binds_app_1 in H0.
       destruct H0.
       *** apply binds_one_iff in H0.
           inversion H0.
           discriminate H2.
       *** apply binds_app_3. apply binds_app_3. apply H0.
Qed.

Lemma wf_cap_narrowing_cap : forall V U C E F X,
  wf_cap (F ++ X ~ bind_sub_cap V ++ E) C ->
  wf_cap (F ++ X ~ bind_sub_cap U ++ E) C.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_cap.
  remember (F ++ X ~ bind_sub_cap V ++ E) as G.
  generalize dependent F.
  induction Hwf_cap; intros F Heq; subst...
  apply wf_cset_set...
  intros a anInA.
  destruct (H a anInA).
  * left. destruct (X == a);destruct H0...
    apply binds_app_1 in H0.
    destruct H0.
    ** eapply ex_intro. apply binds_app_iff. left.
       apply H0.
    ** apply binds_app_1 in H0. destruct H0.
       *** eapply ex_intro. apply binds_app_iff. right. apply binds_app_iff. left.
           apply binds_one...
           apply binds_one_iff in H0.
           inversion H0...
       *** eapply ex_intro. apply binds_app_iff. right. apply binds_app_iff. right.
           apply H0.
  * right. destruct (X == a);destruct H0...
    apply binds_app_1 in H0.
    destruct H0.
    ** eapply ex_intro.
       apply binds_app_2. apply H0.
    ** apply binds_app_1 in H0.
       destruct H0.
       *** eapply ex_intro.
           apply binds_one_iff in H0.
           inversion H0.
           discriminate H2.
           Unshelve.
           apply (pair shp_top (cset_set {} {}N)).
       *** eapply ex_intro.
           apply binds_app_3. apply binds_app_3. apply H0.
    ** eapply ex_intro.
       apply binds_app_iff in H0.
       destruct H0...
       apply binds_app_iff in H0.
       destruct H0...
       apply binds_one_iff in H0.
       inversion H0...
       symmetry in H1. destruct (n H1).
Qed.

Lemma wf_cap_narrowing_typ : forall V U C E F X,
  wf_cap (F ++ X ~ bind_typ V ++ E) C ->
  wf_cap (F ++ X ~ bind_typ U ++ E) C.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_cap.
  remember (F ++ X ~ bind_typ V ++ E) as G.
  generalize dependent F.
  induction Hwf_cap; intros F Heq; subst...
  apply wf_cset_set...
  intros a anInA.
  destruct (H a)...
  * left. destruct H0.
    eapply ex_intro.
    apply binds_app_1 in H0.
    destruct H0.
    ** apply binds_app_2. apply H0.
    ** apply binds_app_1 in H0.
       destruct H0.
       *** apply binds_one_iff in H0.
           inversion H0.
           discriminate H2.
       *** apply binds_app_3. apply binds_app_3. apply H0.
  * right. destruct H0 as [T BindsA]. 
    analyze_binds BindsA...
Qed.

Lemma wf_shp_narrowing_shp : forall V U Sh E F X,
  wf_shp (F ++ X ~ bind_sub_shp V ++ E) Sh ->
  wf_shp (F ++ X ~ bind_sub_shp U ++ E) Sh
with wf_typ_narrowing_shp :  forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub_shp V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub_shp U ++ E) T.
Proof with simpl_env; eauto.
  ----- clear wf_shp_narrowing_shp.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_sub_shp V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        * destruct (x == X)...
        * apply (wf_shp_arrow L _ _ _)...
          intros x xnInL.
          apply (wf_typ_narrowing_shp V _ _ _ (x ~ bind_typ T1 ++ F) _).
          apply (H0 x xnInL).
        * apply (wf_shp_sall L (F ++ X ~ bind_sub_shp U ++ E) S T).
          ** apply (IHHwf_shp F)...
          ** intros X0 X0nInL.
             apply (wf_typ_narrowing_shp V U (open_st T X0) E (X0 ~ bind_sub_shp S ++ F) X)...
        * apply (wf_shp_call L (F ++ X ~ bind_sub_shp U ++ E) C T).
          ** apply (wf_cap_narrowing_shp V _ _ _ _ _)...
          ** intros X0 X0nInL.
              apply (wf_typ_narrowing_shp V U (open_ct T (cset_fvar X0)) E (X0 ~ bind_sub_cap C ++ F) X)...
  ----- clear wf_typ_narrowing_shp.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_sub_shp V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        apply wf_pair.
        * apply (wf_shp_narrowing_shp V _ _ _ _ _)...
        * apply (wf_cap_narrowing_shp V _ _ _ _ _)...
Qed.

Lemma wf_shp_narrowing_cap : forall V U Sh E F X,
  wf_shp (F ++ X ~ bind_sub_cap V ++ E) Sh ->
  wf_shp (F ++ X ~ bind_sub_cap U ++ E) Sh
with wf_typ_narrowing_cap :  forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub_cap V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub_cap U ++ E) T.
Proof with simpl_env; eauto.
  ----- clear wf_shp_narrowing_cap.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_sub_cap V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        * destruct (x == X)... rewrite e in H.
          apply binds_app_1 in H.
          destruct H.
          ** apply (wf_shp_fvar _ U0).
             apply binds_app_2. rewrite e. apply H.
          ** apply binds_app_1 in H. destruct H.
             *** apply binds_one_iff in H.
                 inversion H.
                 discriminate H1.
             *** apply (wf_shp_fvar _ U0).
                 apply binds_app_3. apply binds_app_3.
                 rewrite e. apply H.
        * apply (wf_shp_arrow L _ _ _)...
          intros X0 X0nInL.
          apply (wf_typ_narrowing_cap V _ _ _ (X0 ~ bind_typ T1 ++ F) _).
          apply (H0 X0 X0nInL).
        * apply (wf_shp_sall L (F ++ X ~ bind_sub_cap U ++ E) S T).
          ** apply (IHHwf_shp F)...
          ** intros X0 X0nInL.
             apply (wf_typ_narrowing_cap V U (open_st T X0) E (X0 ~ bind_sub_shp S ++ F) X)...
        * apply (wf_shp_call L (F ++ X ~ bind_sub_cap U ++ E) C T).
          ** apply (wf_cap_narrowing_cap V _ _ _ _ _)...
          ** intros X0 X0nInL.
              apply (wf_typ_narrowing_cap V U (open_ct T (cset_fvar X0)) E (X0 ~ bind_sub_cap C ++ F) X)...
  ----- clear wf_typ_narrowing_cap.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_sub_cap V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        apply wf_pair.
        * apply (wf_shp_narrowing_cap V _ _ _ _ _)...
        * apply (wf_cap_narrowing_cap V _ _ _ _ _)...
Qed.

Lemma wf_shp_narrowing_typ : forall V U Sh E F X,
  wf_shp (F ++ X ~ bind_typ V ++ E) Sh ->
  wf_shp (F ++ X ~ bind_typ U ++ E) Sh
with wf_typ_narrowing_typ :  forall V U T E F X,
  wf_typ (F ++ X ~ bind_typ V ++ E) T ->
  wf_typ (F ++ X ~ bind_typ U ++ E) T.
Proof with simpl_env; eauto.
  ----- clear wf_shp_narrowing_typ.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_typ V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        * destruct (x == X); subst...
          analyze_binds H...  
        * apply (wf_shp_arrow L _ _ _)...
          intros x xnInL.
          apply (wf_typ_narrowing_typ V _ _ _ (x ~ bind_typ T1 ++ F) _).
          apply (H0 x xnInL).
        * apply (wf_shp_sall L (F ++ X ~ bind_typ U ++ E) S T).
          ** apply (IHHwf_shp F)...
          ** intros X0 X0nInL.
             apply (wf_typ_narrowing_typ V U (open_st T X0) E (X0 ~ bind_sub_shp S ++ F) X)...
        * apply (wf_shp_call L (F ++ X ~ bind_typ U ++ E) C T).
          ** apply (wf_cap_narrowing_typ V _ _ _ _ _)...
          ** intros X0 X0nInL.
             eapply (wf_typ_narrowing_typ V U (open_ct T (cset_fvar X0)) E (X0 ~ bind_sub_cap C ++ F) X)...
  ----- clear wf_typ_narrowing_typ.
        intros V U T E F X Hwf_shp.
        remember (F ++ X ~ bind_typ V ++ E) as G.
        generalize dependent F.
        induction Hwf_shp; intros F Heq; subst...
        apply wf_pair.
        * apply (wf_shp_narrowing_typ V _ _ _ _ _)...
        * apply (wf_cap_narrowing_typ V _ _ _ _ _)...
Qed.


Lemma wf_cap_strengthening_shp : forall E F x U T,
 wf_cap (F ++ x ~ bind_sub_shp U ++ E) T ->
 wf_cap (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_sub_shp U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  apply wf_cset_set...
  intros a aInA.
  destruct (H a aInA).
  * left. destruct (x == a); destruct H0...
    ** apply binds_app_iff in H0.
       destruct H0.
       *** eapply ex_intro.
           apply binds_app_2.
           apply H0.
       *** apply binds_app_iff in H0. destruct H0.
           **** eapply ex_intro.
                apply binds_one_iff in H0.
                inversion H0.
                discriminate H2.
                Unshelve.
                apply x0.
           **** eapply ex_intro.
                apply binds_app_3.
                apply H0.
    ** apply binds_app_iff in H0.
       destruct H0.
       *** eapply ex_intro.
           apply binds_app_2.
           apply H0.
        *** apply binds_app_iff in H0. destruct H0.
           **** eapply ex_intro.
                apply binds_one_iff in H0.
                inversion H0.
                symmetry in H1.
                destruct (n H1).
                Unshelve.
                apply x0.
           **** eapply ex_intro.
                apply binds_app_3.
                apply H0.
  * right. destruct (x == a); destruct H0...
    ** apply binds_app_iff in H0.
       destruct H0.
       *** eapply ex_intro.
           apply binds_app_2.
           apply H0.
       *** apply binds_app_iff in H0. destruct H0.
           **** eapply ex_intro.
                apply binds_one_iff in H0.
                inversion H0.
                discriminate H2.
                Unshelve.
                apply x0.
           **** eapply ex_intro.
                apply binds_app_3.
                apply H0.
    ** apply binds_app_iff in H0.
       destruct H0.
       *** eapply ex_intro.
           apply binds_app_2.
           apply H0.
        *** apply binds_app_iff in H0. destruct H0.
           **** eapply ex_intro.
                apply binds_one_iff in H0.
                inversion H0.
                discriminate H2.
                Unshelve.
                apply x0.
           **** eapply ex_intro.
                apply binds_app_3.
                apply H0.
Qed.

Lemma subst_sb_cap_iden : forall U Z P,
  subst_sb Z P (bind_sub_cap U) = bind_sub_cap U.
Proof.
  intros U Z P.
  auto.
Qed.

Lemma subst_cb_cap : forall U Z P,
  subst_cb Z P (bind_sub_cap U) = bind_sub_cap (subst_cc Z P U).
Proof.
  intros U Z P.
  auto.
Qed.

Lemma subst_sb_typ : forall V Z P,
  subst_sb Z P (bind_typ V) = bind_typ (subst_st Z P V).
Proof.
  intros V Z P.
  auto.
Qed.

Lemma subst_sb_shp : forall V Z P,
  subst_sb Z P (bind_sub_shp V) = bind_sub_shp (subst_ss Z P V).
Proof.
  intros V Z P.
  auto.
Qed.

Lemma subst_ss_atom : forall Sh A X,
  X <> A ->
  (subst_ss A Sh X) = X.
Proof.
  intros Sh A X XNA.
  simpl.
  destruct (X == A).
  * destruct (XNA e).
  * reflexivity.
Qed.

Lemma wf_cap_subst_sbs : forall F Q E Z P T,
  wf_cap (F ++ Z ~ bind_sub_shp Q ++ E) T ->
  wf_shp E P ->
  uniq (map (subst_sb Z P) F ++ E) ->
  wf_cap (map (subst_sb Z P) F ++ E) T.
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub_shp Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst...
  apply wf_cset_set.
  intros a aIna.
  destruct (H a aIna).
  * left. destruct H0. apply binds_app_iff in H0.
    destruct H0...
    ** eapply ex_intro. apply binds_app_iff.
       left.
       rewrite <- (subst_sb_cap_iden _ Z P).
       apply (binds_map_2 _ _ (subst_sb Z P) _ ).
       apply H0.
    ** apply binds_app_iff in H0. destruct H0.
       *** eapply ex_intro. apply binds_one_iff in H0.
           inversion H0. discriminate H2.
           Unshelve. apply x.
       *** eapply ex_intro. apply binds_app_iff. right. apply H0.
  * right. destruct H0. apply binds_app_iff in H0.
    destruct H0...
    ** eapply ex_intro. apply binds_app_iff.
       left.
       Unshelve.
       2 : {
        apply (subst_st Z P x).
       }
       rewrite <- subst_sb_typ.
       apply binds_map_2.
       apply H0.
    ** apply binds_app_iff in H0. destruct H0.
       *** eapply ex_intro. apply binds_one_iff in H0.
           inversion H0. discriminate H2. Unshelve. apply x.
       *** eapply ex_intro. apply binds_app_iff. right. apply H0.
Qed.

Lemma wf_shp_subst_sbs : forall F Q E Z P T,
  wf_shp (F ++ Z ~ bind_sub_shp Q ++ E) T ->
  wf_shp E P ->
  uniq (map (subst_sb Z P) F ++ E) ->
  wf_shp (map (subst_sb Z P) F ++ E) (subst_ss Z P T)
with wf_typ_subst_sbs : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub_shp Q ++ E) T ->
  wf_shp E P ->
  uniq (map (subst_sb Z P) F ++ E) ->
  wf_typ (map (subst_sb Z P) F ++ E) (subst_st Z P T).
Proof with simpl_env; eauto using
  wf_typ_weaken_head, type_from_wf_typ, shape_from_wf_shp.
----- 
  clear wf_shp_subst_sbs.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub_shp Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_ss...
  * destruct (x == Z)...
    ** apply wf_shp_weaken_head...
    ** apply binds_app_iff in H. destruct H.
        *** apply (wf_shp_fvar _ (subst_ss Z P U) _).
            apply binds_app_iff.
            left.
            rewrite <- subst_sb_shp.
            apply binds_map_2.
            apply H.
        *** apply binds_app_iff in H. destruct H.
            **** apply binds_one_iff in H. inversion H.
                destruct (n H0).
            **** apply (wf_shp_fvar _ U _).
                apply binds_app_iff. right. apply H.
  * apply (wf_shp_arrow (union (union L (union (dom F) (dom E))) {{ Z }}) _ _)...
    intros X XnInL.
    rewrite <- subst_st_open_ct...
    rewrite_env ((map (subst_sb Z P) (X ~ bind_typ T1 ++ F) ++ E)).
    apply (wf_typ_subst_sbs _ Q _ _ _ _)...
  * apply (wf_shp_sall (union (union L (union (dom F) (dom E))) {{ Z }}) _ _)...
    ** intros X XninL. rewrite <- subst_sb_shp. rewrite <- app_assoc.
        rewrite <- map_cons. rewrite <- (subst_ss_atom P Z X)...
        rewrite <- subst_st_open_st.
        rewrite <- app_assoc.
        rewrite <- map_cons.
        apply (wf_typ_subst_sbs _ Q _ _ _ _)...
        apply (shape_from_wf_shp E P)...
  * apply (wf_shp_call (union (union L (union (dom F) (dom E))) {{ Z }}) _ _)...
    ** apply (wf_cap_subst_sbs _ Q _ _ _ _)...
    ** intros X XnInL.
        rewrite <- (subst_sb_cap_iden _ Z P)...
        rewrite <- app_assoc.
        rewrite <- map_cons.
        unfold open_ct.
        erewrite  <- subst_st_open_ct_rec.
        eapply wf_typ_subst_sbs...
        eapply shape_from_wf_shp...
-----
  clear wf_typ_subst_sbs.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub_shp Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_ss...
  apply wf_pair.
  * induction P...
  * apply (wf_cap_subst_sbs _ Q _ _ _ _)...
Qed.

Lemma union_empty:
  (NatSetImpl.union {}N {}N) = {}N.
Proof.
  apply NatSetEqual.
  split; intros H.
  * apply NatSetImpl.union_1 in H. destruct H; auto.
  * apply NatSetImpl.empty_1 in H. destruct H.
Qed.
#[export] Hint Rewrite union_empty : core.

Lemma wf_cap_subst_cbc : forall F Q E Z P T,
  wf_cap (F ++ Z ~ bind_sub_cap Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_cap (map (subst_cb Z P) F ++ E) (subst_cc Z P T).
Proof with simpl_env; eauto using wf_cap_weaken_head, capture_from_wf_cap.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub_cap Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst...
  repeat (simpl; unfold subst_cc).
  destruct (AtomSetImpl.mem Z A) eqn:ZinA... destruct P...
  * destruct (capture_as_ns_empty (cset_set t t0))... discriminate.
    inversion H0; subst...
    rewrite union_empty.
    apply (wf_cset_set (map (subst_cb Z (cset_set x {}N)) F ++ E) (union (remove Z A) x)).
    intros a aIna.
    (* I am not entirely sure about how to procede here, if a `in` A, we can apply H
       but if a `in` x, I am not certain.
       
       If a `in` x, note that x is well formed in E*)
    inversion WP; subst...
    rewrite AtomSetFacts.union_iff in aIna; destruct aIna as [InRemove | InX]...
    + assert (a `in` A). AtomSetDecide.fsetdec.
      assert (a <> Z). AtomSetDecide.fsetdec.
      destruct (H a) as [[U BindsU] | [V BindsV]]...
      - analyze_binds BindsU...
        left; eexists.
        apply binds_app_2...
        eapply binds_map_2 with (f := subst_cb Z (cset_set x {}N)) in BindsTac...
      - analyze_binds BindsV...
        right; eexists.
        apply binds_app_2...
        eapply binds_map_2 with (f := subst_cb Z (cset_set x {}N)) in BindsTac...
    + destruct (H3 a) as [[U BindsU] | [V BindsV]]...
  *  apply (wf_cset_set (map (subst_cb Z P) F ++ E) A).
    intros a aInA.
    destruct (H a aInA)...
    ** left. destruct H0. apply binds_app_1 in H0. destruct H0.
       *** eexists.
           apply binds_app_2.
           eapply binds_map_2 with (f := subst_cb Z P) in H0...
       *** analyze_binds H0...
           exfalso. rewrite <- AtomSetFacts.not_mem_iff in ZinA...
             (* For Ed, nothing bad, just didn't get a chance to finish this off *)
    ** right. destruct H0. apply binds_app_1 in H0. destruct H0.
      *** eexists.
          apply binds_app_2.
          eapply binds_map_2 with (f := subst_cb Z P) in H0...
      *** analyze_binds H0...
Qed.

Lemma wf_cap_subst_cbt : forall F Q E Z P T,
  wf_cap (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_cap (map (subst_cb Z P) F ++ E) (subst_cc Z P T).
Proof with simpl_env; eauto using wf_cap_weaken_head, capture_from_wf_cap.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst...
  repeat (simpl; unfold subst_cc).
  destruct (AtomSetImpl.mem Z A) eqn:ZinA... destruct P...
  * destruct (capture_as_ns_empty (cset_set t t0))... discriminate.
    inversion H0; subst...
    rewrite union_empty.
    apply (wf_cset_set (map (subst_cb Z (cset_set x {}N)) F ++ E) (union (remove Z A) x)).
    intros a aIna.
    (* I am not entirely sure about how to procede here, if a `in` A, we can apply H
       but if a `in` x, I am not certain.
       
       If a `in` x, note that x is well formed in E*)
    inversion WP; subst...
    rewrite AtomSetFacts.union_iff in aIna; destruct aIna as [InRemove | InX]...
    + assert (a `in` A). AtomSetDecide.fsetdec.
      assert (a <> Z). AtomSetDecide.fsetdec.
      destruct (H a) as [[U BindsU] | [V BindsV]]...
      - analyze_binds BindsU...
        left; eexists.
        apply binds_app_2...
        eapply binds_map_2 with (f := subst_cb Z (cset_set x {}N)) in BindsTac...
      - analyze_binds BindsV...
        right; eexists.
        apply binds_app_2...
        eapply binds_map_2 with (f := subst_cb Z (cset_set x {}N)) in BindsTac...
    + destruct (H3 a) as [[U BindsU] | [V BindsV]]...
  *  apply (wf_cset_set (map (subst_cb Z P) F ++ E) A).
    intros a aInA.
    destruct (H a aInA)...
    ** left. destruct H0. apply binds_app_1 in H0. destruct H0.
       *** eexists.
           apply binds_app_2.
           eapply binds_map_2 with (f := subst_cb Z P) in H0...
       *** analyze_binds H0...
    ** right. destruct H0. apply binds_app_1 in H0. destruct H0.
      *** eexists.
          apply binds_app_2.
          eapply binds_map_2 with (f := subst_cb Z P) in H0...
      *** analyze_binds H0...
          rewrite <- AtomSetFacts.not_mem_iff in *.
          AtomSetDecide.fsetdec.
Qed.

(*
Lemma subst_cs_open_ss_rec : forall k U Z P T,
  open_ss_rec k (subst_cs Z P U) (subst_cs Z P T) = subst_cs Z P (open_ss_rec k U T)
with subst_ct_open_st_rec : forall k U Z P T,
  open_st_rec k (subst_cs Z P U) (subst_ct Z P T) = subst_ct Z P (open_st_rec k U T).
Proof with eauto.
-----
  clear subst_cs_open_ss_rec.
  intros *.
  induction T; simpl in *; f_equal...
  destruct (k == n)...
-----
  clear subst_ct_open_st_rec.
  intros *.
  induction T; simpl in *; f_equal...
Qed.

Lemma subst_ct_open_st_var : forall (X : atom) Z P T,
  open_st (subst_ct Z P T) X = subst_ct Z P (open_st T X).
Proof with eauto.
  intros. unfold open_st.
  assert (shp_fvar X = subst_cs Z P X) by eauto.
  rewrite H. eapply subst_ct_open_st_rec.
Qed.
 *)

Lemma wf_shp_subst_cbc : forall F Q E Z P T,
  wf_shp (F ++ Z ~ bind_sub_cap Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_shp (map (subst_cb Z P) F ++ E) (subst_cs Z P T)
with wf_typ_subst_cbc : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub_cap Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_typ (map (subst_cb Z P) F ++ E) (subst_ct Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ,
  shape_from_wf_shp.
-----
  clear wf_shp_subst_cbc.
  intros * WfShp WfCap Uniq.
  remember (F ++ Z ~ bind_sub_cap Q ++ E) as G.
  generalize dependent F.
  induction WfShp; intros F EQ Ok; subst...
  - analyze_binds H...
    + eapply wf_shp_fvar.
      eapply binds_map_2 with (f := subst_cb Z P) in BindsTac...
    + eapply wf_shp_fvar.
      eapply binds_app_3...
  - pick fresh X and apply wf_shp_arrow... fold subst_ct.
    replace (cset_fvar X) with (subst_cc Z P (cset_fvar X))...
    rewrite <- subst_ct_open_ct.
    rewrite_env ((map (subst_cb Z P) (X ~ bind_typ T1 ++ F)) ++ E).
    eapply wf_typ_subst_cbc...
    eapply capture_from_wf_cap...
    repeat (simpl; unfold subst_cc)...
    destruct (AtomSetImpl.mem Z (singleton X)) eqn:ZX...
    exfalso; rewrite <- AtomSetFacts.mem_iff in *. AtomSetDecide.fsetdec.
  - pick fresh X and apply wf_shp_sall...
    fold subst_cs subst_ct.
    rewrite_env ((map (subst_cb Z P) (X ~ bind_sub_shp S ++ F)) ++ E).
    rewrite <- subst_ct_open_st_var...
    rewrite <- map_one. rewrite <- app_assoc. rewrite <- map_app.
    eapply wf_typ_subst_cbc...
  - pick fresh X and apply wf_shp_call;
      fold subst_cs subst_ct...
    + inversion H; subst; repeat (simpl; unfold subst_cc)...

      destruct (AtomSetImpl.mem Z A) eqn:ZinA; subst...
      * inversion WfCap; subst; autorewrite with core...
        constructor; intros.
        rewrite <- AtomSetFacts.mem_iff in ZinA.
        rewrite AtomSetFacts.union_iff in H3; destruct H3...
          assert (a `in` A) by AtomSetDecide.fsetdec.
          destruct (H1 a)...
          destruct (H5) as [U Bindsa].
          analyze_binds Bindsa...
          eapply binds_map_2
            with (f := subst_cb Z (cset_set A0 {}N))
            in BindsTac.
          left; eexists; apply binds_app_2...
          exfalso; AtomSetDecide.fsetdec.
          destruct (H5) as [V Bindsa].
          analyze_binds Bindsa...
          eapply binds_map_2
            with (f := subst_cb Z (cset_set A0 {}N))
            in BindsTac.
          right; eexists; apply binds_app_2...
          destruct (H2 a)...
          destruct (H4) as [U BindsU]...
          destruct (H4) as [V BindsV]...
      * constructor; intros.
        rewrite <- AtomSetFacts.not_mem_iff in ZinA.
        destruct (H1 a)...
        destruct (H3) as [U Bindsa]...
        analyze_binds Bindsa...
        eapply binds_map_2
          with (f := subst_cb Z P)
          in BindsTac.
        left; eexists; apply binds_app_2...
        destruct (H3) as [V Bindsa]...
        analyze_binds Bindsa...
        eapply binds_map_2
          with (f := subst_cb Z P)
          in BindsTac.
        right; eexists...
    + rewrite subst_ct_open_ct_var...
      rewrite_env ((map (subst_cb Z P) ((X ~ bind_sub_cap C) ++ F)) ++ E).
      eapply wf_typ_subst_cbc...
      eapply capture_from_wf_cap... 
-----
  clear wf_typ_subst_cbc.
  intros * WfTyp WfCap Uniq.
  remember (F ++ Z ~ bind_sub_cap Q ++ E) as G.
  generalize dependent F.
  induction WfTyp; intros F EQ Ok; subst...
  simpl subst_ct... constructor...
  eapply wf_cap_subst_cbc...
Qed.


Lemma wf_shp_subst_cbt : forall F Q E Z P T,
  wf_shp (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_shp (map (subst_cb Z P) F ++ E) (subst_cs Z P T)
with wf_typ_subst_cbt : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_cap E P ->
  uniq (map (subst_cb Z P) F ++ E) ->
  wf_typ (map (subst_cb Z P) F ++ E) (subst_ct Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ,
  shape_from_wf_shp.
-----
  clear wf_shp_subst_cbt.
  intros * WfShp WfCap Uniq.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WfShp; intros F EQ Ok; subst...
  - analyze_binds H...
    + eapply wf_shp_fvar.
      eapply binds_map_2 with (f := subst_cb Z P) in BindsTac...
    + eapply wf_shp_fvar.
      eapply binds_app_3...
  - pick fresh X and apply wf_shp_arrow... fold subst_ct.
    replace (cset_fvar X) with (subst_cc Z P (cset_fvar X))...
    rewrite <- subst_ct_open_ct...
    rewrite_env ((map (subst_cb Z P) (X ~ bind_typ T1 ++ F)) ++ E).
    eapply wf_typ_subst_cbt...
    eapply capture_from_wf_cap...
    repeat (simpl; unfold subst_cc); destruct (AtomSetImpl.mem Z (singleton X)) eqn:ZinX...
    exfalso; rewrite <- AtomSetFacts.mem_iff in ZinX. AtomSetDecide.fsetdec.  
  - pick fresh X and apply wf_shp_sall...
    fold subst_cs subst_ct.
    rewrite_env ((map (subst_cb Z P) (X ~ bind_sub_shp S ++ F)) ++ E).
    rewrite <- subst_ct_open_st_var...
    rewrite <- map_one. rewrite <- app_assoc. rewrite <- map_app.
    eapply wf_typ_subst_cbt...
  - pick fresh X and apply wf_shp_call;
      fold subst_cs subst_ct...
    + inversion H; subst;  repeat (simpl; unfold subst_cc)...
      destruct (AtomSetImpl.mem Z A) eqn:ZinA; subst...
      * inversion WfCap; subst; autorewrite with core...
        constructor; intros.
        rewrite <- AtomSetFacts.mem_iff in ZinA.
        rewrite AtomSetFacts.union_iff in H3; destruct H3...
          assert (a `in` A) by AtomSetDecide.fsetdec.
          destruct (H1 a)...
          destruct (H5) as [U Bindsa].
          analyze_binds Bindsa...
          eapply binds_map_2
            with (f := subst_cb Z (cset_set A0 {}N))
            in BindsTac.
          left; eexists; apply binds_app_2...
          destruct (H5) as [V Bindsa].
          analyze_binds Bindsa...
          eapply binds_map_2
            with (f := subst_cb Z (cset_set A0 {}N))
            in BindsTac.
          right; eexists; apply binds_app_2...
          exfalso; AtomSetDecide.fsetdec.
          destruct (H2 a)...
          destruct (H4) as [U BindsU]...
          destruct (H4) as [V BindsV]...
      * constructor; intros.
        rewrite <- AtomSetFacts.not_mem_iff in ZinA.
        destruct (H1 a)...
        destruct (H3) as [U Bindsa]...
        analyze_binds Bindsa...
        eapply binds_map_2
          with (f := subst_cb Z P)
          in BindsTac.
        left; eexists; apply binds_app_2...
        destruct (H3) as [V Bindsa]...
        analyze_binds Bindsa...
        eapply binds_map_2
          with (f := subst_cb Z P)
          in BindsTac.
        right; eexists...
    + rewrite subst_ct_open_ct_var...
      rewrite_env ((map (subst_cb Z P) ((X ~ bind_sub_cap C) ++ F)) ++ E).
      eapply wf_typ_subst_cbt...
      eapply capture_from_wf_cap... 
-----
  clear wf_typ_subst_cbt.
  intros * WfTyp WfCap Uniq.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WfTyp; intros F EQ Ok; subst...
  simpl subst_ct... constructor...
  eapply wf_cap_subst_cbt...
Qed.

Lemma wf_shp_open : forall E U T1 T2,
  uniq E ->
  wf_shp E (shp_sall T1 T2) ->
  wf_shp E U ->
  wf_typ E (open_st T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_st_intro X)...
  rewrite_env (map (subst_sb X U) empty ++ E).
  eapply wf_typ_subst_sbs...
Qed.

Lemma wf_cap_open : forall E U T1 T2,
  uniq E ->
  wf_shp E (shp_call T1 T2) ->
  wf_cap E U ->
  wf_typ E (open_ct T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_ct_intro X)...
  rewrite_env (map (subst_cb X U) empty ++ E).
  eapply wf_typ_subst_cbc...
Qed.

Lemma wf_cap_open_expr : forall E U T1 T2,
  uniq E ->
  wf_shp E (shp_arrow T1 T2) ->
  wf_cap E U ->
  wf_typ E (open_ct T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_ct_intro X)...
  rewrite_env (map (subst_cb X U) empty ++ E).
  eapply wf_typ_subst_cbt with (Q := T1)...
Qed.



(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the MetatheoryEnv library use [uniq], whereas here we naturally
    have (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

#[export] Hint Resolve uniq_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_shp_from_binds_shp : forall x U E,
  wf_env E ->
  binds x (bind_sub_shp U) E ->
  wf_shp E U.
Proof with auto using wf_shp_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_cap_from_binds_cap : forall x U E,
  wf_env E ->
  binds x (bind_sub_cap U) E ->
  wf_cap E U.
Proof with auto using wf_cap_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_cap_from_binds_typ : forall x Sh U E,
  wf_env E ->
  binds x (bind_typ (pair Sh U)) E ->
  wf_cap E U.
Proof with auto using wf_cap_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
  inversion H0...
Qed.


Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_shp_from_wf_env_sub_shp : forall x T E,
  wf_env (x ~ bind_sub_shp T ++ E) ->
  wf_shp E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_cap_from_wf_env_sub_cap : forall x T E,
  wf_env (x ~ bind_sub_cap T ++ E) ->
  wf_cap E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing_cap : forall V E F U X,
  wf_env (F ++ X ~ bind_sub_cap V ++ E) ->
  wf_cap E U ->
  wf_env (F ++ X ~ bind_sub_cap U ++ E).
Proof with eauto using wf_cap_narrowing_cap.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
    * apply (wf_env_sub_shp (F ++ X ~ bind_sub_cap U ++ E) X0 Sh)... 
      apply (wf_shp_narrowing_cap V _ _ _ _ _).
      apply H2.
    * apply wf_env_typ...
      apply (wf_typ_narrowing_cap V _ _ _ _ _).
      apply H2.
Qed.

Lemma wf_env_narrowing_shp : forall V E F U X,
  wf_env (F ++ X ~ bind_sub_shp V ++ E) ->
  wf_shp E U ->
  wf_env (F ++ X ~ bind_sub_shp U ++ E).
Proof with eauto using wf_cap_narrowing_cap.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
    * apply (wf_env_sub_shp (F ++ X ~ bind_sub_shp U ++ E) X0 Sh)... 
      apply (wf_shp_narrowing_shp V _ _ _ _ _).
      apply H2.
    * apply wf_env_sub_cap...
      apply (wf_cap_narrowing_shp V _ _ _ _ _).
      apply H2.
    * apply wf_env_typ...
      apply (wf_typ_narrowing_shp V _ _ _ _ _).
      apply H2.
Qed.

Lemma wf_env_narrowing_typ : forall V E F U X,
  wf_env (F ++ X ~ bind_typ V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_typ U ++ E).
Proof with eauto using wf_cap_narrowing_cap.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
    * apply (wf_env_sub_shp (F ++ X ~ bind_typ U ++ E) X0 Sh)...
      apply (wf_shp_narrowing_typ V)...
    * apply (wf_env_sub_cap (F ++ X ~ bind_typ U ++ E) X0 C)...
      apply (wf_cap_narrowing_typ V)...
    * apply (wf_env_typ (F ++ X ~ bind_typ U ++ E) x T)...
      apply (wf_typ_narrowing_typ V)...
Qed.

Lemma wf_env_subst_sbs : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub_shp Q ++ E) ->
  wf_shp E P ->
  wf_env (map (subst_sb Z P) F ++ E).
Proof with eauto 6 using wf_shp_subst_sbs.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_sb...
    * apply wf_env_sub_cap...
      apply (wf_cap_subst_sbs _ Q _ _ _ _)...
    * apply wf_env_typ...
      apply (wf_typ_subst_sbs _ Q _ _ _)...
Qed.

Lemma wf_env_subst_cbc : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub_cap Q ++ E) ->
  wf_cap E P ->
  wf_env (map (subst_cb Z P) F ++ E).
Proof with eauto 6 using wf_cap_subst_cbc.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_cb...
    * apply wf_env_sub_shp...
      apply (wf_shp_subst_cbc _ Q _ _ _ _)...
    * apply wf_env_typ...
      apply (wf_typ_subst_cbc _ Q _ _ _)...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_typ Q ++ E) ->
  wf_cap E P ->
  wf_env (map (subst_cb Z P) F ++ E).
Proof with eauto 6 using wf_shp_subst_cbt, wf_cap_subst_cbt, wf_typ_subst_cbt.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_cb...
Qed.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(*** TODO: generalize for all k in opening, and then prove *)
Lemma notin_fv_ss_open_cs_rec : forall (Y X : atom) k T,
  X `notin` fv_ss (open_cs_rec k (cset_fvar Y) T) ->
  X `notin` fv_ss T
with notin_fv_st_open_ct_rec : forall (Y X : atom) k T,
  X `notin` fv_st (open_ct_rec k (cset_fvar Y) T) ->
  X `notin` fv_st T.
Proof.
-----   
  clear notin_fv_ss_open_cs_rec.
  intros Y X k T. unfold open_cs, open_ct in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
-----
  clear notin_fv_st_open_ct_rec.
  intros Y X k T. unfold open_cs, open_ct in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto. 
Qed.

Lemma notin_fv_st_open_ct : forall (Y X : atom) T,
  X `notin` fv_st (open_ct T (cset_fvar Y)) ->
  X `notin` fv_st T.
Proof with eauto.
  intros; unfold open_ct.
  eapply notin_fv_st_open_ct_rec...
Qed.

Lemma notin_fv_ss_open_ss_rec : forall (Y X : atom) k T,
  X `notin` fv_ss (open_ss_rec k Y T) ->
  X `notin` fv_ss T
with notin_fv_st_open_st_rec : forall (Y X : atom) k T,
  X `notin` fv_st (open_st_rec k Y T) ->
  X `notin` fv_st T.
Proof.
-----   
  clear notin_fv_ss_open_ss_rec.
  intros Y X k T. unfold open_ss, open_st in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
-----
  clear notin_fv_st_open_st_rec.
  intros Y X k T. unfold open_cs, open_ct in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_st_open_st : forall (Y X : atom) T,
  X `notin` fv_st (open_st T Y) ->
  X `notin` fv_st T.
Proof with eauto.
  intros; unfold open_st.
  eapply notin_fv_st_open_st_rec...
Qed.


Lemma notin_fv_cs_open_ss_rec : forall (Y X : atom) k T,
  X `notin` fv_cs (open_ss_rec k Y T) ->
  X `notin` fv_cs T
with notin_fv_ct_open_st_rec : forall (Y X : atom) k T,
  X `notin` fv_ct (open_st_rec k Y T) ->
  X `notin` fv_ct T.
Proof.
-----   
  clear notin_fv_cs_open_ss_rec.
  intros Y X k T. unfold open_ss, open_st in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
-----
  clear notin_fv_ct_open_st_rec.
  intros Y X k T. unfold open_cs, open_ct in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_ct_open_st : forall (Y X : atom) T,
  X `notin` fv_ct (open_st T Y) ->
  X `notin` fv_ct T.
Proof with eauto.
  intros; unfold open_st.
  eapply notin_fv_ct_open_st_rec...
Qed.


Lemma notin_fv_cs_open_cs_rec : forall (Y X : atom) k T,
  X `notin` fv_cs (open_cs_rec k (cset_fvar Y) T) ->
  X `notin` fv_cs T
with notin_fv_ct_open_ct_rec : forall (Y X : atom) k T,
  X `notin` fv_ct (open_ct_rec k (cset_fvar Y) T) ->
  X `notin` fv_ct T.
Proof with eauto; try solve csetdec.
-----   
  clear notin_fv_cs_open_cs_rec.
  intros Y X k T. unfold open_cs, open_st in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
  unshelve epose proof (notin_fv_ct_open_ct_rec Y X (S k) t _)...
  csetdec.
  unfold open_cc_rec in Fr; destruct c eqn:HC; subst; simpl fv_cc...
  csetdec.
  destruct (NatSetImpl.mem k t1); simpl in *...
-----
  clear notin_fv_ct_open_ct_rec.
  intros Y X k T. unfold open_cs, open_ct in *.
  generalize dependent k.
  induction T; simpl; intros k Fr; eauto.
  unshelve epose proof (notin_fv_cs_open_cs_rec Y X k s _)...
  unfold open_cc_rec in Fr; destruct c eqn:HC; subst; simpl fv_cc...
  csetdec.
  destruct (NatSetImpl.mem k t0); simpl in *...
Qed.

Lemma notin_fv_ct_open_ct : forall (Y X : atom) T,
  X `notin` fv_ct (open_ct T (cset_fvar Y)) ->
  X `notin` fv_ct T.
Proof with eauto; try solve csetdec.
  intros.
  eapply notin_fv_ct_open_ct_rec...
Qed.

(*
Lemma notin_fv_ss_open_sc : forall (Y X : atom) T,
  X `notin` fv_sc (open_cc T (cset_fvar Y)) ->
  X `notin` fv_sc T.
Proof.
 intros Y X T. unfold open_cc.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
 destruct (NatSetImpl.mem k t0)...
 * unfold fv_sc in Fr. auto.
 * auto.
Qed.
 *)

Lemma notin_fv_wf_cap : forall E (X : atom) T,
  wf_cap E T ->
  X `notin` dom E ->
   X `notin` fv_cc T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  intro xInA. destruct (H X xInA); destruct H0. 
    ** apply (binds_dom_contradiction _ X (bind_sub_cap x) E)...
    ** apply (binds_dom_contradiction _ X (bind_typ x) E)...
Qed.

Lemma notin_fv_wf_shp : forall E (X : atom) T,
  wf_shp E T ->
  X `notin` dom E ->
  X `notin` fv_ss T /\ X `notin` fv_cs T
with notin_fv_wf_typ : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_st T /\ X `notin` fv_ct T.
Proof with auto.
  ----- clear notin_fv_wf_shp.
        intros E X T Wf_typ.
        induction Wf_typ; intros Fr; simpl...
        * split; auto. destruct (X == x)...
          rewrite e in *.
          destruct (binds_dom_contradiction _ x (bind_sub_shp U) E)...
        * split; apply union_rewrite; split.
          ** apply (notin_fv_wf_typ E _ T1)...
          ** pick fresh y.
             eapply notin_fv_wf_typ with (X := X) in H0
              as [FrOpen FrCaptOpen]...
             eapply notin_fv_st_open_ct...
          ** apply (notin_fv_wf_typ E _ T1)...
          ** pick fresh y.
             eapply notin_fv_wf_typ with (X := X) in H0
              as [FrOpen FrCaptOpen]...
             eapply notin_fv_ct_open_ct...
        * split; apply union_rewrite; split.
          ** apply (IHWf_typ Fr)...
          ** pick fresh Y. 
             eapply notin_fv_wf_typ with (X := X) in H
              as [FrOpen FrCaptOpen]...
             eapply notin_fv_st_open_st... 
          ** apply (IHWf_typ Fr)...
          ** pick fresh Y. 
             eapply notin_fv_wf_typ with (X := X) in H
              as [FrOpen FrCaptOpen]...
             eapply notin_fv_ct_open_st...
        * split... 
          ** pick fresh Y.
             eapply notin_fv_wf_typ with (X := X) in H0
                as [FrOpen FrCaptOpen]...
             eapply notin_fv_st_open_ct...
          ** unshelve epose proof (notin_fv_wf_cap E X C _ _)...
             apply union_rewrite; split...
             pick fresh Y.
             eapply notin_fv_wf_typ with (X := X) in H0
              as [FrOpen FrCaptOpen]...
             eapply notin_fv_ct_open_ct...          
-----
  clear notin_fv_wf_typ.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  split...
  unshelve epose proof (notin_fv_wf_shp E X S)...
  apply union_rewrite; split...
  unshelve epose proof (notin_fv_wf_shp E X S)...
  unshelve epose proof (notin_fv_wf_cap E X C)...
Qed.

Lemma map_subst_sb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_sb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_ss_fresh... eapply notin_fv_wf_shp; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_st_fresh... f_equal... destruct (notin_fv_wf_typ E Z T)...
Qed.


Lemma map_subst_cb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_cb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_cs_fresh... eapply notin_fv_wf_shp; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_cc_fresh... apply (notin_fv_wf_cap E Z C)...
  rewrite <- IHwf_env...
    rewrite <- subst_ct_fresh... destruct (notin_fv_wf_typ E Z T)... 
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma sub_cap_regular : forall E S T,
  sub_cap E S T ->
  wf_env E /\ wf_cap E S /\ wf_cap E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  * split... split...
    remember (cset_set ys {}N)...
    destruct H0 eqn:h0...
    ** discriminate Heqc.
    ** apply wf_cset_set...
       intros a aInx...
       inversion Heqc...
       replace a with x by AtomSetDecide.fsetdec.
       apply (o x)...
       rewrite H3...
  * split... split...
    inversion IHsub_cap. inversion H2.
    remember (cset_set ys {}N)...
    apply wf_cset_set...
    intros a aInx...
    left. eapply ex_intro...
    replace a with x by AtomSetDecide.fsetdec.
    apply H0...
  * split... split...
    ** apply wf_cset_set...
       intros a aInx.
       replace a with x by AtomSetDecide.fsetdec.
       right.
       eapply ex_intro.
       apply H0.
Qed.

Lemma sub_shp_regular : forall E S T,
  sub_shp E S T ->
  wf_env E /\ wf_shp E S /\ wf_shp E T
with sub_typ_regular : forall E S T,
  sub_typ E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  ----- clear sub_shp_regular.
        intros E S T H.
        induction H...
        * inversion IHsub_shp. inversion H2. split; eauto.
        * split.
          ** destruct (sub_typ_regular E T1 S1)...
          ** split.
             *** eapply wf_shp_arrow. destruct (sub_typ_regular E T1 S1)...
                 intros X XnInL.
                 eapply sub_typ_regular in H0 as [WfEnv [WfTypL WfTypR]]...
                 rewrite_env (empty ++ X ~ bind_typ S1 ++ E).
                 eapply wf_typ_narrowing_typ with (V := T1)...
             *** eapply wf_shp_arrow with (L := L). destruct (sub_typ_regular E T1 S1)...
                 intros X XnInL.
                 unshelve epose proof (sub_typ_regular _ _ _ (H0 X XnInL))...
        * split.
          ** destruct IHsub_shp...
          ** split; apply (wf_shp_sall L _ _ _).
             *** destruct IHsub_shp. destruct H2. apply H3.
             *** intros X xnInL. destruct ((sub_typ_regular _ _ _) (H0 X xnInL))... 
                 destruct H2...
                 apply (wf_typ_narrowing_shp T1 S1 (open_st S2 X) E empty X)...
             *** destruct IHsub_shp. destruct H2. apply H2.
             *** intros X xnInL. destruct ((sub_typ_regular _ _ _) (H0 X xnInL))...
        * split.
          ** destruct (sub_cap_regular E T1 S1)...
          ** split; apply (wf_shp_call L _ _ _).
             *** destruct (sub_cap_regular E T1 S1)...
             *** intros X xnInL. destruct ((sub_typ_regular _ _ _) (H0 X xnInL))...
                 destruct H2...
                  apply (wf_typ_narrowing_cap T1 S1 (open_ct S2 (cset_fvar X)) E empty X)...
             *** destruct (sub_cap_regular E T1 S1)...
             *** intros X xnInL. destruct ((sub_typ_regular _ _ _) (H0 X xnInL))...
  ----- clear sub_typ_regular.
        intros E S T H.
        induction H...
        split; try split.
        * destruct (sub_shp_regular E Sh1 Sh2)...
        * apply wf_pair... destruct (sub_shp_regular E Sh1 Sh2)... destruct (sub_cap_regular E C1 C2)...
        * apply wf_pair... destruct (sub_shp_regular E Sh1 Sh2)... destruct (sub_cap_regular E C1 C2)...
Qed.

Lemma fv_exp_cap_open_ee : forall e (k: nat) (x : atom) (Y : atom),
  x `in` (fv_exp_for_cap e) ->
  x `in` (fv_exp_for_cap (open_ee_rec k Y (cset_fvar Y) e)).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k;simpl...
  * unfold fv_exp_for_cap in Hxine.
    AtomSetDecide.fsetdec.
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma fv_exp_cap_open_se : forall e (k : nat) (x : atom) (Y : atom),
  x `in` (fv_exp_for_cap e) ->
  x `in` (fv_exp_for_cap (open_se_rec k Y e)).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl...
  simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma fv_exp_cap_open_ce : forall e (k : nat) (x : atom) (Y : atom),
  x `in` (fv_exp_for_cap e) ->
  x `in` (fv_exp_for_cap (open_ce_rec k (cset_fvar Y) e)).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl...
  simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma fv_exp_cap_bound_typing : forall E e (x : atom) T,
  typing E e T ->
  x `in` (fv_exp_for_cap e) ->
  exists T, binds x (bind_typ T) E.
Proof with eauto.
  intros E e x T Ht xIn.
  induction Ht; simpl in *...
  * replace x with x0 by AtomSetDecide.fsetdec.
    eapply ex_intro.
    apply H0.
  * pick fresh Y for (union L {{ x }}).
    destruct (H0 Y)...
    apply fv_exp_cap_open_ee...
    eapply ex_intro...
    analyze_binds H1...
  * apply AtomSetImpl.union_1 in xIn.
    destruct xIn...
  * pick fresh Y for (union L {{ x }}).
    destruct (H0 Y)...
    apply fv_exp_cap_open_se...
    eapply ex_intro...
    analyze_binds H1...
  * pick fresh Y for (union L {{ x }}).
    destruct (H0 Y)...
    apply fv_exp_cap_open_ce...
    eapply ex_intro...
    analyze_binds H1...
Qed.

Lemma typing_cap : forall E e T,
  typing E e T ->
  wf_cap E (cset_set (fv_exp_for_cap e) {}N).
Proof with eauto using fv_exp_cap_bound_typing.
  intros E e T Htyp.
  induction Htyp...
  * apply wf_cset_set...
    intros a aInfv...
    right...
    pick fresh x for (union L {{ a }}).
    apply union_rewrite in Fr. inversion Fr.
    destruct (fv_exp_cap_bound_typing _ _ a _ (H x H1))...
    apply fv_exp_cap_open_ee...
    eapply ex_intro.
    analyze_binds H3...
  * apply wf_cset_set...
    intros a aInfv...
    right...
    pick fresh x for (union L {{ a }}).
    apply union_rewrite in Fr. inversion Fr.
    destruct (fv_exp_cap_bound_typing _ _ a _ (H x H1))...
    apply fv_exp_cap_open_se...
    eapply ex_intro.
    analyze_binds H3...
  * apply wf_cset_set...
    intros a aInfv...
    right...
    pick fresh x for (union L {{ a }}).
    apply union_rewrite in Fr. inversion Fr.
    destruct (fv_exp_cap_bound_typing _ _ a _ (H x H1))...
    apply fv_exp_cap_open_ce...
    eapply ex_intro.
    analyze_binds H3...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E e T H. assert (typing E e T) as Typing by assumption. induction H...
  * repeat split...
    eapply wf_typ_from_binds_typ in H0... inversion H0...
    eapply wf_cset_set; intros.
    replace a with x in * by AtomSetDecide.fsetdec; subst.
    right... eexists; eassumption.
  * pick fresh X. destruct (H0 X) as [Hok [J K]]...
    repeat split...
    - inversion Hok...
    - apply expr_abs with (L := L)...
      eapply type_from_wf_typ.
      eapply wf_typ_from_binds_typ with (x := X) (E := X ~ bind_typ V ++ E)...
      intros x Frx.
      destruct (H0 x)...
    - apply wf_shp_arrow with (L := L)...
      inversion Hok...
      intros X' FrX'...
      destruct (H0 X')...
    - unshelve epose proof (typing_cap _ _ _ Typing)...
  * destruct (IHtyping1) as [WfEnv [Expr1 WfTyp]]...
    destruct (IHtyping2) as [WfEnv2 [Expr2 WfTyp3]]...
    repeat split...
    + constructor...
      inversion WfTyp; subst...
      inversion WfTyp3; subst...
      eapply capture_from_wf_cap; eauto...
    + inversion WfTyp; subst...
      inversion H4; subst...
      eapply wf_cap_open_expr with (T1 := (pair T1 C))...
      inversion WfTyp3; subst...
  * pick fresh Y. destruct (H0 Y) as [WfEnv [Expr WfTyp]]...
    repeat split; eauto.
    - inversion WfEnv...
    - pick fresh Y' and apply expr_sabs...
      eapply shape_from_wf_shp...
      inversion WfEnv; subst; eauto...
      destruct (H0 Y')...
    - pick fresh Y' and apply wf_shp_sall.
      inversion WfEnv...
      destruct (H0 Y')...
    - unshelve epose proof (typing_cap _ _ _ Typing)...
  * destruct (IHtyping) as [WfEnv [Expr1 WfTyp1]]...
    repeat split...
    - constructor...
      destruct (sub_shp_regular _ _ _ H0) as [WfEnv1 [WfShp1 WfShp2]]...
      eapply shape_from_wf_shp; eauto...
    - inversion WfTyp1; inversion H4; subst...
      eapply wf_shp_open with (T1 := Sh1)...
      eapply sub_shp_regular with (S := Sh) (T := Sh1)...
  * pick fresh Y.
    destruct (H0 Y) as [WfEnv [Expr WfTyp]]...
    repeat split...
    - inversion WfEnv...
    - apply expr_cabs with (L := L)...
      + eapply capture_from_wf_cap.
        eapply wf_cap_from_wf_env_sub_cap; eassumption...
      + intros X Frx.
        destruct (H0 X)...
    - apply wf_shp_call with (L := L)...
      + eapply wf_cap_from_wf_env_sub_cap; eassumption...
      + intros X' FrX'...
        destruct (H0 X')... 
    - unshelve epose proof (typing_cap _ _ _ Typing)...
  * destruct IHtyping as [WfEnv [Expr WfTyp]]...
    repeat split...
    - constructor...
      eapply capture_from_wf_cap.
      eapply sub_cap_regular with (S := C) (T := C1); eassumption.
    - inversion WfTyp. eapply wf_cap_open with (T1 := C1)...
      eapply sub_cap_regular with (T := C1); eassumption.
  * destruct IHtyping as [WfEnv [Expr WfTyp]]...
    repeat split...
    eapply sub_typ_regular; eassumption...
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with try solve [auto | intuition auto].
  intros e e' H.
  induction H; assert(J := value_regular); split; try apply expr_app...
  * inversion H; subst.
    pick fresh y. erewrite (subst_ee_intro)...
  * inversion H; subst.
    pick fresh Y. erewrite (subst_se_intro)...
  * inversion H; subst.
    pick fresh Y. erewrite (subst_ce_intro)...
Qed.

Lemma wf_cap_from_wf_typ : forall E S C,
  wf_typ E (pair S C) ->
  wf_cap E C.
Proof with eauto.
  intros.
  inversion H...
Qed.

Lemma wf_shp_from_wf_typ : forall E S C,
  wf_typ E (pair S C) ->
  wf_shp E S.
Proof with eauto.
  intros.
  inversion H...
Qed.



(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint
    since it helps blur the distinction between [wf_env] and [uniq] in
    proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

#[export] Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub_typ _ _ _ |- _ => apply (proj1 (sub_typ_regular _ _ _ H))
  | H: sub_shp _ _ _ |- _ => apply (proj1 (sub_shp_regular _ _ _ H))
  | H: sub_cap _ _ _ |- _ => apply (proj1 (sub_cap_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

#[export] Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub_typ E T _ |- _ => apply (proj1 (proj2 (sub_typ_regular _ _ _ H)))
  | H: sub_typ E _ T |- _ => apply (proj2 (proj2 (sub_typ_regular _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (wf_cap ?E ?C) =>
  match goal with
  | H: typing E _ (pair _ C)   |- _ => apply (wf_cap_from_wf_typ _ _ _ (proj2 (proj2 (typing_regular _ _ _ H))))
  | H: sub_typ E (pair _ C) _  |- _ => apply (wf_cap_from_wf_typ _ _ _ (proj1 (proj2 (sub_typ_regular _ _ _ H))))
  | H: sub_typ E _ (pair _ C)  |- _ => apply (wf_cap_from_wf_typ _ _ _ (proj2 (proj2 (sub_typ_regular _ _ _ H))))
  end : core.

#[export] Hint Extern 1 (wf_shp ?E ?T) =>
  match goal with
  | H: sub_shp E T _ |- _ => apply (proj1 (proj2 (sub_shp_regular _ _ _ H)))
  | H: sub_shp E _ T |- _ => apply (proj2 (proj2 (sub_shp_regular _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (wf_shp ?E ?S) =>
  match goal with
  | H: typing E _ (pair S _)    |- _ => apply (wf_shp_from_wf_typ _ _ _ (proj2 (proj2 (typing_regular _ _ _ H))))
  | H: sub_typ E (pair S _) _   |- _ => apply (wf_shp_from_wf_typ _ _ _ (proj1 (proj2 (sub_typ_regular _ _ _ H))))
  | H: sub_typ E _ (pair S _ )  |- _ => apply (wf_shp_from_wf_typ _ _ _ (proj2 (proj2 (sub_typ_regular _ _ _ H))))
  end : core.

#[export] Hint Extern 1 (wf_cap ?E ?T) =>
  match goal with
  | H: sub_cap E T _ |- _ => apply (proj1 (proj2 (sub_cap_regular _ _ _ H)))
  | H: sub_cap E _ T |- _ => apply (proj2 (proj2 (sub_cap_regular _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub_typ ?E T _ |- _ => go E
  | H: sub_typ ?E _ T |- _ => go E
  end : core.

#[export] Hint Extern 1 (shape ?T) =>
  let go E := apply (shape_from_wf_shp E); auto in
  match goal with
  | H: typing ?E _ (pair T _) |- _ => go E
  | H: sub_shp ?E T _ |- _ => go E 
  | H: sub_shp ?E _ T |- _ => go E
  end : core.

#[export] Hint Extern 1 (capture ?T) =>
  let go E := apply (capture_from_wf_cap E); auto in
  match goal with
  | H: typing ?E _ (pair _ T) |- _ => go E
  | H: sub_cap ?E T _ |- _ => go E
  | H: sub_cap ?E _ T |- _ => go E
  end : core.

#[export] Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end : core.

#[export] Hint Resolve wf_shp_from_wf_typ wf_cap_from_wf_typ : core.
