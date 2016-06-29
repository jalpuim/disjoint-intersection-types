Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import MSetProperties.
Require Import Coq.Init.Specif.

Module TLC
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

Module EqFacts := BoolEqualityFacts(VarTyp).

Module M := MSetWeakList.Make(VarTyp).
Export M.
  
Module MSetProperties := WPropertiesOn(VarTyp)(M).

Inductive STyp :=
  | STUnitT : STyp
  | STInt : STyp
  | STFun : STyp -> STyp -> STyp
  | STTuple : STyp -> STyp -> STyp.

Inductive SExp (A : Type) :=
  | STFVar  : A -> SExp A
  | STBVar  : nat -> SExp A
  | STUnit  : SExp A
  | STLit   : nat -> SExp A
  | STLam   : STyp -> SExp A -> SExp A
  | STLam'  : SExp A -> SExp A
  | STApp   : SExp A -> SExp A -> SExp A
  | STPair  : SExp A -> SExp A -> SExp A
  | STProj1 : SExp A -> SExp A
  | STProj2 : SExp A -> SExp A.

Definition Exp := forall A, SExp A.

Definition var : Type := VarTyp.t.

Definition vars := M.t.

(** Definitions borrowed from STLC_Tutorial **)

(* Contexts *)
Definition context (A : Type) := list (var * A). 

Definition extend {A} (x : var) (a : A) (c : context A) : context A :=
  ((x,a) :: nil) ++ c.

Definition dom {A} (c : context A) : vars :=
  fold_right (fun el r => add (fst el) r) empty c.

(* Functions on contexts *)
Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
  map (fun p => (fst p, (f (snd p)))) c.

Lemma cons_to_push : forall {A} x v (E : context A),
  (x, v) :: E = extend x v E.
Proof. intros; unfold extend; simpl; reflexivity. Defined.

Lemma env_ind : forall {A} (P : context A -> Prop),
  (P nil) ->
  (forall E x v, P E -> P (extend x v E)) ->
  (forall E, P E).
Proof.
  unfold extend.
  induction E as [|(x,v)].
  assumption.
  pose (H0 _ x v IHE).
  now simpl in p.
Defined.

Lemma dom_map_id : forall (A B : Type) (E : context A) (f : A -> B),
  dom E = dom (mapctx f E).
Proof.
  unfold mapctx.
  intros.
  induction E.
  simpl; reflexivity.
  simpl in *.
  rewrite IHE.
  reflexivity.
Defined.

Lemma dom_union : forall (A : Type) (E G : context A) x,
  M.In x (dom (E ++ G)) <-> M.In x (M.union (dom E) (dom G)).
Proof.
  intros. generalize dependent G.
  induction E; intros.
  unfold dom at 2; simpl.
  unfold "<->".
  split; intros.
  apply MSetProperties.Dec.F.union_3.
  assumption.
  apply MSetProperties.Dec.F.union_1 in H.
  inversion H.
  inversion H0.
  assumption.
  simpl.
  destruct a.
  split; intros.
  simpl in *.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.union_2.
  apply MSetProperties.Dec.F.add_iff.
  auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  assert (Ha : M.Equal (M.union (M.add v (dom E)) (dom G)) (M.add v (M.union (dom E) (dom G)))) by apply MSetProperties.union_add.
  apply Ha.
  apply IHE in H.
  unfold not in n.
  apply MSetProperties.Dec.F.add_2.
  assumption.
  simpl in *.
  apply MSetProperties.Dec.F.union_1 in H.
  destruct H.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.add_iff; auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  apply MSetProperties.Dec.F.add_neq_iff; auto.
  apply IHE.
  apply MSetProperties.Dec.F.union_2; assumption.
  apply MSetProperties.Dec.F.add_iff.
  right.
  apply IHE.
  apply MSetProperties.Dec.F.union_3; assumption.
Defined.

Lemma list_impl_m : forall {A} Gamma x (v : A), List.In (x, v) Gamma -> M.In x (dom Gamma).
Proof.
  intros.
  induction Gamma.
  inversion H.
  simpl.
  destruct a.
  simpl in *.
  inversion H.
  apply MSetProperties.Dec.F.add_1.
  apply f_equal with (f := fst) in H0.
  simpl in H0.
  rewrite H0.
  reflexivity.
  apply MSetProperties.Dec.F.add_2.
  apply IHGamma; assumption.
Defined.

Ltac not_in_L x :=
  repeat rewrite dom_union; repeat rewrite M.union_spec;
  repeat match goal with
    | H: M.In x M.empty |- _ => inversion H
    | H:_ |- context [M.In x (dom nil)] => simpl
    | H:_ |- context [M.In x (dom ((?v, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H: _ |- context [M.In ?v (dom ((x, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H1: ~ ?l, H2: ?l |- _ => contradiction
    | H: ~ M.In ?y (M.singleton x) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; assumption 
    | H: ~ M.In x (M.singleton ?y) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; unfold not; intros; apply H; symmetry; assumption
    | H: ~ M.In x (M.add ?v M.empty) |- _ => rewrite <- MSetProperties.singleton_equal_add in H 
    | H: not (M.In x (dom ?l)) |- _ => rewrite dom_union in H; simpl in H
    | H: not (M.In x (M.union ?l1 ?l2)) |- _ =>
      rewrite M.union_spec in H
    | H: not (M.In x ?l3 \/ ?l) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (?l \/ M.In x ?l3) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (M.In x ?l1) |- not (M.In x ?l1) => assumption
    | H:_ |- ~ (x == ?v \/ M.In ?v ?l) => unfold not; intro HInv; inversion HInv as [HH | HH]
    | H:_ |- not (?A \/ ?B) => apply and_not_or; split
    | H1: ~ M.In x (M.singleton ?v), H2: ?v == x |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; assumption
    | H1: ~ M.In x (M.singleton ?v), H2: x == ?v |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; symmetry; assumption
    | H: not (M.In x ?l1) |- not (M.In x ?l2) =>
      unfold not; intros; apply H; repeat rewrite M.union_spec; auto 10 
  end.

(* Ok *)

Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (extend v ty E).        

Hint Constructors ok.

Lemma ok_app_l : forall {A} (E F : context A), ok (E ++ F) -> ok E.
Proof.
  intros A E; induction E; intros.
  apply Ok_nil.
  inversion H.
  subst.
  apply Ok_push.
  apply (IHE _ H2).
  not_in_L v.
Defined.  
  
Lemma ok_app_r : forall {A} (E F : context A), ok (E ++ F) -> ok F.
Proof.
  intros A E.
  induction E; intros.
  - rewrite app_nil_l in H.
    auto.
  - inversion H; subst.
    apply (IHE _ H2).
Defined.

Lemma ok_remove : forall {A} (E F G : context A), ok (E ++ G ++ F) -> ok (E ++ F).
Proof.
  intros.
  induction E using env_ind.
  rewrite app_nil_l in *.
  now apply ok_app_r in H.
  unfold extend; rewrite <- app_assoc.
  apply Ok_push.
  apply IHE.
  unfold extend in H; rewrite <- app_assoc in H.
  inversion H; subst.
  assumption.
  unfold extend in H.
  inversion H; subst.
  rewrite dom_union in *.
  rewrite union_spec in *.
  unfold not; intros.
  apply H4.
  inversion H0.
  auto.
  right.
  rewrite dom_union; rewrite union_spec.
  auto.
Defined.
  
Lemma ok_extend_comm : forall {A} (E F : context A) x v,
               ok (F ++ E ++ (x, v) :: nil) ->
               ok (F ++ (x, v) :: nil ++ E).
Proof.
  intros A E F x v HOk.  
  generalize dependent E.
  
  induction F using env_ind; intros.
  unfold extend; simpl.
  rewrite app_nil_l in HOk.
  apply Ok_push.
  now apply ok_app_l in HOk.
  induction E.
  unfold not; intros HInv; inversion HInv.
  simpl.
  rewrite <- app_comm_cons in HOk.
  inversion HOk; subst.
  apply IHE in H1.
  simpl in *.
  unfold not; intros H3; apply MSetProperties.Dec.F.add_iff in H3.
  inversion H3.
  rewrite H in H2.
  rewrite dom_union in H2.
  rewrite union_spec in H2.
  apply not_or_and in H2.
  inversion H2.
  simpl in H4.
  apply H4.
  apply MSetProperties.Dec.F.add_1.
  reflexivity.
  contradiction.
  unfold extend.
  rewrite <- app_assoc.
  apply Ok_push.
  apply IHF.
  inversion HOk.
  subst.
  assumption.
  rewrite dom_union.
  rewrite union_spec.
  unfold not; intros.
  inversion H.
  apply ok_app_l in HOk.
  inversion HOk.
  subst.
  contradiction.
  simpl in H0.
  apply MSetProperties.Dec.F.add_iff in H0.
  inversion H0.
  unfold extend in HOk.
  apply ok_remove in HOk.
  rewrite <- app_assoc in HOk.
  apply ok_remove in HOk.
  simpl in HOk.
  inversion HOk; subst.
  simpl in *.
  apply H6.
  apply MSetProperties.Dec.F.add_1.
  assumption.
  inversion HOk; subst.
  rewrite dom_union in H6; rewrite union_spec in H6.
  apply not_or_and in H6.
  inversion H6.
  rewrite dom_union in H3; rewrite union_spec in H3; apply not_or_and in H3.
  inversion H3.
  contradiction.
Defined.
  
Lemma ok_app_comm : forall {A} (E F : context A), ok (F ++ E) -> ok (E ++ F).
Proof.
  intros.
  generalize dependent H.
  generalize dependent F.
  dependent induction E using (@env_ind A).
  intros.
  rewrite app_nil_r in H.
  now simpl.
  intros.
  unfold extend in *.
  rewrite <- app_assoc.
  apply Ok_push.
  apply IHE.
  apply ok_remove in H.
  assumption.
  rewrite dom_union.
  rewrite union_spec.
  unfold not; intros.
  inversion H0.
  apply ok_app_r in H.
  inversion H; subst.
  contradiction.
  rewrite app_assoc in H.
  apply ok_app_l in H.
  rewrite <- app_nil_l in H.
  apply ok_extend_comm in H.
  rewrite app_nil_l in H.
  simpl in H.
  inversion H; subst.
  contradiction.
Defined.  
  
Definition ok_app_and {A} (E F : context A) (H : ok (E ++ F)) : ok E /\ ok F :=
  conj (ok_app_l _ _ H) (ok_app_r _ _ H).

Lemma ok_middle_comm :
  forall {A} (E : context A) F G H, ok (E ++ F ++ G ++ H) -> ok (E ++ G ++ F ++ H).
Proof.
  intros.
  induction E.
  generalize dependent F.
  induction H; intros.
  rewrite app_nil_l in *.
  rewrite app_nil_r in *.
  now apply ok_app_comm.
  rewrite app_nil_l.
  rewrite app_assoc.
  apply ok_app_comm.
  rewrite <- app_comm_cons.
  destruct a.
  apply Ok_push.
  apply ok_app_comm.
  rewrite <- app_assoc.
  rewrite app_nil_l in H0.
  rewrite app_assoc in H0.
  apply ok_app_comm in H0.
  rewrite <- app_comm_cons in H0.
  inversion H0; subst.
  apply IHlist.
  rewrite app_nil_l.
  apply ok_app_comm in H3.
  now rewrite <- app_assoc in H3.
  rewrite app_nil_l in H0.
  rewrite app_assoc in H0.
  apply ok_app_comm in H0.
  rewrite <- app_comm_cons in H0.
  inversion H0; subst.
  not_in_L v.
  rewrite dom_union in H2; rewrite union_spec in H2; inversion H2; contradiction.
  intros.
  rewrite <- app_comm_cons.
  destruct a.
  apply Ok_push.
  apply IHE.
  rewrite <- app_comm_cons in H0.
  inversion H0.
  assumption.
  rewrite <- app_comm_cons in H0.
  inversion H0.
  subst.
  not_in_L v.
  rewrite dom_union in H5; rewrite union_spec in H5; inversion H5.
  contradiction.
  rewrite dom_union in H7; rewrite union_spec in H7; inversion H7.
  contradiction.
  contradiction.
Defined.


(** Target language **)
Fixpoint fv (sExp : SExp var) : vars :=
  match sExp with
    | STFVar _ v => singleton v
    | STBVar _ _ => empty
    | STUnit _ => empty
    | STLit _ _ => empty
    | STLam _ _ t => fv t
    | STLam' _ t => fv t
    | STApp _ t1 t2 => union (fv t1) (fv t2)
    | STPair _ t1 t2 => union (fv t1) (fv t2)
    | STProj1 _ t => fv t
    | STProj2 _ t => fv t
  end.

Fixpoint open_rec (k : nat) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i => if Nat.eqb k i then u else (STBVar _ i)
  | STFVar _ x => STFVar _ x
  | STUnit _ => STUnit _
  | STLit _ x => STLit _ x
  | STLam _ ty t1 => STLam _ ty (open_rec (S k) u t1)
  | STLam' _ t1 => STLam' _ (open_rec (S k) u t1)    
  | STApp _ t1 t2 => STApp _ (open_rec k u t1) (open_rec k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec k u t1) (open_rec k u t2)
  | STProj1 _ t => STProj1 _ (open_rec k u t)
  | STProj2 _ t => STProj2 _ (open_rec k u t)
  end.

Definition open (t : SExp var) u := open_rec 0 u t.

(* Notation "[ z ~> u ] t" := (subst z u t) (at level 68). *)
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^ x" := (open t (STFVar var x)).
Notation "t ^^ u" := (open t u) (at level 67).

Lemma fv_distr :
  forall t1 t2 x n, In x (fv (open_rec n t2 t1)) ->
               In x (union (fv t1) (fv t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; rewrite union_spec in *; auto.
  - destruct (Nat.eqb n0 n); auto. 
  - rewrite <- union_spec.
    eapply IHt1.
    apply H.
  - apply IHt1 in H.
    now rewrite union_spec in H.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite <- union_spec.
    eapply IHt1; apply H.
  - rewrite <- union_spec.
    apply (IHt1 _ _ H).
Defined.


Inductive STTerm : SExp var -> Prop :=
  | STTerm_Var : forall x,
      STTerm (STFVar _ x)
  | STTerm_Unit : STTerm (STUnit _)
  | STTerm_Lit : forall n,
      STTerm (STLit _ n)
  | STTerm_Lam : forall L t1 ty,
      (forall x, not (In x L) -> STTerm (open t1 (STFVar _ x))) ->
      STTerm (STLam _ ty t1)
  | STTerm_Lam' : forall L t1,
      (forall x, not (In x L) -> STTerm (open t1 (STFVar _ x))) ->
      STTerm (STLam' _ t1)
  | STTerm_App : forall t1 t2,
      STTerm t1 -> 
      STTerm t2 -> 
      STTerm (STApp _ t1 t2)
  | STTerm_Pair : forall t1 t2,
      STTerm t1 ->
      STTerm t2 ->
      STTerm (STPair _ t1 t2)
  | STTerm_Proj1 : forall t,
      STTerm t ->
      STTerm (STProj1 _ t)
  | STTerm_Proj2 : forall t,
      STTerm t ->
      STTerm (STProj2 _ t).

Hint Constructors STTerm.

(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars_with F :=
  let rec gather V :=
   (match goal with
    | H:?S
      |- _ =>
          let FH := constr:(F H) in
          match V with
          | empty => gather FH
          | context [FH] => fail 1
          | _ => gather (union FH V)
          end
    | _ => V
    end)
  in
  let L := gather (empty : vars) in
  eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  (*let C := gather_vars_with (fun (x : context PTyp) => dom x) in *)
  let D := gather_vars_with (fun (x : context STyp) => dom x) in
  (*let E := gather_vars_with (fun x : PExp => fv_source x) in *)
  let F := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union D F))).

Ltac beautify_fset V :=
  let rec go Acc E :=
   (match E with
    | union ?E1 ?E2 => let Acc1 := go Acc E1 in
                    go Acc1 E2
    | empty => Acc
    | ?E1 => match Acc with
             | empty => E1
             | _ => constr:(union Acc E1)
             end
    end)
  in
  go (empty : vars) V.

Parameter var_fresh : forall L : vars, (sig (A := var) (fun x => not (In x L))).
  
Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  destruct (var_fresh L) as (Y, Fr).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac apply_fresh_base_simple lemma gather :=
  let L0 := gather in
  let L := beautify_fset L0 in
  first
  [ apply (lemma L) | eapply (lemma L) ].

Ltac intros_fresh x :=
  first
  [ let Fr := fresh "Fr" x in
    intros x Fr
  | let x2 :=
     (match goal with
      | |- ?T -> _ =>
            match T with
            | var => fresh "y"
            | vars => fresh "ys"
            | list var => fresh "ys"
            | _ => fresh "y"
            end
      end)
    in
    let Fr := fresh "Fr" x2 in
    intros x2 Fr ]. 

Fixpoint fresh (L : vars) (n : nat) (xs : list var) : Prop :=
  match xs with
  | nil => match n with
           | 0 => True
           | S _ => False
           end
  | (x :: xs')%list =>
      match n with
      | 0 => False
      | S n' => (not (In x L)) /\ fresh (union L (singleton x)) n' xs'
      end
  end.

Ltac apply_fresh_base lemma gather var_name :=
  apply_fresh_base_simple lemma gather;
   try
    match goal with
    | |- _ -> not (In _ _) -> _ => intros_fresh var_name
    | |- _ -> fresh _ _ _ -> _ => intros_fresh var_name
    end.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  { j ~> v }t = { i ~> u }({ j ~> v }t) -> t = { i ~> u }t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in *.
    case_eq (Nat.eqb i n); intros.
    case_eq (Nat.eqb j n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    rewrite H2 in H0.
    unfold open_rec in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H. 
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2.  
Defined.

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term : forall t u,
  STTerm  t -> forall k, t =  { k ~> u }t.
Proof.
  induction 1; intros; simpl; auto.
  pick_fresh x.
  rewrite <- open_rec_term_core with (j := 0) (v := STFVar _ x).
  reflexivity.
  auto.
  simpl.
  unfold open in *.
  rewrite <- H0.
  reflexivity.
  unfold not; intros; apply Fr; rewrite union_spec; rewrite union_spec; left; left.
  assumption.
  pick_fresh x.
  rewrite <- open_rec_term_core with (j := 0) (v := STFVar _ x).
  reflexivity.
  auto.
  simpl.
  unfold open in *.
  rewrite <- H0.
  reflexivity.
  unfold not; intros; apply Fr; rewrite union_spec; rewrite union_spec; left; left.
  assumption.
  rewrite <- IHSTTerm1.
  rewrite <- IHSTTerm2.
  reflexivity.
  rewrite <- IHSTTerm1.
  rewrite <- IHSTTerm2.
  reflexivity.
  rewrite <- IHSTTerm.
  reflexivity.
  rewrite <- IHSTTerm.
  reflexivity.
Defined.

Hint Resolve open_rec_term.

Lemma open_app_eq : forall x E n F,
  not (In x (fv E)) ->
  not (In x (fv F)) ->
  (open_rec n (STFVar var x) E) = (open_rec n (STFVar var x) F) ->
  E = F.
Proof.
  intros x E.
  induction E; intros n' F HNotE HNotF HEqOpen.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    destruct (Nat.eqb n' n); auto.
    exfalso; apply HNotE.
    apply MSetProperties.Dec.F.singleton_2; inversion H0; reflexivity.
  - induction F; simpl in *; try (now (destruct (Nat.eqb n' n); inversion HEqOpen)).
    destruct (Nat.eqb n' n).
    exfalso; apply HNotF.
    apply MSetProperties.Dec.F.singleton_2; inversion HEqOpen; reflexivity. 
    inversion HEqOpen.
    case_eq (Nat.eqb n' n); intros.
    case_eq (Nat.eqb n' n0); intros.
    apply f_equal.
    apply beq_nat_true in H.
    apply beq_nat_true in H0.
    now subst.
    rewrite H in HEqOpen.
    rewrite H0 in HEqOpen.
    inversion HEqOpen.
    rewrite H in HEqOpen.
    case_eq (Nat.eqb n' n0); intros;
    rewrite H0 in HEqOpen; inversion HEqOpen.
    reflexivity.
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n); [ inversion HEqOpen | auto ].
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n0); [ inversion HEqOpen | auto ].
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n); inversion HEqOpen.
    inversion HEqOpen.
    apply f_equal.
    now apply (IHE (S n')).
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n); inversion HEqOpen.
    inversion HEqOpen.
    apply f_equal.
    now apply (IHE (S n')).
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    apply f_equal.
    apply IHE with (n := n'); try not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    apply f_equal.
    apply IHE with (n := n'); try not_in_L x.
    now inversion HEqOpen. 
Defined.

(* Typing rules *)

(* Typing rules of STLC, inspired by STLC_Tutorial *)
Inductive has_type_st : (context STyp) -> (SExp var) -> STyp -> Prop :=
  | STTyVar : forall (Gamma : context STyp) x ty,
                ok Gamma -> List.In (x,ty) Gamma -> has_type_st Gamma (STFVar _ x) ty
  | STTyUnit : forall Gamma, ok Gamma -> has_type_st Gamma (STUnit _) STUnitT
  | STTyLit : forall Gamma x, ok Gamma -> has_type_st Gamma (STLit _ x) STInt       
  | STTyLam : forall L Gamma t A B,
                (forall x, not (In x L) -> 
                      has_type_st (extend x A Gamma) (open t (STFVar _ x)) B) ->
                has_type_st Gamma (STLam _ A t) (STFun A B)
  | STTyLam' : forall L Gamma t A B,
                 (forall x, not (In x L) -> 
                       has_type_st (extend x A Gamma) (open t (STFVar _ x)) B) ->
                 has_type_st Gamma (STLam' _ t) (STFun A B)
  | STTyApp : forall Gamma A B t1 t2, has_type_st Gamma t1 (STFun A B) ->
                             has_type_st Gamma t2 A -> has_type_st Gamma (STApp _ t1 t2) B
  | STTyPair : forall Gamma A B t1 t2, has_type_st Gamma t1 A ->
                              has_type_st Gamma t2 B ->
                              has_type_st Gamma (STPair _ t1 t2) (STTuple A B)
  | STTyProj1 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj1 _ t) A
  | STTyProj2 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj2 _ t) B.

Hint Constructors has_type_st.

(* Typing lemmas *)

Lemma typing_weaken : forall G E F t T,
   has_type_st (E ++ G) t T -> 
   ok (E ++ F ++ G) ->
   has_type_st (E ++ F ++ G) t T.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply STTyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
  (* STTyLam *)
  - apply_fresh STTyLam as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H6.
    rewrite union_spec in H6.
    inversion H6; exfalso; [apply H8 | apply H9]; auto.
  - apply_fresh STTyLam' as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H6.
    rewrite union_spec in H6.
    inversion H6; exfalso; [apply H8 | apply H9]; auto.
Defined.

Lemma typing_strengthen : forall z U E F t T,
  not (In z (fv t)) ->
  has_type_st (E ++ ((z,U) :: nil) ++ F) t T ->
  has_type_st (E ++ F) t T.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - subst; apply STTyVar.
    now apply ok_remove in H0.
    apply in_or_app.
    repeat apply in_app_or in H1.
    inversion H1.
    auto.
    apply in_app_or in H2.
    inversion H2.
    inversion H3.
    inversion H4.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H4.
    auto.
  - apply STTyUnit.
    subst.
    now apply ok_remove in H0.
  - apply STTyLit.
    subst.
    now apply ok_remove in H0.
  - subst.
    apply_fresh STTyLam as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_distr in H2.
    rewrite union_spec in H2.
    inversion H2.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H3.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H3.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
  - subst.
    apply_fresh STTyLam' as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_distr in H2.
    rewrite union_spec in H2.
    inversion H2.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H3.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H3.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
  - eapply STTyApp.
    subst.
    apply IHhas_type_st1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHhas_type_st2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply STTyPair.
    apply IHhas_type_st1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_st2; simpl in *; not_in_L z; reflexivity.
  - subst.
    eapply STTyProj1.
    apply IHhas_type_st.
    not_in_L z.
    reflexivity.
  - subst.
    eapply STTyProj2.
    apply IHhas_type_st.
    not_in_L z.
    reflexivity.
Defined. 

Lemma has_type_env_comm : forall E F G H T t,
              has_type_st (E ++ F ++ G ++ H) t T ->
              has_type_st (E ++ G ++ F ++ H) t T.
Proof.
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply STTyVar.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    now apply ok_middle_comm.
    apply in_app_or in H1.
    inversion H1.
    apply in_or_app; auto.
    apply in_or_app; right.
    apply in_app_or in H2.
    inversion H2.
    apply in_or_app.
    right; apply in_or_app; left.
    assumption.
    apply in_app_or in H3.
    inversion H3.
    apply in_or_app; auto.
    apply in_or_app; right; apply in_or_app; auto.
  - apply STTyUnit.
    now apply ok_middle_comm.
  - apply STTyLit.
    now apply ok_middle_comm.
  - apply_fresh STTyLam as x.
    unfold extend.
    rewrite app_assoc.
    apply H1.
    not_in_L x.
    unfold extend.
    rewrite <- app_assoc.
    reflexivity.
  - apply_fresh STTyLam' as x.
    unfold extend.
    rewrite app_assoc.
    apply H1.
    not_in_L x.
    unfold extend.
    rewrite <- app_assoc.
    reflexivity.
  - eapply STTyApp.
    apply IHhas_type_st1; reflexivity.
    apply IHhas_type_st2; reflexivity.
  - eapply STTyProj1; apply IHhas_type_st; reflexivity.
  - eapply STTyProj2; apply IHhas_type_st; reflexivity.
Defined.
    
Lemma has_type_env_comm_extend : forall Gamma x y v1 v2 E t,
              has_type_st (extend x v1 (extend y v2 Gamma)) t E ->
              has_type_st (extend y v2 (extend x v1 Gamma)) t E.
Proof.
  unfold extend.
  intros.
  rewrite <- app_nil_l with (l := ((x, v1) :: nil) ++ ((y, v2) :: nil) ++ Gamma) in H.
  apply has_type_env_comm in H.
  now rewrite app_nil_l in H.
Defined.  

Lemma typing_weaken_extend : forall t T x v Gamma,
   has_type_st Gamma t T ->
   not (M.In x (dom Gamma)) ->                            
   has_type_st ((x,v) :: Gamma) t T.
Proof.
  intros.
  induction H; eauto.
  apply STTyVar.
  apply Ok_push; assumption.
  apply in_cons; assumption.
  apply STTyUnit.
  apply Ok_push; assumption.
  apply STTyLit.
  apply Ok_push; assumption.
  apply_fresh STTyLam as x; cbn.
  unfold extend in H1.
  apply has_type_env_comm_extend.
  apply H1.
  not_in_L y.
  not_in_L x.
  not_in_L y.
  apply_fresh STTyLam' as x; cbn.
  unfold extend in H1.
  apply has_type_env_comm_extend.
  apply H1.
  not_in_L y.
  not_in_L x.
  not_in_L y.
Defined.

Lemma typing_ok_env : forall Gamma E ty, has_type_st Gamma E ty -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Defined.
  
Lemma typing_gives_terms : forall Gamma E ty, has_type_st Gamma E ty -> STTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh STTerm_Lam as x.
  apply H0.
  not_in_L x.
  apply_fresh STTerm_Lam' as x.
  apply H0.
  not_in_L x.
Defined.


End TLC.